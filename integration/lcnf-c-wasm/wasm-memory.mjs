function fail(message) {
  throw new Error(`Wasm memory inspection: ${message}`);
}

class Reader {
  constructor(bytes) {
    this.bytes = bytes;
    this.offset = 0;
  }

  byte() {
    if (this.offset >= this.bytes.length) {
      fail("unexpected end of module");
    }
    const value = this.bytes[this.offset];
    this.offset += 1;
    return value;
  }

  varuint() {
    let value = 0n;
    let shift = 0n;
    for (let index = 0; index < 10; index += 1) {
      const byte = this.byte();
      value |= BigInt(byte & 0x7f) << shift;
      if ((byte & 0x80) === 0) {
        return value;
      }
      shift += 7n;
    }
    fail("oversized unsigned LEB128 value");
  }

  safeVaruint(label) {
    const value = Number(this.varuint());
    if (!Number.isSafeInteger(value)) {
      fail(`${label} exceeds the JavaScript safe integer range`);
    }
    return value;
  }

  name() {
    const length = this.safeVaruint("name length");
    const end = this.offset + length;
    if (end > this.bytes.length) {
      fail("name extends past the end of the module");
    }
    const value = new TextDecoder().decode(this.bytes.subarray(this.offset, end));
    this.offset = end;
    return value;
  }

  skip(length) {
    const end = this.offset + length;
    if (end > this.bytes.length) {
      fail("section extends past the end of the module");
    }
    this.offset = end;
  }
}

function limits(reader) {
  const flags = reader.safeVaruint("memory flags");
  if ((flags & ~0x7) !== 0) {
    fail(`unsupported memory flags 0x${flags.toString(16)}`);
  }
  const memory64 = (flags & 0x4) !== 0;
  const initialPages = reader.varuint();
  const maximumPages = (flags & 0x1) !== 0 ? reader.varuint() : null;
  if ((flags & 0x2) !== 0 && maximumPages === null) {
    fail("shared memory has no declared maximum");
  }
  return {
    shared: (flags & 0x2) !== 0,
    memory64,
    initialPages,
    maximumPages,
  };
}

function inspectImportSection(reader, sectionEnd) {
  const count = reader.safeVaruint("import count");
  const memories = [];
  for (let index = 0; index < count; index += 1) {
    const module = reader.name();
    const name = reader.name();
    const kind = reader.byte();
    switch (kind) {
      case 0:
        reader.varuint();
        break;
      case 1:
        reader.byte();
        limits(reader);
        break;
      case 2:
        memories.push({ module, name, ...limits(reader) });
        break;
      case 3:
        reader.byte();
        reader.byte();
        break;
      case 4:
        reader.varuint();
        reader.varuint();
        break;
      default:
        fail(`unknown import kind ${kind}`);
    }
  }
  if (reader.offset !== sectionEnd) {
    fail("import section length does not match its contents");
  }
  return memories;
}

export function inspectImportedMemories(input) {
  const bytes = input instanceof Uint8Array ? input : new Uint8Array(input);
  const reader = new Reader(bytes);
  const expectedHeader = [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
  for (const expected of expectedHeader) {
    if (reader.byte() !== expected) {
      fail("invalid Wasm header");
    }
  }
  while (reader.offset < bytes.length) {
    const id = reader.byte();
    const size = reader.safeVaruint("section size");
    const end = reader.offset + size;
    if (end > bytes.length) {
      fail("section extends past the end of the module");
    }
    if (id === 2) {
      return inspectImportSection(reader, end);
    }
    reader.skip(size);
  }
  return [];
}

export function inspectSingleImportedMemory(input) {
  const memories = inspectImportedMemories(input);
  if (memories.length !== 1) {
    fail(`expected exactly one imported memory, found ${memories.length}`);
  }
  const memory = memories[0];
  const pageBytes = 65536n;
  const initialByteLength = memory.initialPages * pageBytes;
  const maximumByteLength =
    memory.maximumPages === null ? null : memory.maximumPages * pageBytes;
  for (const [label, byteLength] of [
    ["initial", initialByteLength],
    ["maximum", maximumByteLength],
  ]) {
    if (
      byteLength !== null &&
      byteLength > BigInt(Number.MAX_SAFE_INTEGER)
    ) {
      fail(`${label} memory byte length exceeds the safe integer range`);
    }
  }
  return {
    module: memory.module,
    name: memory.name,
    shared: memory.shared,
    memory64: memory.memory64,
    initialPages: memory.initialPages.toString(),
    maximumPages: memory.maximumPages?.toString() ?? null,
    initialByteLength: Number(initialByteLength),
    maximumByteLength:
      maximumByteLength === null ? null : Number(maximumByteLength),
  };
}
