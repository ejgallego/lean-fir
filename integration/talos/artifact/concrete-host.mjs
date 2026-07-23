import assert from "../../../scripts/wasm_assert.mjs";

const PAGE_BYTES = 65536;
const HEAP_BASE = 1024;
const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const MAX_IMMEDIATE_PAYLOAD = 0x7fffffffn;
const MAX_TAGGED_PAYLOAD = 0x7fffffffffffffffn;
const STRING_UTF8_MARKER = 1;
const INTEGER_SIGN_MAGNITUDE_MARKER = 1;

const OBJECT_KINDS = new Set(["object", "tagged", "tobject"]);
const SCALAR_KINDS = new Set(["uint8", "uint16", "uint32", "uint64"]);
const OBJECT_FIELD_KINDS = new Set(["object", "tagged", "tobject", "erased"]);

const KIND = Object.freeze({
  constructor: 1,
  closure: 2,
  boxed: 3,
  string: 4,
  natural: 5,
  integer: 6,
  byteArray: 7,
  opaque: 8,
  freed: 255,
});

function align8(bytes) {
  return Math.ceil(bytes / 8) * 8;
}

function unsigned32(value) {
  return Number(value) >>> 0;
}

function signed32(value) {
  return Number(BigInt.asIntN(32, BigInt(unsigned32(value))));
}

function uniquePush(values, value, equal = (left, right) => left === right) {
  if (!values.some((candidate) => equal(candidate, value))) {
    values.push(value);
  }
}

function sameKinds(left, right) {
  return left.length === right.length && left.every((kind, index) => kind === right[index]);
}

function scalarTypeRepr(kind) {
  const typeName = kind === "usize"
    ? "USize"
    : kind === "uint8"
      ? "UInt8"
      : kind === "uint16"
        ? "UInt16"
        : kind === "uint32"
          ? "UInt32"
          : kind === "uint64"
            ? "UInt64"
            : undefined;
  assert.ok(typeName, `unsupported boxed scalar kind: ${kind}`);
  return `Lean.Expr.const \`${typeName} []`;
}

export class ConcreteFault extends Error {
  constructor(fault) {
    super(`FIR concrete fault: ${fault.kind}`);
    this.fault = fault;
  }
}

export function concreteManifestValue(argument) {
  assert.ok(argument && typeof argument === "object", "manifest argument must be an object");
  switch (argument.kind) {
    case "tagged":
      return { kind: "tagged", payload: BigInt(argument.payload) };
    case "usize":
      return { kind: "usize", value: BigInt(argument.value) };
    case "scalar":
      assert.ok(SCALAR_KINDS.has(argument.scalarKind),
        `unsupported manifest scalar kind: ${argument.scalarKind}`);
      return {
        kind: "scalar",
        scalarKind: argument.scalarKind,
        value: BigInt(argument.value),
      };
    case "erased":
      return { kind: "erased" };
    case "reuseToken":
      assert.ok(argument.location === null ||
        (Number.isSafeInteger(argument.location) && argument.location >= 0),
      "reuse-token location must be null or a nonnegative safe integer");
      return { kind: "reuseToken", location: argument.location };
    case "heap":
      assert.ok(Number.isSafeInteger(argument.location) && argument.location >= 0,
        "heap argument location must be a nonnegative safe integer");
      return { kind: "heap", location: argument.location };
    default:
      throw new Error(`unsupported manifest argument kind: ${argument.kind}`);
  }
}

/**
 * Executable JavaScript counterpart of `Fir.Wasm.Concrete.MemoryState` for
 * standard WebAssembly engines. Runtime operations consume and return actual
 * wasm32 words; logical locations and allocation descriptors are retained only
 * to normalize final observations against the source oracle.
 */
export class ConcreteHost {
  constructor(manifestImports = [], initialRuntime = undefined,
    externalRegistry = undefined) {
    this.buffer = new ArrayBuffer(PAGE_BYTES);
    this.view = new DataView(this.buffer);
    this.heapCursor = HEAP_BASE;
    this.globals = new Map();
    this.world = 0;
    this.trace = [];
    this.externalRegistry = externalRegistry instanceof Map
      ? new Map(externalRegistry)
      : new Map(Object.entries(externalRegistry ?? {}));

    this.nextLocation = 0;
    this.addressLocations = new Map();
    this.locationAddresses = new Map();
    this.descriptors = new Map();
    this.allocations = [];

    const operations = manifestImports.map((descriptor) => descriptor.operation);
    this.closureDispatch = [];
    this.closureDescriptors = [];
    for (const operation of operations) {
      if (operation.kind === "partialApply" || operation.kind === "closureMatches" ||
          operation.kind === "closureProj") {
        uniquePush(this.closureDispatch, operation.function);
      }
      if (operation.kind === "partialApply") {
        uniquePush(this.closureDescriptors, [...operation.fields], sameKinds);
      }
    }
    if (initialRuntime !== undefined) {
      this.loadInitialRuntime(initialRuntime);
    }
  }

  initialNaturalLimbs(value) {
    const limbs = [];
    let remaining = BigInt(value);
    assert.ok(remaining >= 0n, "initial natural must be nonnegative");
    do {
      limbs.push(BigInt.asUintN(64, remaining));
      remaining >>= 64n;
    } while (remaining !== 0n);
    return limbs;
  }

  initialObjectFieldKind(value) {
    if (value.kind === "object") return "tobject";
    if (value.kind === "erased") return "erased";
    throw new Error(`unsupported concrete initial constructor field: ${value.kind}`);
  }

  initialCellLayout(cell) {
    const object = cell.object;
    assert.ok(object && typeof object === "object", "initial heap object must be an object");
    switch (object.kind) {
      case "ctor": {
        assert.ok(Array.isArray(object.objectFields),
          "initial constructor objectFields must be an array");
        assert.ok(Array.isArray(object.usizeFields),
          "initial constructor usizeFields must be an array");
        assert.ok(Array.isArray(object.scalarFields),
          "initial constructor scalarFields must be an array");
        assert.equal(object.scalarFields.length, 0,
          "packed initial constructors remain outside the concrete loader fragment");
        const tag = BigInt(object.tag);
        assert.ok(tag >= 0n && tag <= 0xffffffffn,
          "initial constructor tag must fit UInt32");
        const fieldKinds = object.objectFields.map((value) =>
          this.initialObjectFieldKind(value));
        return {
          kind: KIND.constructor,
          payloadBytes: SLOT_BYTES * (object.objectFields.length + object.usizeFields.length),
          auxiliaries: {
            aux0: Number(tag),
            aux1: object.objectFields.length,
            aux2: object.usizeFields.length,
            aux3: 0,
          },
          descriptor: { kind: "constructor", fieldKinds },
        };
      }
      case "natural": {
        const limbs = this.initialNaturalLimbs(object.value);
        return {
          kind: KIND.natural,
          payloadBytes: SLOT_BYTES * limbs.length,
          auxiliaries: { aux0: 2, aux1: limbs.length },
          descriptor: { kind: "natural" },
          limbs,
        };
      }
      case "integer": {
        const value = BigInt(object.value);
        const negative = value < 0n;
        const limbs = this.initialNaturalLimbs(negative ? -value : value);
        return {
          kind: KIND.integer,
          payloadBytes: SLOT_BYTES * limbs.length,
          auxiliaries: {
            aux0: INTEGER_SIGN_MAGNITUDE_MARKER,
            aux1: limbs.length,
            aux2: negative ? 1 : 0,
            aux3: 0,
          },
          descriptor: { kind: "integer" },
          limbs,
        };
      }
      case "string": {
        assert.equal(typeof object.value, "string", "initial string value must be text");
        const bytes = new TextEncoder().encode(object.value);
        assert.ok(bytes.length <= 0xffffffff,
          "initial string UTF-8 byte count must fit UInt32");
        return {
          kind: KIND.string,
          payloadBytes: bytes.length,
          auxiliaries: {
            aux0: STRING_UTF8_MARKER,
            aux1: bytes.length,
            aux2: 0,
            aux3: 0,
          },
          descriptor: { kind: "string" },
          bytes,
        };
      }
      default:
        throw new Error(`unsupported concrete initial-runtime heap object: ${object.kind}`);
    }
  }

  initialObjectWord(value) {
    if (value.kind === "erased") return 0;
    assert.equal(value.kind, "object", "initial constructor field must be object-like");
    assert.ok(value.reference && typeof value.reference === "object",
      "initial object reference must be an object");
    if (value.reference.kind === "tagged") {
      return this.encodeTagged(BigInt(value.reference.payload));
    }
    if (value.reference.kind === "heap") {
      const address = this.locationAddresses.get(value.reference.location);
      assert.notEqual(address, undefined,
        `initial object references unknown location ${value.reference.location}`);
      return address;
    }
    throw new Error(`unsupported initial object reference: ${value.reference.kind}`);
  }

  loadInitialRuntime(runtime) {
    assert.ok(runtime && typeof runtime === "object", "initialRuntime must be an object");
    assert.ok(Number.isSafeInteger(runtime.nextLocation) && runtime.nextLocation >= 0,
      "initialRuntime.nextLocation must be a nonnegative safe integer");
    assert.ok(Array.isArray(runtime.heap), "initialRuntime.heap must be an array");
    const layouts = new Map();
    const locations = new Set();

    for (const cell of [...runtime.heap].reverse()) {
      assert.ok(cell && typeof cell === "object", "initial heap cell must be an object");
      assert.ok(Number.isSafeInteger(cell.location) && cell.location >= 0 &&
        cell.location < runtime.nextLocation,
      "initial heap location must be below nextLocation");
      assert.ok(!locations.has(cell.location), `duplicate initial heap location ${cell.location}`);
      locations.add(cell.location);
      assert.ok(Number.isSafeInteger(cell.rc) && cell.rc >= 0 && cell.rc <= 0xffffffff,
        "initial reference count must fit UInt32");
      assert.equal(typeof cell.persistent, "boolean", "initial persistent flag must be boolean");
      assert.equal(typeof cell.live, "boolean", "initial live flag must be boolean");
      const layout = this.initialCellLayout(cell);
      const address = this.allocate(layout.kind, layout.payloadBytes, layout.auxiliaries,
        { logical: false });
      this.addressLocations.set(address, cell.location);
      this.locationAddresses.set(cell.location, address);
      this.allocations.unshift(address);
      this.descriptors.set(address, layout.descriptor);
      layouts.set(cell.location, layout);
    }

    this.nextLocation = runtime.nextLocation;
    for (const cell of runtime.heap) {
      const address = this.locationAddresses.get(cell.location);
      const layout = layouts.get(cell.location);
      assert.notEqual(address, undefined, `missing initial address for location ${cell.location}`);
      assert.ok(layout, `missing initial layout for location ${cell.location}`);
      if (cell.object.kind === "ctor") {
        cell.object.objectFields.forEach((value, index) =>
          this.writeWordSlot(address + HEADER_BYTES + SLOT_BYTES * index,
            this.initialObjectWord(value)));
        cell.object.usizeFields.forEach((value, index) =>
          this.writeU64(address + HEADER_BYTES +
            SLOT_BYTES * (cell.object.objectFields.length + index), BigInt(value)));
      } else if (cell.object.kind === "natural" || cell.object.kind === "integer") {
        layout.limbs.forEach((limb, index) =>
          this.writeU64(address + HEADER_BYTES + SLOT_BYTES * index, limb));
      } else if (cell.object.kind === "string") {
        new Uint8Array(this.buffer, address + HEADER_BYTES, layout.bytes.length)
          .set(layout.bytes);
      }
      const header = this.readHeader(address);
      this.writeHeader(address, {
        ...header,
        persistent: cell.persistent,
        live: cell.live,
        rc: cell.rc,
      });
    }
  }

  growToFit(requiredBytes) {
    if (requiredBytes <= this.buffer.byteLength) {
      return;
    }
    const pages = Math.ceil(requiredBytes / PAGE_BYTES);
    const next = new ArrayBuffer(pages * PAGE_BYTES);
    new Uint8Array(next).set(new Uint8Array(this.buffer));
    this.buffer = next;
    this.view = new DataView(this.buffer);
  }

  readU32(address) {
    assert.ok(address >= 0 && address + 4 <= this.buffer.byteLength,
      `concrete memory read is out of bounds at ${address}`);
    return this.view.getUint32(address, true);
  }

  writeU32(address, value) {
    assert.ok(address >= 0 && address + 4 <= this.buffer.byteLength,
      `concrete memory write is out of bounds at ${address}`);
    this.view.setUint32(address, unsigned32(value), true);
  }

  readU64(address) {
    assert.ok(address >= 0 && address + 8 <= this.buffer.byteLength,
      `concrete memory read is out of bounds at ${address}`);
    return this.view.getBigUint64(address, true);
  }

  writeU64(address, value) {
    assert.ok(address >= 0 && address + 8 <= this.buffer.byteLength,
      `concrete memory write is out of bounds at ${address}`);
    this.view.setBigUint64(address, BigInt.asUintN(64, BigInt(value)), true);
  }

  classify(word) {
    const value = unsigned32(word);
    if (value === 0) return "sentinel";
    if (value % 2 === 1) return "immediate";
    if (value % 8 === 0) return "heap";
    return "invalid";
  }

  encodeImmediate(payload) {
    const value = BigInt(payload);
    assert.ok(value >= 0n && value <= MAX_IMMEDIATE_PAYLOAD,
      `tagged payload does not fit wasm32: ${value}`);
    return unsigned32(value * 2n + 1n);
  }

  decodeImmediate(word) {
    const value = unsigned32(word);
    assert.equal(this.classify(value), "immediate", "expected an immediate concrete word");
    return BigInt(value >>> 1);
  }

  writeHeader(address, header) {
    const flags = (header.persistent ? 1 : 0) + (header.live ? 2 : 0);
    const words = [header.kind, flags, header.rc, header.bytes,
      header.aux0 ?? 0, header.aux1 ?? 0, header.aux2 ?? 0, header.aux3 ?? 0];
    words.forEach((word, index) => this.writeU32(address + 4 * index, word));
  }

  readHeader(address, requireLive = true) {
    const word = unsigned32(address);
    assert.equal(this.classify(word), "heap", `invalid concrete object address ${word}`);
    const flags = this.readU32(word + 4);
    const header = {
      kind: this.readU32(word),
      persistent: flags % 2 === 1,
      live: Math.floor(flags / 2) % 2 === 1,
      rc: this.readU32(word + 8),
      bytes: this.readU32(word + 12),
      aux0: this.readU32(word + 16),
      aux1: this.readU32(word + 20),
      aux2: this.readU32(word + 24),
      aux3: this.readU32(word + 28),
    };
    assert.ok(header.bytes >= HEADER_BYTES && header.bytes % 8 === 0 &&
      word + header.bytes <= this.buffer.byteLength,
    `malformed concrete header at ${word}`);
    if (requireLive && !header.live) {
      const location = this.addressLocations.get(word);
      throw new ConcreteFault({ kind: "deadObject", location });
    }
    return header;
  }

  allocate(kind, payloadBytes, auxiliaries = {}, options = {}) {
    const bytes = align8(HEADER_BYTES + payloadBytes);
    const address = align8(this.heapCursor);
    const end = address + bytes;
    assert.ok(end <= 0x100000000, "concrete wasm32 address space exhausted");
    this.growToFit(end);
    this.heapCursor = end;
    this.writeHeader(address, {
      kind,
      persistent: options.persistent ?? false,
      live: true,
      rc: options.persistent ? 0 : 1,
      bytes,
      ...auxiliaries,
    });
    if (options.logical !== false) {
      const location = this.nextLocation++;
      this.addressLocations.set(address, location);
      this.locationAddresses.set(location, address);
      this.allocations.unshift(address);
    }
    return address;
  }

  writeWordSlot(address, word) {
    this.writeU32(address, word);
    this.writeU32(address + 4, 0);
  }

  readWordSlot(address) {
    const word = this.readU32(address);
    assert.equal(this.readU32(address + 4), 0,
      `nonzero concrete word padding at ${address + 4}`);
    return word;
  }

  encodeTagged(payload) {
    const value = BigInt(payload);
    if (value <= MAX_IMMEDIATE_PAYLOAD) {
      return this.encodeImmediate(value);
    }
    const address = this.allocate(KIND.natural, 8, { aux0: 1, aux1: 1 },
      { persistent: true, logical: false });
    this.writeU64(address + HEADER_BYTES, value);
    return address;
  }

  taggedPayload(word) {
    const value = unsigned32(word);
    if (this.classify(value) === "immediate") {
      return this.decodeImmediate(value);
    }
    const header = this.readHeader(value);
    if (header.kind === KIND.natural && header.persistent && header.aux0 === 1) {
      return this.readU64(value + HEADER_BYTES);
    }
    throw new ConcreteFault({ kind: "expectedConstructor" });
  }

  allocateNatural(value) {
    const natural = BigInt(value);
    if (natural <= MAX_TAGGED_PAYLOAD) {
      return this.encodeTagged(natural);
    }
    const limbs = [];
    let remaining = natural;
    do {
      limbs.push(BigInt.asUintN(64, remaining));
      remaining >>= 64n;
    } while (remaining !== 0n);
    const address = this.allocate(KIND.natural, SLOT_BYTES * limbs.length,
      { aux0: 2, aux1: limbs.length });
    limbs.forEach((limb, index) => this.writeU64(address + HEADER_BYTES + SLOT_BYTES * index, limb));
    this.descriptors.set(address, { kind: "natural" });
    return address;
  }

  readNatural(address, header = this.readHeader(address)) {
    assert.equal(header.kind, KIND.natural, "expected a concrete natural object");
    if (header.persistent && header.aux0 === 1) {
      return this.readU64(address + HEADER_BYTES);
    }
    assert.equal(header.aux0, 2, "unknown concrete natural representation");
    let value = 0n;
    for (let index = header.aux1 - 1; index >= 0; --index) {
      value = (value << 64n) + this.readU64(address + HEADER_BYTES + SLOT_BYTES * index);
    }
    return value;
  }

  allocateInteger(value) {
    const integer = BigInt(value);
    if (integer >= -0x80000000n && integer <= 0x7fffffffn) {
      return this.encodeTagged(BigInt.asUintN(32, integer));
    }
    const negative = integer < 0n;
    const magnitude = negative ? -integer : integer;
    const limbs = this.initialNaturalLimbs(magnitude);
    const address = this.allocate(KIND.integer, SLOT_BYTES * limbs.length, {
      aux0: INTEGER_SIGN_MAGNITUDE_MARKER,
      aux1: limbs.length,
      aux2: negative ? 1 : 0,
      aux3: 0,
    });
    limbs.forEach((limb, index) =>
      this.writeU64(address + HEADER_BYTES + SLOT_BYTES * index, limb));
    this.descriptors.set(address, { kind: "integer" });
    return address;
  }

  readInteger(address, header = this.readHeader(address)) {
    assert.equal(header.kind, KIND.integer, "expected a concrete integer object");
    assert.equal(header.aux0, INTEGER_SIGN_MAGNITUDE_MARKER,
      "unknown concrete integer representation");
    assert.ok(header.aux2 === 0 || header.aux2 === 1,
      "concrete integer sign must be zero or one");
    assert.equal(header.aux3, 0, "concrete integer reserved header lane must be zero");
    assert.ok(header.aux1 > 0, "concrete integer must contain a magnitude limb");
    assert.equal(header.bytes, align8(HEADER_BYTES + SLOT_BYTES * header.aux1),
      "concrete integer allocation extent is noncanonical");
    let magnitude = 0n;
    for (let index = header.aux1 - 1; index >= 0; --index) {
      magnitude = (magnitude << 64n) +
        this.readU64(address + HEADER_BYTES + SLOT_BYTES * index);
    }
    assert.ok(header.aux2 === 0 || magnitude !== 0n,
      "concrete integer cannot encode negative zero");
    return header.aux2 === 1 ? -magnitude : magnitude;
  }

  allocateString(value) {
    assert.equal(typeof value, "string", "concrete string literal must be text");
    const bytes = new TextEncoder().encode(value);
    assert.ok(bytes.length <= 0xffffffff,
      "concrete string UTF-8 byte count must fit UInt32");
    const address = this.allocate(KIND.string, bytes.length, {
      aux0: STRING_UTF8_MARKER,
      aux1: bytes.length,
      aux2: 0,
      aux3: 0,
    });
    new Uint8Array(this.buffer, address + HEADER_BYTES, bytes.length).set(bytes);
    this.descriptors.set(address, { kind: "string" });
    return address;
  }

  readString(address, header = this.readHeader(address)) {
    assert.equal(header.kind, KIND.string, "expected a concrete string object");
    assert.equal(header.aux0, STRING_UTF8_MARKER, "unknown concrete string representation");
    assert.equal(header.aux2, 0, "nonzero concrete string reserved metadata");
    assert.equal(header.aux3, 0, "nonzero concrete string reserved metadata");
    assert.ok(HEADER_BYTES + header.aux1 <= header.bytes,
      "concrete string payload exceeds its allocation");
    const bytes = new Uint8Array(this.buffer, address + HEADER_BYTES, header.aux1);
    return new TextDecoder("utf-8", { fatal: true }).decode(bytes);
  }

  acceptsWord(kind, word) {
    const classification = this.classify(word);
    if (kind === "erased") return unsigned32(word) === 0;
    if (kind === "reuseToken") return unsigned32(word) === 0 || classification === "heap";
    if (kind === "tagged") {
      if (classification === "immediate") return true;
      if (classification !== "heap") return false;
      const header = this.readHeader(word);
      return header.kind === KIND.natural && header.persistent && header.aux0 === 1;
    }
    if (kind === "object") {
      if (classification !== "heap") return false;
      const header = this.readHeader(word);
      return !(header.kind === KIND.natural && header.persistent && header.aux0 === 1);
    }
    if (kind === "tobject") {
      return classification === "immediate" || classification === "heap";
    }
    return false;
  }

  checkedWord(kind, physical) {
    assert.ok(OBJECT_KINDS.has(kind) || kind === "erased" || kind === "reuseToken",
      `ABI kind ${kind} is not represented by a concrete word`);
    assert.equal(typeof physical, "number", `${kind} must use the WebAssembly i32 lane`);
    const word = unsigned32(physical);
    assert.ok(this.acceptsWord(kind, word), `concrete word ${word} does not refine ${kind}`);
    return word;
  }

  encode(kind, value) {
    switch (kind) {
      case "uint8":
      case "uint16":
      case "uint32": {
        assert.equal(value.kind, "scalar", `${kind} requires a scalar value`);
        assert.equal(value.scalarKind, kind, `${value.scalarKind} does not refine ${kind}`);
        const maximum = kind === "uint8" ? 0xffn : kind === "uint16" ? 0xffffn : 0xffffffffn;
        assert.ok(value.value >= 0n && value.value <= maximum,
          `${kind} argument is out of range: ${value.value}`);
        return signed32(value.value);
      }
      case "uint64":
        assert.equal(value.kind, "scalar", "uint64 requires a scalar value");
        assert.equal(value.scalarKind, "uint64", `${value.scalarKind} does not refine uint64`);
        return BigInt.asIntN(64, value.value);
      case "usize":
        assert.equal(value.kind, "usize", "usize requires a usize value");
        return BigInt.asIntN(64, value.value);
      case "erased":
        assert.equal(value.kind, "erased", "erased has the wrong semantic kind");
        return 0;
      case "reuseToken":
        assert.equal(value.kind, "reuseToken", "reuseToken has the wrong semantic kind");
        if (value.location === null) return 0;
        assert.ok(Number.isSafeInteger(value.location) && value.location >= 0,
          "reuse-token location must be a nonnegative safe integer");
        const address = this.addressOf(value.location);
        return signed32(this.checkedWord("reuseToken", address));
      case "object":
      case "tagged":
      case "tobject": {
        if (value.kind === "tagged") return signed32(this.encodeTagged(value.payload));
        assert.equal(value.kind, "heap", `${kind} requires an object-like value`);
        const address = this.addressOf(value.location);
        return signed32(this.checkedWord(kind, address));
      }
      default:
        throw new Error(`unsupported concrete argument ABI kind: ${kind}`);
    }
  }

  decode(kind, physical) {
    switch (kind) {
      case "uint8":
      case "uint16":
      case "uint32": {
        assert.equal(typeof physical, "number", `${kind} must use the WebAssembly i32 lane`);
        const value = unsigned32(physical);
        if (kind === "uint8") assert.ok(value <= 0xff, `uint8 result is out of range: ${value}`);
        if (kind === "uint16") assert.ok(value <= 0xffff, `uint16 result is out of range: ${value}`);
        return { kind: "scalar", scalarKind: kind, value: BigInt(value) };
      }
      case "uint64":
        assert.equal(typeof physical, "bigint", "uint64 must use the WebAssembly i64 lane");
        return { kind: "scalar", scalarKind: "uint64", value: BigInt.asUintN(64, physical) };
      case "usize":
        assert.equal(typeof physical, "bigint", "usize must use the WebAssembly i64 lane");
        return { kind: "usize", value: BigInt.asUintN(64, physical) };
      case "erased":
        assert.equal(this.checkedWord("erased", physical), 0, "erased sentinel must be zero");
        return { kind: "erased" };
      case "reuseToken": {
        const word = this.checkedWord("reuseToken", physical);
        return { kind: "reuseToken", location: word === 0 ? null : this.locationOf(word) };
      }
      case "object":
      case "tagged":
      case "tobject": {
        const word = this.checkedWord(kind, physical);
        const classification = this.classify(word);
        if (classification === "immediate" || kind === "tagged" ||
            (classification === "heap" && this.readHeader(word).kind === KIND.natural &&
              this.readHeader(word).persistent && this.readHeader(word).aux0 === 1)) {
          return { kind: "tagged", payload: this.taggedPayload(word) };
        }
        return { kind: "heap", location: this.locationOf(word) };
      }
      default:
        throw new Error(`unsupported concrete result ABI kind: ${kind}`);
    }
  }

  locationOf(address) {
    const location = this.addressLocations.get(unsigned32(address));
    assert.notEqual(location, undefined, `concrete address ${unsigned32(address)} has no logical location`);
    return location;
  }

  addressOf(location) {
    assert.ok(Number.isSafeInteger(location) && location >= 0,
      "concrete location must be a nonnegative safe integer");
    const address = this.locationAddresses.get(location);
    assert.notEqual(address, undefined, `concrete location ${location} has no physical address`);
    return address;
  }

  naturalLiteral(operation, args) {
    assert.equal(args.length, 0, "natural literal host arity mismatch");
    return signed32(this.allocateNatural(operation.value));
  }

  stringLiteral(operation, args) {
    assert.equal(args.length, 0, "string literal host arity mismatch");
    return signed32(this.allocateString(operation.value));
  }

  allocCtor(operation, args) {
    assert.equal(args.length, operation.fields.length, "constructor host arity mismatch");
    assert.equal(operation.size, operation.fields.length, "constructor manifest size mismatch");
    const fields = operation.fields.map((kind, index) => this.checkedWord(kind, args[index]));
    if (operation.size === 0 && operation.usize === 0 && operation.ssize === 0) {
      return signed32(this.encodeTagged(operation.tag));
    }
    const bytes = align8(HEADER_BYTES + SLOT_BYTES * (operation.size + operation.usize) +
      operation.ssize);
    const address = this.allocate(KIND.constructor, bytes - HEADER_BYTES, {
      aux0: Number(operation.tag),
      aux1: operation.size,
      aux2: operation.usize,
      aux3: operation.ssize,
    });
    fields.forEach((field, index) => this.writeWordSlot(address + HEADER_BYTES + SLOT_BYTES * index,
      field));
    this.descriptors.set(address, {
      kind: "constructor",
      fieldKinds: [...operation.fields],
    });
    return signed32(address);
  }

  constructorHeader(word) {
    const address = this.checkedWord("object", word);
    const header = this.readHeader(address);
    if (header.kind !== KIND.constructor) {
      throw new ConcreteFault({ kind: "expectedConstructor" });
    }
    return [address, header];
  }

  objectProj(operation, args) {
    assert.equal(args.length, 1, "object projection host arity mismatch");
    const [address, header] = this.constructorHeader(args[0]);
    if (operation.index >= header.aux1) {
      throw new ConcreteFault({
        kind: "objectFieldOutOfBounds",
        index: operation.index,
        size: header.aux1,
      });
    }
    return signed32(this.readWordSlot(address + HEADER_BYTES + SLOT_BYTES * operation.index));
  }

  objectSet(operation, args) {
    assert.equal(args.length, 2, "object mutation host arity mismatch");
    const [address, header] = this.constructorHeader(args[0]);
    const field = this.checkedWord(operation.field, args[1]);
    if (operation.index >= header.aux1) {
      throw new ConcreteFault({
        kind: "objectFieldOutOfBounds",
        index: operation.index,
        size: header.aux1,
      });
    }
    this.writeU32(address + HEADER_BYTES + SLOT_BYTES * operation.index, field);
  }

  usizeFieldIndex(header, slot) {
    const start = header.aux1;
    const index = slot - start;
    if (index < 0 || index >= header.aux2) {
      throw new ConcreteFault({
        kind: "usizeFieldOutOfBounds",
        index: slot,
        size: start + header.aux2,
      });
    }
    return index;
  }

  usizeProj(operation, args) {
    assert.equal(args.length, 1, "usize projection host arity mismatch");
    const [address, header] = this.constructorHeader(args[0]);
    const index = this.usizeFieldIndex(header, operation.index);
    return BigInt.asIntN(64,
      this.readU64(address + HEADER_BYTES + SLOT_BYTES * (header.aux1 + index)));
  }

  usizeSet(operation, args) {
    assert.equal(args.length, 2, "usize mutation host arity mismatch");
    const [address, header] = this.constructorHeader(args[0]);
    assert.equal(typeof args[1], "bigint", "usize mutation must use the WebAssembly i64 lane");
    const index = this.usizeFieldIndex(header, operation.index);
    this.writeU64(address + HEADER_BYTES + SLOT_BYTES * (header.aux1 + index), args[1]);
  }

  scalarByteWidth(kind) {
    switch (kind) {
      case "uint8": return 1;
      case "uint16": return 2;
      case "uint32": return 4;
      case "uint64": return 8;
      default: throw new Error(`unsupported concrete packed scalar kind: ${kind}`);
    }
  }

  scalarAddress(operation, address, header) {
    const bytes = this.scalarByteWidth(operation.result ?? operation.field);
    if (operation.width !== header.aux1 + header.aux2 ||
        operation.offset + bytes > header.aux3) {
      throw new ConcreteFault({
        kind: "scalarFieldMissing",
        width: operation.width,
        offset: operation.offset,
      });
    }
    return address + HEADER_BYTES + SLOT_BYTES * operation.width + operation.offset;
  }

  scalarProj(operation, args) {
    assert.equal(args.length, 1, "scalar projection host arity mismatch");
    const [address, header] = this.constructorHeader(args[0]);
    const fieldAddress = this.scalarAddress(operation, address, header);
    switch (operation.result) {
      case "uint8": return this.view.getUint8(fieldAddress);
      case "uint16": return this.view.getUint16(fieldAddress, true);
      case "uint32": return signed32(this.readU32(fieldAddress));
      case "uint64": return BigInt.asIntN(64, this.readU64(fieldAddress));
      default: throw new Error(`unsupported concrete packed scalar kind: ${operation.result}`);
    }
  }

  scalarSet(operation, args) {
    assert.equal(args.length, 2, "scalar mutation host arity mismatch");
    const [address, header] = this.constructorHeader(args[0]);
    const fieldAddress = this.scalarAddress(operation, address, header);
    switch (operation.field) {
      case "uint8":
        this.view.setUint8(fieldAddress, unsigned32(args[1]));
        return;
      case "uint16":
        this.view.setUint16(fieldAddress, unsigned32(args[1]), true);
        return;
      case "uint32":
        this.writeU32(fieldAddress, args[1]);
        return;
      case "uint64":
        assert.equal(typeof args[1], "bigint", "uint64 mutation must use i64");
        this.writeU64(fieldAddress, args[1]);
        return;
      default:
        throw new Error(`unsupported concrete packed scalar kind: ${operation.field}`);
    }
  }

  setTag(operation, args) {
    assert.equal(args.length, 1, "setTag host arity mismatch");
    const [address, header] = this.constructorHeader(args[0]);
    this.writeHeader(address, { ...header, aux0: Number(operation.tag) });
  }

  getTag(args) {
    assert.equal(args.length, 1, "getTag host arity mismatch");
    const word = this.checkedWord("tobject", args[0]);
    if (this.classify(word) === "immediate") {
      return signed32(this.decodeImmediate(word));
    }
    const header = this.readHeader(word);
    if (header.kind === KIND.constructor) return signed32(header.aux0);
    if (header.kind === KIND.natural && header.persistent && header.aux0 === 1) {
      return signed32(this.readU64(word + HEADER_BYTES));
    }
    throw new ConcreteFault({ kind: "expectedConstructor" });
  }

  writeCapture(address, kind, physical) {
    if (["uint64", "usize", "float"].includes(kind)) {
      assert.equal(typeof physical, "bigint", `${kind} closure capture must use i64`);
      this.writeU64(address, physical);
      return;
    }
    assert.equal(typeof physical, "number", `${kind} closure capture must use i32`);
    this.writeWordSlot(address, unsigned32(physical));
  }

  readCapture(address, kind) {
    if (["uint64", "usize", "float"].includes(kind)) {
      return BigInt.asIntN(64, this.readU64(address));
    }
    return signed32(this.readWordSlot(address));
  }

  partialApply(operation, args) {
    assert.equal(args.length, operation.fields.length, "partial application host arity mismatch");
    assert.equal(operation.fixed, operation.fields.length,
      "partial application manifest fixed-count mismatch");
    const targetId = this.closureDispatch.indexOf(operation.function);
    const descriptorId = this.closureDescriptors.findIndex((kinds) =>
      sameKinds(kinds, operation.fields));
    assert.ok(targetId >= 0, `unknown concrete closure target ${operation.function}`);
    assert.ok(descriptorId >= 0, "unknown concrete closure capture descriptor");
    const address = this.allocate(KIND.closure, SLOT_BYTES * args.length, {
      aux0: targetId,
      aux1: operation.arity,
      aux2: operation.fixed,
      aux3: descriptorId,
    });
    operation.fields.forEach((kind, index) =>
      this.writeCapture(address + HEADER_BYTES + SLOT_BYTES * index, kind, args[index]));
    this.descriptors.set(address, {
      kind: "closure",
      function: operation.function,
      fieldKinds: [...operation.fields],
    });
    return signed32(address);
  }

  closureMetadata(word) {
    const address = this.checkedWord("object", word);
    const header = this.readHeader(address);
    if (header.kind !== KIND.closure) {
      throw new ConcreteFault({ kind: "expectedClosure" });
    }
    const functionName = this.closureDispatch[header.aux0];
    const fields = this.closureDescriptors[header.aux3];
    assert.notEqual(functionName, undefined, `unknown concrete closure target id ${header.aux0}`);
    assert.ok(fields && fields.length === header.aux2,
      `unknown concrete closure descriptor id ${header.aux3}`);
    return { address, header, functionName, fields };
  }

  closureMatches(operation, args) {
    assert.equal(args.length, 1, "closure match host arity mismatch");
    const metadata = this.closureMetadata(args[0]);
    return metadata.functionName === operation.function &&
      metadata.header.aux1 === operation.arity && metadata.header.aux2 === operation.fixed ? 1 : 0;
  }

  closureProj(operation, args) {
    assert.equal(args.length, 1, "closure projection host arity mismatch");
    const metadata = this.closureMetadata(args[0]);
    assert.ok(metadata.functionName === operation.function &&
      metadata.header.aux1 === operation.arity && metadata.header.aux2 === operation.fixed,
    "concrete closure metadata mismatch");
    assert.equal(metadata.fields[operation.index], operation.result,
      "concrete closure capture kind mismatch");
    return this.readCapture(metadata.address + HEADER_BYTES + SLOT_BYTES * operation.index,
      operation.result);
  }

  markPersistentWord(word) {
    const value = unsigned32(word);
    const classification = this.classify(value);
    if (classification === "immediate" || classification === "sentinel") return;
    if (classification !== "heap") {
      throw new ConcreteFault({ kind: "expectedObject" });
    }
    const header = this.readHeader(value);
    if (header.persistent) return;
    const owned = this.ownedWords(value, header);
    this.writeHeader(value, { ...header, persistent: true, rc: 0 });
    for (const child of owned) this.markPersistentWord(child);
  }

  cacheSet(operation, args) {
    assert.equal(args.length, 1, "cacheSet host arity mismatch");
    const physical = args[0];
    if (OBJECT_KINDS.has(operation.value) || operation.value === "erased" ||
        operation.value === "reuseToken") {
      const word = this.checkedWord(operation.value, physical);
      this.markPersistentWord(word);
    }
    this.globals.set(operation.declaration, { kind: operation.value, physical });
    return physical;
  }

  boxedScalarCode(kind) {
    switch (kind) {
      case "uint8": return 1;
      case "uint16": return 2;
      case "uint32": return 3;
      case "uint64": return 4;
      case "usize": return 5;
      default: throw new Error(`unsupported concrete boxed scalar kind: ${kind}`);
    }
  }

  boxedScalarPayload(kind, physical) {
    if (["uint8", "uint16", "uint32"].includes(kind)) {
      assert.equal(typeof physical, "number", `${kind} box operand must use i32`);
      return BigInt(unsigned32(physical));
    }
    assert.equal(typeof physical, "bigint", `${kind} box operand must use i64`);
    return BigInt.asUintN(64, physical);
  }

  physicalScalar(kind, payload) {
    return ["uint64", "usize"].includes(kind)
      ? BigInt.asIntN(64, payload)
      : signed32(payload);
  }

  box(operation, args) {
    assert.equal(args.length, 1, "box host arity mismatch");
    const payload = this.boxedScalarPayload(operation.scalar, args[0]);
    if (payload <= MAX_TAGGED_PAYLOAD) {
      return signed32(this.encodeTagged(payload));
    }
    const payloadBytes = ["uint64", "usize"].includes(operation.scalar) ? 8 : 4;
    const address = this.allocate(KIND.boxed, SLOT_BYTES, {
      aux0: this.boxedScalarCode(operation.scalar),
      aux1: payloadBytes,
    });
    this.writeU64(address + HEADER_BYTES, payload);
    this.descriptors.set(address, { kind: "boxed", scalarKind: operation.scalar });
    return signed32(address);
  }

  unbox(operation, args) {
    assert.equal(args.length, 1, "unbox host arity mismatch");
    const word = this.checkedWord("tobject", args[0]);
    const classification = this.classify(word);
    if (classification === "immediate" || this.isPromotedTag(this.readHeader(word))) {
      return this.physicalScalar(operation.scalar, this.taggedPayload(word));
    }
    const header = this.readHeader(word);
    if (header.kind !== KIND.boxed) {
      throw new ConcreteFault({ kind: "expectedScalar" });
    }
    const descriptor = this.descriptors.get(word);
    assert.equal(descriptor?.kind, "boxed", "missing concrete boxed-scalar descriptor");
    assert.equal(descriptor.scalarKind, operation.scalar,
      "concrete boxed scalar kind does not match unbox operation");
    return this.physicalScalar(operation.scalar, this.readU64(word + HEADER_BYTES));
  }

  isPromotedTag(header) {
    return header.kind === KIND.natural && header.persistent && header.aux0 === 1;
  }

  isShared(args) {
    assert.equal(args.length, 1, "isShared host arity mismatch");
    const word = this.checkedWord("tobject", args[0]);
    if (this.classify(word) === "immediate") return 1;
    const header = this.readHeader(word);
    return header.persistent || header.rc !== 1 ? 1 : 0;
  }

  inc(operation, args) {
    assert.equal(args.length, 1, "inc host arity mismatch");
    const word = unsigned32(args[0]);
    const classification = this.classify(word);
    if (classification === "immediate") {
      if (operation.check) return;
      throw new ConcreteFault({ kind: "expectedHeapReference" });
    }
    if (classification !== "heap") {
      throw new ConcreteFault({ kind: "expectedObject" });
    }
    const header = this.readHeader(word);
    if (this.isPromotedTag(header)) {
      if (operation.check) return;
      throw new ConcreteFault({ kind: "expectedHeapReference" });
    }
    if (!header.persistent) {
      assert.ok(header.rc + operation.amount <= 0xffffffff,
        "concrete reference count overflow");
      this.writeHeader(word, { ...header, rc: header.rc + operation.amount });
    }
  }

  ownedWords(address, header) {
    const descriptor = this.descriptors.get(address);
    const kinds = header.kind === KIND.constructor && descriptor?.kind === "constructor"
      ? descriptor.fieldKinds
      : header.kind === KIND.closure
        ? this.closureDescriptors[header.aux3]
        : [];
    const result = [];
    kinds.forEach((kind, index) => {
      if (OBJECT_FIELD_KINDS.has(kind)) {
        result.push(this.readWordSlot(address + HEADER_BYTES + SLOT_BYTES * index));
      }
    });
    return result;
  }

  releaseWord(word, check) {
    const value = unsigned32(word);
    const classification = this.classify(value);
    if (classification === "immediate" || classification === "sentinel") {
      if (check) return;
      throw new ConcreteFault({
        kind: classification === "immediate" ? "expectedHeapReference" : "expectedObject",
      });
    }
    if (classification !== "heap") {
      throw new ConcreteFault({ kind: "expectedObject" });
    }
    const header = this.readHeader(value);
    if (this.isPromotedTag(header)) {
      if (check) return;
      throw new ConcreteFault({ kind: "expectedHeapReference" });
    }
    if (header.persistent) return;
    if (header.rc === 0) {
      throw new ConcreteFault({
        kind: "referenceCountUnderflow",
        location: this.locationOf(value),
      });
    }
    if (header.rc > 1) {
      this.writeHeader(value, { ...header, rc: header.rc - 1 });
      return;
    }
    const owned = this.ownedWords(value, header);
    this.writeHeader(value, {
      kind: KIND.freed,
      persistent: false,
      live: false,
      rc: 0,
      bytes: header.bytes,
      aux0: 0,
      aux1: 0,
      aux2: 0,
      aux3: 0,
    });
    for (const child of owned) this.releaseWord(child, true);
  }

  dec(operation, args) {
    assert.equal(args.length, 1, "dec host arity mismatch");
    for (let index = 0; index < operation.amount; ++index) {
      this.releaseWord(args[0], operation.check);
    }
  }

  deleteObject(args) {
    assert.equal(args.length, 1, "delete host arity mismatch");
    const word = unsigned32(args[0]);
    if (word === 0) return;
    if (this.classify(word) !== "heap") {
      throw new ConcreteFault({ kind: "expectedHeapReference" });
    }
    const header = this.readHeader(word);
    if (this.isPromotedTag(header)) {
      throw new ConcreteFault({ kind: "expectedHeapReference" });
    }
    this.writeHeader(word, {
      kind: KIND.freed,
      persistent: false,
      live: false,
      rc: 0,
      bytes: header.bytes,
      aux0: 0,
      aux1: 0,
      aux2: 0,
      aux3: 0,
    });
  }

  reset(operation, args) {
    assert.equal(args.length, 1, "reset host arity mismatch");
    const word = unsigned32(args[0]);
    const classification = this.classify(word);
    if (classification === "immediate") return 0;
    if (classification !== "heap") {
      throw new ConcreteFault({ kind: "expectedObject" });
    }
    const header = this.readHeader(word);
    if (this.isPromotedTag(header) || header.persistent || header.rc !== 1) {
      this.releaseWord(word, true);
      return 0;
    }
    if (header.kind !== KIND.constructor) {
      throw new ConcreteFault({ kind: "expectedConstructor" });
    }
    if (operation.objectFields > header.aux1) {
      throw new ConcreteFault({
        kind: "objectFieldOutOfBounds",
        index: operation.objectFields,
        size: header.aux1,
      });
    }
    const owned = Array.from({ length: operation.objectFields }, (_, index) =>
      this.readWordSlot(word + HEADER_BYTES + SLOT_BYTES * index));
    for (let index = 0; index < operation.objectFields; ++index) {
      this.writeWordSlot(word + HEADER_BYTES + SLOT_BYTES * index, this.encodeImmediate(0n));
    }
    for (const child of owned) this.releaseWord(child, true);
    return signed32(word);
  }

  allocateConstructorOperation(operation, args) {
    return this.allocCtor({
      ...operation,
      kind: "allocCtor",
    }, args);
  }

  reuse(operation, args) {
    assert.equal(args.length, operation.fields.length + 1, "reuse host arity mismatch");
    const token = unsigned32(args[0]);
    const fields = operation.fields.map((kind, index) =>
      this.checkedWord(kind, args[index + 1]));
    if (token === 0) {
      return this.allocateConstructorOperation(operation, args.slice(1));
    }
    if (this.classify(token) !== "heap") {
      throw new ConcreteFault({ kind: "expectedReuseToken" });
    }
    const header = this.readHeader(token);
    if (header.kind !== KIND.constructor) {
      throw new ConcreteFault({ kind: "expectedConstructor" });
    }
    const requiredBytes = align8(HEADER_BYTES + SLOT_BYTES * (operation.size + operation.usize) +
      operation.ssize);
    assert.ok(requiredBytes <= header.bytes,
      `concrete reuse allocation is too small: ${header.bytes} < ${requiredBytes}`);
    new Uint8Array(this.buffer, token + HEADER_BYTES, header.bytes - HEADER_BYTES).fill(0);
    fields.forEach((field, index) =>
      this.writeWordSlot(token + HEADER_BYTES + SLOT_BYTES * index, field));
    this.writeHeader(token, {
      ...header,
      kind: KIND.constructor,
      persistent: false,
      live: true,
      aux0: operation.updateHeader ? Number(operation.tag) : header.aux0,
      aux1: operation.size,
      aux2: operation.usize,
      aux3: operation.ssize,
    });
    this.descriptors.set(token, {
      kind: "constructor",
      fieldKinds: [...operation.fields],
    });
    return signed32(token);
  }

  external(operation, physicalArgs) {
    assert.equal(physicalArgs.length, operation.params.length,
      "external host arity mismatch");
    assert.equal(operation.results.length, 1,
      "concrete external host requires exactly one result");
    const args = operation.params.map((kind, index) =>
      this.decode(kind, physicalArgs[index]));
    const implementation = this.externalRegistry.get(operation.declaration);
    if (implementation === undefined) {
      throw new ConcreteFault({
        kind: "externalFailure",
        name: operation.declaration,
        message: "no concrete external implementation installed",
      });
    }
    const response = implementation({
      declaration: operation.declaration,
      args,
      host: this,
      world: this.world,
    });
    assert.ok(response && typeof response === "object",
      `concrete external ${operation.declaration} returned no response`);
    assert.ok(response.value && typeof response.value === "object",
      `concrete external ${operation.declaration} returned no semantic value`);
    assert.ok(response.world === undefined ||
      (Number.isSafeInteger(response.world) && response.world >= 0),
    `concrete external ${operation.declaration} returned an invalid world`);
    if (response.world !== undefined) {
      this.world = response.world;
    }
    this.trace.push({
      name: operation.declaration,
      args: args.map((value) => this.valueJson(value)),
      result: this.valueJson(response.value),
    });
    return this.encode(operation.results[0], response.value);
  }

  importFunction(operation) {
    switch (operation.kind) {
      case "naturalLiteral":
        return (...args) => this.naturalLiteral(operation, args);
      case "stringLiteral":
        return (...args) => this.stringLiteral(operation, args);
      case "allocCtor":
        return (...args) => this.allocCtor(operation, args);
      case "objectProj":
        return (...args) => this.objectProj(operation, args);
      case "objectSet":
        return (...args) => this.objectSet(operation, args);
      case "usizeProj":
        return (...args) => this.usizeProj(operation, args);
      case "usizeSet":
        return (...args) => this.usizeSet(operation, args);
      case "scalarProj":
        return (...args) => this.scalarProj(operation, args);
      case "scalarSet":
        return (...args) => this.scalarSet(operation, args);
      case "setTag":
        return (...args) => this.setTag(operation, args);
      case "getTag":
        return (...args) => this.getTag(args);
      case "partialApply":
        return (...args) => this.partialApply(operation, args);
      case "closureMatches":
        return (...args) => this.closureMatches(operation, args);
      case "closureProj":
        return (...args) => this.closureProj(operation, args);
      case "cacheSet":
        return (...args) => this.cacheSet(operation, args);
      case "box":
        return (...args) => this.box(operation, args);
      case "unbox":
        return (...args) => this.unbox(operation, args);
      case "isShared":
        return (...args) => this.isShared(args);
      case "inc":
        return (...args) => this.inc(operation, args);
      case "dec":
        return (...args) => this.dec(operation, args);
      case "delete":
        return (...args) => this.deleteObject(args);
      case "reset":
        return (...args) => this.reset(operation, args);
      case "reuse":
        return (...args) => this.reuse(operation, args);
      case "external":
        return (...args) => this.external(operation, args);
      default:
        throw new Error(`unsupported concrete artifact operation: ${operation.kind}`);
    }
  }

  imports(manifestImports) {
    const imports = {};
    for (const descriptor of manifestImports) {
      imports[descriptor.module] ??= {};
      assert.equal(imports[descriptor.module][descriptor.name], undefined,
        `duplicate import ${descriptor.module}.${descriptor.name}`);
      imports[descriptor.module][descriptor.name] = this.importFunction(descriptor.operation);
    }
    return imports;
  }

  valueJson(value) {
    switch (value.kind) {
      case "tagged":
        return { kind: "object", reference: { kind: "tagged", payload: value.payload.toString() } };
      case "heap":
        return { kind: "object", reference: { kind: "heap", location: value.location } };
      case "usize":
        return { kind: "usize", value: value.value.toString() };
      case "scalar":
        return {
          kind: "scalar",
          scalar: { kind: value.scalarKind, value: value.value.toString() },
        };
      case "erased":
        return { kind: "erased" };
      case "reuseToken":
        return { kind: "reuseToken", location: value.location };
      default:
        throw new Error(`cannot observe concrete value kind ${value.kind}`);
    }
  }

  objectJson(address, header) {
    const descriptor = this.descriptors.get(address);
    if (header.kind === KIND.constructor) {
      assert.equal(descriptor?.kind, "constructor", "missing concrete constructor descriptor");
      const objectFields = descriptor.fieldKinds.map((kind, index) =>
        this.decode(kind, signed32(this.readWordSlot(address + HEADER_BYTES + SLOT_BYTES * index))));
      const usizeFields = Array.from({ length: header.aux2 }, (_, index) =>
        this.readU64(address + HEADER_BYTES + SLOT_BYTES * (header.aux1 + index)).toString());
      return {
        kind: "ctor",
        tag: header.aux0.toString(),
        objectFields: objectFields.map((value) => this.valueJson(value)),
        usizeFields,
        scalarFields: [],
      };
    }
    if (header.kind === KIND.closure) {
      const metadata = this.closureMetadata(address);
      const fixed = metadata.fields.map((kind, index) =>
        this.decode(kind, this.readCapture(address + HEADER_BYTES + SLOT_BYTES * index, kind)));
      return {
        kind: "closure",
        function: metadata.functionName,
        arity: header.aux1,
        fixed: fixed.map((value) => this.valueJson(value)),
      };
    }
    if (header.kind === KIND.natural) {
      return { kind: "natural", value: this.readNatural(address, header).toString() };
    }
    if (header.kind === KIND.integer) {
      return { kind: "integer", value: this.readInteger(address, header).toString() };
    }
    if (header.kind === KIND.string) {
      return { kind: "string", value: this.readString(address, header) };
    }
    if (header.kind === KIND.boxed) {
      const kind = descriptor?.scalarKind;
      assert.ok(kind, "missing concrete boxed-scalar descriptor");
      const value = kind === "usize"
        ? { kind: "usize", value: this.readU64(address + HEADER_BYTES) }
        : { kind: "scalar", scalarKind: kind, value: this.readU64(address + HEADER_BYTES) };
      return { kind: "boxed", type: scalarTypeRepr(kind), value: this.valueJson(value) };
    }
    throw new Error(`cannot observe concrete heap object kind ${header.kind}`);
  }

  ownedAddresses(address, header) {
    const descriptor = this.descriptors.get(address);
    const kinds = header.kind === KIND.constructor && descriptor?.kind === "constructor"
      ? descriptor.fieldKinds
      : header.kind === KIND.closure
        ? this.closureDescriptors[header.aux3]
        : [];
    const result = [];
    kinds.forEach((kind, index) => {
      if (!OBJECT_FIELD_KINDS.has(kind)) return;
      const word = this.readWordSlot(address + HEADER_BYTES + SLOT_BYTES * index);
      if (this.classify(word) === "heap") {
        const childHeader = this.readHeader(word);
        if (!(childHeader.kind === KIND.natural && childHeader.persistent && childHeader.aux0 === 1)) {
          result.push(word);
        }
      }
    });
    return result;
  }

  reachableAddresses(value) {
    const rootAddress = value.kind === "heap" ? this.locationAddresses.get(value.location) : undefined;
    const pending = rootAddress === undefined ? [] : [rootAddress];
    const seen = new Set();
    while (pending.length > 0) {
      const address = pending.shift();
      if (seen.has(address)) continue;
      seen.add(address);
      const header = this.readHeader(address);
      pending.unshift(...this.ownedAddresses(address, header));
    }
    return seen;
  }

  observation(resultKind, physicalResult) {
    const value = this.decode(resultKind, physicalResult);
    const reachable = this.reachableAddresses(value);
    return {
      outcome: { kind: "returned", value: this.valueJson(value) },
      reachableHeap: this.allocations
        .filter((address) => reachable.has(address))
        .map((address) => {
          const header = this.readHeader(address);
          return {
            location: this.locationOf(address),
            rc: header.rc,
            persistent: header.persistent,
            live: header.live,
            object: this.objectJson(address, header),
          };
        }),
      world: this.world,
      trace: this.trace,
    };
  }

  faultObservation(fault) {
    return {
      outcome: { kind: "fault", fault },
      reachableHeap: [],
      world: this.world,
      trace: this.trace,
    };
  }
}
