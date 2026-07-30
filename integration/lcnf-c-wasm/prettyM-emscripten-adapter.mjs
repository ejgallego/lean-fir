import { loadEmscriptenModule } from "./emscripten-loader.mjs";

export const PRETTY_M_BROWSER_API_VERSION = "fir.prettyM.browser/v1";
export const PRETTY_M_INPUT_LAYOUT_VERSION =
  "lean-4.32-Std.Format.compact/v1";
export const PRETTY_M_EMSCRIPTEN_WIRE_VERSION =
  "fir.prettyM.emscripten-wire/v1";

const MAX_UINT32 = 0xffffffff;
const DEFAULT_MAXIMUM_NODES = 1_000_000;
const DEFAULT_MAXIMUM_BYTES = 64 * 1024 * 1024;
const REQUIRED_EXPORTS = Object.freeze([
  "fir_lcnf_c_pretty_input_alloc",
  "fir_lcnf_c_pretty_render",
  "fir_lcnf_c_pretty_result_ptr",
  "fir_lcnf_c_pretty_result_len",
  "fir_lcnf_c_pretty_release",
]);

function fail(message) {
  throw new Error(`FIR Emscripten prettyM adapter: ${message}`);
}

function requireCondition(condition, message) {
  if (!condition) fail(message);
}

function defaultNow() {
  if (
    globalThis.performance &&
    typeof globalThis.performance.now === "function"
  ) {
    return globalThis.performance.now();
  }
  return Date.now();
}

function elapsed(now, started) {
  const result = now() - started;
  return Number.isFinite(result) && result >= 0 ? result : 0;
}

function ownKeys(value, required, optional = []) {
  const allowed = new Set([...required, ...optional]);
  for (const key of required) {
    requireCondition(
      Object.hasOwn(value, key),
      `Format.${value.kind ?? "?"} is missing property ${key}`,
    );
  }
  for (const key of Object.keys(value)) {
    requireCondition(
      allowed.has(key),
      `Format.${value.kind ?? "?"} has unknown property ${key}`,
    );
  }
}

function natural(value, label) {
  let result;
  if (typeof value === "bigint") {
    result = value;
  } else if (typeof value === "number") {
    requireCondition(
      Number.isSafeInteger(value),
      `${label} number must be a safe integer`,
    );
    result = BigInt(value);
  } else if (typeof value === "string") {
    requireCondition(
      /^(0|[1-9][0-9]*)$/.test(value),
      `${label} string must be a canonical unsigned decimal integer`,
    );
    result = BigInt(value);
  } else {
    fail(`${label} must be a bigint, safe integer, or canonical decimal string`);
  }
  requireCondition(result >= 0n, `${label} must be nonnegative`);
  return result;
}

function integer(value, label) {
  let result;
  if (typeof value === "bigint") {
    result = value;
  } else if (typeof value === "number") {
    requireCondition(
      Number.isSafeInteger(value),
      `${label} number must be a safe integer`,
    );
    result = BigInt(value);
  } else if (typeof value === "string") {
    requireCondition(
      /^(0|-?[1-9][0-9]*)$/.test(value),
      `${label} string must be a canonical signed decimal integer`,
    );
    result = BigInt(value);
  } else {
    fail(`${label} must be a bigint, safe integer, or canonical decimal string`);
  }
  return result;
}

function normalizeBehavior(value) {
  if (value === undefined || value === "allOrNone" || value === 0) return 0;
  if (value === "fill" || value === 1) return 1;
  fail("Format.group behavior must be allOrNone, fill, 0, or 1");
}

class ByteWriter {
  constructor(maximumBytes) {
    this.maximumBytes = maximumBytes;
    this.buffer = new Uint8Array(256);
    this.length = 0;
  }

  ensure(extra) {
    const required = this.length + extra;
    requireCondition(
      Number.isSafeInteger(required) && required <= this.maximumBytes,
      `wire request exceeds ${this.maximumBytes} bytes`,
    );
    if (required <= this.buffer.length) return;
    let capacity = this.buffer.length;
    while (capacity < required) {
      capacity = Math.min(this.maximumBytes, Math.max(capacity * 2, required));
    }
    const grown = new Uint8Array(capacity);
    grown.set(this.buffer.subarray(0, this.length));
    this.buffer = grown;
  }

  u8(value) {
    this.ensure(1);
    this.buffer[this.length] = value;
    this.length += 1;
  }

  u32(value) {
    requireCondition(
      Number.isSafeInteger(value) && value >= 0 && value <= MAX_UINT32,
      `wire UInt32 is invalid: ${value}`,
    );
    this.ensure(4);
    this.buffer[this.length] = value;
    this.buffer[this.length + 1] = value >>> 8;
    this.buffer[this.length + 2] = value >>> 16;
    this.buffer[this.length + 3] = value >>> 24;
    this.length += 4;
  }

  bytes(value) {
    this.ensure(value.length);
    this.buffer.set(value, this.length);
    this.length += value.length;
  }

  finish() {
    return this.buffer.slice(0, this.length);
  }
}

function writeNatural(writer, value) {
  const limbs = [];
  let remaining = value;
  do {
    limbs.push(Number(remaining & 0xffffffffn));
    remaining >>= 32n;
  } while (remaining !== 0n);
  writer.u32(limbs.length);
  for (const limb of limbs) writer.u32(limb);
}

function writeInteger(writer, value) {
  writer.u8(value < 0n ? 1 : 0);
  writeNatural(writer, value < 0n ? -value : value);
}

function writeString(writer, encoder, value) {
  const encoded = encoder.encode(value);
  writer.u32(encoded.length);
  writer.bytes(encoded);
}

function writeFormat(writer, encoder, root, maximumNodes) {
  const active = new WeakSet();
  const stack = [{ phase: "enter", value: root }];
  let nodes = 0;

  while (stack.length !== 0) {
    const frame = stack.pop();
    if (frame.phase === "exit") {
      active.delete(frame.value);
      continue;
    }
    const value = frame.value;
    requireCondition(
      value !== null && typeof value === "object" && !Array.isArray(value),
      "Format node must be an object",
    );
    requireCondition(!active.has(value), "Format input contains a cycle");
    requireCondition(
      typeof value.kind === "string",
      "Format node kind must be a string",
    );
    requireCondition(
      nodes < maximumNodes,
      `Format input exceeds ${maximumNodes} nodes`,
    );
    nodes += 1;
    active.add(value);
    stack.push({ phase: "exit", value });

    switch (value.kind) {
      case "nil":
        ownKeys(value, ["kind"]);
        writer.u8(0);
        break;
      case "line":
        ownKeys(value, ["kind"]);
        writer.u8(1);
        break;
      case "align":
        ownKeys(value, ["kind", "force"]);
        requireCondition(
          typeof value.force === "boolean",
          "Format.align force must be boolean",
        );
        writer.u8(2);
        writer.u8(value.force ? 1 : 0);
        break;
      case "text":
        ownKeys(value, ["kind", "text"]);
        requireCondition(
          typeof value.text === "string",
          "Format.text text must be a string",
        );
        writer.u8(3);
        writeString(writer, encoder, value.text);
        break;
      case "nest":
        ownKeys(value, ["kind", "indent", "body"]);
        writer.u8(4);
        writeInteger(writer, integer(value.indent, "Format.nest indent"));
        stack.push({ phase: "enter", value: value.body });
        break;
      case "append":
        ownKeys(value, ["kind", "left", "right"]);
        writer.u8(5);
        stack.push({ phase: "enter", value: value.right });
        stack.push({ phase: "enter", value: value.left });
        break;
      case "group":
        ownKeys(value, ["kind", "body"], ["behavior"]);
        writer.u8(6);
        writer.u8(normalizeBehavior(value.behavior));
        stack.push({ phase: "enter", value: value.body });
        break;
      case "tag":
        ownKeys(value, ["kind", "tag", "body"]);
        writer.u8(7);
        writeNatural(writer, natural(value.tag, "Format.tag tag"));
        stack.push({ phase: "enter", value: value.body });
        break;
      default:
        fail(`unknown Format node kind ${value.kind}`);
    }
  }
  return nodes;
}

function encodeRequest(request, {
  maximumNodes,
  maximumBytes,
  encoder,
}) {
  requireCondition(
    request !== null && typeof request === "object" && !Array.isArray(request),
    "render request must be an object",
  );
  ownKeys(request, ["format", "width"], ["indent", "column"]);
  const writer = new ByteWriter(maximumBytes);
  writer.bytes(Uint8Array.of(0x46, 0x50, 0x4d, 0x31));
  writeNatural(writer, natural(request.width, "width"));
  writeNatural(writer, natural(request.indent ?? 0, "indent"));
  writeNatural(writer, natural(request.column ?? 0, "column"));
  const formatNodes = writeFormat(
    writer,
    encoder,
    request.format,
    maximumNodes,
  );
  return { bytes: writer.finish(), formatNodes };
}

class ByteReader {
  constructor(bytes, maximumNodes, decoder) {
    this.bytes = bytes;
    this.maximumNodes = maximumNodes;
    this.decoder = decoder;
    this.position = 0;
  }

  require(count, label) {
    requireCondition(
      this.position + count <= this.bytes.length,
      `${label} exceeds the wire response`,
    );
  }

  u8(label) {
    this.require(1, label);
    return this.bytes[this.position++];
  }

  u32(label) {
    this.require(4, label);
    const position = this.position;
    this.position += 4;
    return (
      this.bytes[position] +
      this.bytes[position + 1] * 0x100 +
      this.bytes[position + 2] * 0x10000 +
      this.bytes[position + 3] * 0x1000000
    );
  }

  expect(value, label) {
    requireCondition(
      this.u8(label) === value,
      `wire response has invalid ${label}`,
    );
  }

  string(label) {
    const length = this.u32(`${label} length`);
    this.require(length, label);
    const start = this.position;
    this.position += length;
    try {
      return this.decoder.decode(this.bytes.subarray(start, this.position));
    } catch (error) {
      fail(`${label} is not valid UTF-8: ${error}`);
    }
  }

  natural(label) {
    const count = this.u32(`${label} limb count`);
    requireCondition(count > 0, `${label} has no limbs`);
    requireCondition(
      count <= this.maximumNodes,
      `${label} exceeds ${this.maximumNodes} limbs`,
    );
    let value = 0n;
    let shift = 0n;
    let last = 0;
    for (let index = 0; index < count; index += 1) {
      const limb = this.u32(`${label} limb`);
      value |= BigInt(limb) << shift;
      shift += 32n;
      last = limb;
    }
    requireCondition(
      count === 1 || last !== 0,
      `${label} has a non-canonical leading zero limb`,
    );
    return value;
  }

  done() {
    requireCondition(
      this.position === this.bytes.length,
      "wire response has trailing bytes",
    );
  }
}

function decodeResponse(bytes, maximumNodes, decoder) {
  const reader = new ByteReader(bytes, maximumNodes, decoder);
  reader.expect(0x46, "magic");
  reader.expect(0x50, "magic");
  reader.expect(0x52, "magic");
  reader.expect(0x31, "version");
  const status = reader.u8("status");
  if (status === 1) {
    const message = reader.string("error");
    reader.done();
    fail(`Lean prettyM rejected the request: ${message}`);
  }
  requireCondition(status === 0, `wire response status ${status} is invalid`);
  const text = reader.string("PrettyTrace.text");
  const eventCount = reader.u32("PrettyTrace event count");
  requireCondition(
    eventCount <= maximumNodes,
    `PrettyTrace exceeds ${maximumNodes} events`,
  );
  const events = [];
  for (let index = 0; index < eventCount; index += 1) {
    const kind = reader.u8("PrettyTrace event kind");
    requireCondition(kind <= 3, `PrettyTrace event kind ${kind} is invalid`);
    const eventText = reader.string("PrettyTrace event text");
    const value = reader.natural("PrettyTrace event value");
    requireCondition(
      kind !== 0 || value === 0n,
      "PrettyTrace output event has a numeric payload",
    );
    requireCondition(
      kind === 0 || eventText === "",
      "PrettyTrace numeric event has a text payload",
    );
    events.push({ kind, text: eventText, value });
  }
  reader.done();
  return { text, events };
}

function validateFacadeManifest(manifest) {
  requireCondition(
    manifest?.profile === "emscripten",
    "manifest is not an Emscripten artifact",
  );
  const exports = new Set(manifest.abi?.exports);
  for (const symbol of REQUIRED_EXPORTS) {
    requireCondition(
      exports.has(symbol),
      `manifest does not declare ${symbol}`,
    );
  }
  requireCondition(
    manifest.abi?.runtimeMethods?.includes("HEAPU8"),
    "manifest does not declare the HEAPU8 bulk-transfer view",
  );
}

/**
 * Helpers for constructing the shared compact `Std.Format` input.
 */
export const PrettyFormat = Object.freeze({
  nil: () => ({ kind: "nil" }),
  line: () => ({ kind: "line" }),
  align: (force = false) => ({ kind: "align", force }),
  text: (text) => ({ kind: "text", text }),
  nest: (indent, body) => ({ kind: "nest", indent, body }),
  append: (left, right) => ({ kind: "append", left, right }),
  group: (body, behavior = "allOrNone") =>
    ({ kind: "group", body, behavior }),
  tag: (tag, body) => ({ kind: "tag", tag, body }),
});

export class EmscriptenPrettyMAdapter {
  constructor(loaded, {
    maximumNodes = DEFAULT_MAXIMUM_NODES,
    maximumBytes = DEFAULT_MAXIMUM_BYTES,
    now = defaultNow,
  } = {}) {
    requireCondition(
      Number.isSafeInteger(maximumNodes) && maximumNodes > 0,
      "maximumNodes must be a positive safe integer",
    );
    requireCondition(
      Number.isSafeInteger(maximumBytes) &&
        maximumBytes > 0 &&
        maximumBytes <= DEFAULT_MAXIMUM_BYTES,
      `maximumBytes must be between 1 and ${DEFAULT_MAXIMUM_BYTES}`,
    );
    validateFacadeManifest(loaded.manifest);
    requireCondition(
      loaded.module.HEAPU8 instanceof Uint8Array,
      "Emscripten module does not expose HEAPU8",
    );
    this.loaded = loaded;
    this.module = loaded.module;
    this.exports = loaded.exports;
    this.maximumNodes = maximumNodes;
    this.maximumBytes = maximumBytes;
    this.now = now;
    this.encoder = new TextEncoder();
    this.decoder = new TextDecoder("utf-8", { fatal: true });
    this.disposed = false;
    this.rendering = false;
  }

  render(request) {
    requireCondition(!this.disposed, "adapter has been disposed");
    requireCondition(!this.rendering, "render is not reentrant");
    this.rendering = true;
    try {
      const encodeStarted = this.now();
      const encoded = encodeRequest(request, {
        maximumNodes: this.maximumNodes,
        maximumBytes: this.maximumBytes,
        encoder: this.encoder,
      });
      const encodeMs = elapsed(this.now, encodeStarted);
      const heapBytesBefore = this.module.HEAPU8.byteLength;
      const inputPointer =
        this.exports.fir_lcnf_c_pretty_input_alloc(encoded.bytes.length) >>> 0;
      requireCondition(inputPointer !== 0, "could not allocate the wire request");
      this.module.HEAPU8.set(encoded.bytes, inputPointer);

      const executeStarted = this.now();
      const executionStatus =
        this.exports.fir_lcnf_c_pretty_render(encoded.bytes.length) >>> 0;
      const executeMs = elapsed(this.now, executeStarted);
      requireCondition(
        executionStatus === 0,
        `C bridge failed with status ${executionStatus}`,
      );
      const resultPointer =
        this.exports.fir_lcnf_c_pretty_result_ptr() >>> 0;
      const resultLength =
        this.exports.fir_lcnf_c_pretty_result_len() >>> 0;
      requireCondition(
        resultLength <= this.module.HEAPU8.byteLength &&
          resultPointer <= this.module.HEAPU8.byteLength - resultLength,
        "C bridge returned an out-of-bounds result",
      );
      const response =
        this.module.HEAPU8.slice(resultPointer, resultPointer + resultLength);
      const decodeStarted = this.now();
      const trace = decodeResponse(response, this.maximumNodes, this.decoder);
      const decodeMs = elapsed(this.now, decodeStarted);
      return {
        trace,
        timings: {
          encodeMs,
          executeMs,
          decodeMs,
          totalMs: encodeMs + executeMs + decodeMs,
        },
        memory: {
          requestBytes: encoded.bytes.length,
          responseBytes: response.length,
          formatNodes: encoded.formatNodes,
          heapBytesBefore,
          heapBytesAfter: this.module.HEAPU8.byteLength,
        },
      };
    } finally {
      this.rendering = false;
    }
  }

  dispose() {
    if (!this.disposed) {
      this.exports.fir_lcnf_c_pretty_release();
      this.disposed = true;
    }
  }
}

/**
 * Verify, instantiate, and initialize a packaged C/Emscripten prettyM module.
 */
export async function loadEmscriptenPrettyMAdapter(
  manifestSource,
  options = {},
) {
  const loaded = await loadEmscriptenModule(manifestSource, options.loader);
  return new EmscriptenPrettyMAdapter(loaded, options);
}
