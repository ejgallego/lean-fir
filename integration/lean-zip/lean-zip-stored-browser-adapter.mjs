const PAGE_BYTES = 65536;
const HEADER_BYTES = 32;
const HEAP_ALIGNMENT = 8;
const HEAP_BASE = 1024;
const KIND_BYTE_ARRAY = 7;
const LIVE_PERSISTENT = 3;
const BYTE_ARRAY_MARKER = 0x42595445;
const ENTRY = "Zip.Wasm.compressStored";

export const LEAN_ZIP_STORED_ADAPTER_API_VERSION =
  "fir.lean-zip.stored.browser/v1";
export const LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION =
  "fir.wasm.byte-array/v1";
export const LEAN_ZIP_STORED_OWNERSHIP_VERSION =
  "fir.lean-zip.stored.scratch-transfer/v1";

function requireCondition(condition, message) {
  if (!condition) throw new TypeError(message);
}

function elapsed(now, started) {
  const value = now() - started;
  return value < 0 ? 0 : value;
}

function align8(value) {
  requireCondition(Number.isSafeInteger(value) && value >= 0,
    "allocation size must be a nonnegative safe integer");
  return Math.ceil(value / HEAP_ALIGNMENT) * HEAP_ALIGNMENT;
}

function asBytes(input) {
  if (input instanceof Uint8Array) return input;
  if (ArrayBuffer.isView(input)) {
    return new Uint8Array(input.buffer, input.byteOffset, input.byteLength);
  }
  if (input instanceof ArrayBuffer) return new Uint8Array(input);
  throw new TypeError("compressStored input must be an ArrayBuffer or view");
}

function writeHeader(view, address, size, capacity) {
  const allocation = align8(HEADER_BYTES + capacity);
  for (const [index, value] of [
    KIND_BYTE_ARRAY,
    LIVE_PERSISTENT,
    0,
    allocation,
    BYTE_ARRAY_MARKER,
    size,
    capacity,
    0,
  ].entries()) {
    view.setUint32(address + 4 * index, value, true);
  }
}

function verifyDescriptor(descriptor) {
  if (descriptor === undefined) return;
  requireCondition(descriptor !== null && typeof descriptor === "object",
    "module descriptor must be an object");
  requireCondition(descriptor.entry === ENTRY,
    `module descriptor entry must be ${ENTRY}`);
  requireCondition(Array.isArray(descriptor.params) &&
    descriptor.params.length === 1 && descriptor.params[0] === "object",
  "module descriptor must expose one ByteArray object parameter");
  requireCondition(descriptor.result === "object",
    "module descriptor must expose one ByteArray object result");
  requireCondition(Array.isArray(descriptor.imports) &&
    descriptor.imports.length === 0,
  "module descriptor must declare zero imports");
}

function verifyModule(module) {
  requireCondition(WebAssembly.Module.imports(module).length === 0,
    "lean-zip stored module must have zero imports");
  const exports = WebAssembly.Module.exports(module);
  const actual = exports.map(({ name, kind }) => `${kind}:${name}`);
  const expected = [
    `function:${ENTRY}`,
    "function:fir_heap_frontier",
    "function:fir_heap_set_frontier",
    "function:fir_heap_rewind",
    "function:fir_heap_alloc",
    "memory:memory",
  ];
  requireCondition(actual.length === expected.length &&
    actual.every((value, index) => value === expected[index]),
  `unexpected lean-zip stored exports: ${actual.join(", ")}`);
}

class LeanZipStoredAdapter {
  constructor(instance, now) {
    this.instance = instance;
    this.exports = instance.exports;
    this.memory = this.exports.memory;
    this.now = now;
  }

  frontier() {
    return this.exports.fir_heap_frontier() >>> 0;
  }

  encodeByteArray(input) {
    requireCondition(input.byteLength <= 0xffffffff - HEADER_BYTES - 7,
      "input is too large for the wasm32 ByteArray layout");
    const allocation = align8(HEADER_BYTES + input.byteLength);
    const address = this.exports.fir_heap_alloc(allocation) >>> 0;
    requireCondition(address >= HEAP_BASE && address % HEAP_ALIGNMENT === 0,
      "resident allocator returned an invalid ByteArray address");
    const frontier = this.frontier();
    requireCondition(frontier === address + allocation,
      "resident allocator advanced by an unexpected amount");
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, input.byteLength, input.byteLength);
    new Uint8Array(this.memory.buffer, address + HEADER_BYTES,
      input.byteLength).set(input);
    return { address, allocation };
  }

  decodeByteArray(address) {
    requireCondition(Number.isInteger(address) && address >= HEAP_BASE &&
      address % HEAP_ALIGNMENT === 0,
    "stored entry returned an invalid ByteArray address");
    const view = new DataView(this.memory.buffer);
    requireCondition(address + HEADER_BYTES <= view.byteLength,
      "stored entry returned a truncated ByteArray header");
    const kind = view.getUint32(address, true);
    const flags = view.getUint32(address + 4, true);
    const rc = view.getUint32(address + 8, true);
    const allocation = view.getUint32(address + 12, true);
    const marker = view.getUint32(address + 16, true);
    const size = view.getUint32(address + 20, true);
    const capacity = view.getUint32(address + 24, true);
    const reserved = view.getUint32(address + 28, true);
    requireCondition(kind === KIND_BYTE_ARRAY, "result is not a ByteArray");
    requireCondition(flags === LIVE_PERSISTENT,
      "result ByteArray is not a live persistent value");
    requireCondition(rc === 0, "result ByteArray has an unexpected refcount");
    requireCondition(marker === BYTE_ARRAY_MARKER,
      "result ByteArray has an unexpected layout marker");
    requireCondition(reserved === 0,
      "result ByteArray has nonzero reserved metadata");
    requireCondition(size <= capacity, "result ByteArray size exceeds capacity");
    requireCondition(allocation === align8(HEADER_BYTES + capacity),
      "result ByteArray has an invalid allocation size");
    requireCondition(address + allocation <= this.memory.buffer.byteLength,
      "result ByteArray exceeds module memory");
    return new Uint8Array(this.memory.buffer,
      address + HEADER_BYTES, size).slice();
  }

  compressStored(value) {
    const totalStarted = this.now();
    const frontierBefore = this.frontier();
    const input = asBytes(value);
    let encodeMs = 0;
    let executeMs = 0;
    let decodeMs = 0;
    let peakFrontier = frontierBefore;
    let output;
    try {
      const encodeStarted = this.now();
      const encoded = this.encodeByteArray(input);
      encodeMs = elapsed(this.now, encodeStarted);
      peakFrontier = Math.max(peakFrontier, this.frontier());

      const executeStarted = this.now();
      const outputAddress = this.exports[ENTRY](encoded.address) >>> 0;
      executeMs = elapsed(this.now, executeStarted);
      peakFrontier = Math.max(peakFrontier, this.frontier());

      const decodeStarted = this.now();
      output = this.decodeByteArray(outputAddress);
      decodeMs = elapsed(this.now, decodeStarted);
    } finally {
      this.exports.fir_heap_rewind(frontierBefore);
    }
    const totalMs = elapsed(this.now, totalStarted);
    const frontierAfter = this.frontier();
    requireCondition(frontierAfter === frontierBefore,
      "scratch arena did not return to its checkpoint");
    return {
      bytes: output,
      timings: {
        encodeMs,
        executeMs,
        decodeMs,
        totalMs,
        overheadMs: Math.max(0, totalMs - encodeMs - executeMs - decodeMs),
      },
      memory: {
        frontierBefore,
        peakFrontier,
        frontierAfter,
        frontierGrowth: peakFrontier - frontierBefore,
        pages: this.memory.buffer.byteLength / PAGE_BYTES,
      },
    };
  }
}

/** Compile/instantiate one self-contained module-owned stored compressor. */
export async function createLeanZipStoredAdapter({
  bytes,
  module,
  descriptor,
  now = () => performance.now(),
} = {}) {
  requireCondition(typeof now === "function", "now must be a function");
  verifyDescriptor(descriptor);
  const compiled = module ?? await WebAssembly.compile(bytes);
  requireCondition(compiled instanceof WebAssembly.Module,
    "module must be a WebAssembly.Module");
  verifyModule(compiled);
  const instance = await WebAssembly.instantiate(compiled, {});
  return new LeanZipStoredAdapter(instance, now);
}

/** Fetch and instantiate a stored compressor without any host imports. */
export async function fetchLeanZipStoredAdapter({ wasmUrl, descriptorUrl, now }) {
  const [wasmResponse, descriptorResponse] = await Promise.all([
    fetch(wasmUrl),
    fetch(descriptorUrl),
  ]);
  requireCondition(wasmResponse.ok,
    `failed to fetch ${wasmUrl}: HTTP ${wasmResponse.status}`);
  requireCondition(descriptorResponse.ok,
    `failed to fetch ${descriptorUrl}: HTTP ${descriptorResponse.status}`);
  return createLeanZipStoredAdapter({
    bytes: await wasmResponse.arrayBuffer(),
    descriptor: await descriptorResponse.json(),
    now,
  });
}
