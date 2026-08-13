const PAGE_BYTES = 65536;
const HEADER_BYTES = 32;
const HEAP_ALIGNMENT = 8;
const HEAP_BASE = 1024;
const KIND_BYTE_ARRAY = 7;
const LIVE = 2;
const LIVE_PERSISTENT = 3;
const BYTE_ARRAY_MARKER = 0x42595445;
const STORED_ENTRY = "Zip.Wasm.compressStored";

export const LEAN_ZIP_BYTE_ARRAY_ADAPTER_API_VERSION =
  "fir.lean-zip.byte-array.browser/v1";
export const LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION =
  "fir.wasm.byte-array/v2";
export const LEAN_ZIP_BYTE_ARRAY_OWNERSHIP_VERSION =
  "fir.lean-zip.byte-array.scratch-transfer/v2";

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
  throw new TypeError("compress input must be an ArrayBuffer or view");
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

function verifyDescriptor(descriptor, entry, parameterKinds) {
  if (descriptor === undefined) return;
  requireCondition(descriptor !== null && typeof descriptor === "object",
    "module descriptor must be an object");
  requireCondition(descriptor.entry === entry,
    `module descriptor entry must be ${entry}`);
  requireCondition(Array.isArray(descriptor.params) &&
    descriptor.params.length === parameterKinds.length &&
    descriptor.params.every((kind, index) => kind === parameterKinds[index]),
  `module descriptor parameters must be ${parameterKinds.join(", ")}`);
  requireCondition(descriptor.result === "object",
    "module descriptor must expose one ByteArray object result");
  requireCondition(Array.isArray(descriptor.imports) &&
    descriptor.imports.length === 0,
  "module descriptor must declare zero imports");
}

function verifyModule(module, entry, label, persistentInitializer) {
  requireCondition(WebAssembly.Module.imports(module).length === 0,
    `${label} module must have zero imports`);
  const exports = WebAssembly.Module.exports(module);
  const actual = exports.map(({ name, kind }) => `${kind}:${name}`);
  const expected = [
    `function:${entry}`,
    ...(persistentInitializer === null
      ? [] : [`function:${persistentInitializer}`]),
    "function:fir_heap_frontier",
    "function:fir_heap_set_frontier",
    "function:fir_heap_rewind",
    "function:fir_heap_alloc",
    "memory:memory",
  ];
  requireCondition(actual.length === expected.length &&
    actual.every((value, index) => value === expected[index]),
  `unexpected ${label} exports: ${actual.join(", ")}`);
}

class LeanZipByteArrayAdapter {
  constructor(instance, now, entry, initialization) {
    this.instance = instance;
    this.exports = instance.exports;
    this.memory = this.exports.memory;
    this.now = now;
    this.entry = entry;
    this.initialization = initialization;
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
    requireCondition(flags === LIVE || flags === LIVE_PERSISTENT,
      "result ByteArray is not live");
    requireCondition(flags === LIVE_PERSISTENT ? rc === 0 : rc > 0,
      "result ByteArray has an invalid ownership state");
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

  compress(value, extraArguments = []) {
    const totalStarted = this.now();
    const frontierBefore = this.frontier();
    requireCondition(frontierBefore === this.initialization.checkpoint,
      "scratch arena moved below or above its persistent checkpoint");
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
      const outputAddress = this.exports[this.entry](
        encoded.address, ...extraArguments) >>> 0;
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

  compressStored(value) {
    requireCondition(this.entry === STORED_ENTRY,
      "adapter does not expose Zip.Wasm.compressStored");
    return this.compress(value);
  }

  compressLevel1(value) {
    requireCondition(this.entry === "Zip.Wasm.compressLevel1",
      "adapter does not expose Zip.Wasm.compressLevel1");
    return this.compress(value);
  }

  compressRaw(value, level) {
    requireCondition(this.entry === "Zip.Wasm.compressRaw",
      "adapter does not expose Zip.Wasm.compressRaw");
    requireCondition(Number.isInteger(level) && level >= 1 && level <= 10,
      "raw compression level must be an integer in 1..10");
    return this.compress(value, [level]);
  }
}

/** Compile/instantiate one self-contained module-owned ByteArray entry. */
export async function createLeanZipByteArrayAdapter({
  entry,
  label = "lean-zip ByteArray",
  bytes,
  module,
  descriptor,
  parameterKinds = ["object"],
  persistentInitializer = null,
  reservedMemoryBytes = null,
  now = () => performance.now(),
} = {}) {
  requireCondition(typeof entry === "string" && entry.length > 0,
    "entry must be a nonempty string");
  requireCondition(typeof now === "function", "now must be a function");
  requireCondition(Array.isArray(parameterKinds) && parameterKinds.length > 0 &&
    parameterKinds.every((kind) => typeof kind === "string" && kind.length > 0),
  "parameterKinds must be a nonempty string array");
  requireCondition(persistentInitializer === null ||
    (typeof persistentInitializer === "string" && persistentInitializer.length > 0),
  "persistentInitializer must be null or a nonempty string");
  requireCondition(reservedMemoryBytes === null ||
    (Number.isSafeInteger(reservedMemoryBytes) &&
      reservedMemoryBytes >= HEAP_BASE &&
      reservedMemoryBytes <= 0xffffffff &&
      reservedMemoryBytes % HEAP_ALIGNMENT === 0),
  "reservedMemoryBytes must be null or an aligned wasm32 heap address");
  verifyDescriptor(descriptor, entry, parameterKinds);
  const compiled = module ?? await WebAssembly.compile(bytes);
  requireCondition(compiled instanceof WebAssembly.Module,
    "module must be a WebAssembly.Module");
  verifyModule(compiled, entry, label, persistentInitializer);
  const instance = await WebAssembly.instantiate(compiled, {});
  const freshFrontier = instance.exports.fir_heap_frontier() >>> 0;
  const reservedFrontier = reservedMemoryBytes ?? freshFrontier;
  requireCondition(freshFrontier <= reservedFrontier,
    "fresh resident frontier overlaps the external runtime reservation");
  requireCondition(reservedFrontier <= instance.exports.memory.buffer.byteLength,
    "external runtime reservation exceeds module memory");
  if (freshFrontier !== reservedFrontier) {
    instance.exports.fir_heap_set_frontier(reservedFrontier);
  }
  const initialFrontier = instance.exports.fir_heap_frontier() >>> 0;
  requireCondition(initialFrontier === reservedFrontier,
    "resident frontier did not advance past the external runtime reservation");
  let initializeMs = 0;
  let idempotenceMs = 0;
  if (persistentInitializer !== null) {
    const initializeStarted = now();
    instance.exports[persistentInitializer]();
    initializeMs = elapsed(now, initializeStarted);
    const checkpoint = instance.exports.fir_heap_frontier() >>> 0;
    requireCondition(checkpoint >= initialFrontier,
      "persistent initializer moved the arena frontier backwards");
    const idempotenceStarted = now();
    instance.exports[persistentInitializer]();
    idempotenceMs = elapsed(now, idempotenceStarted);
    requireCondition((instance.exports.fir_heap_frontier() >>> 0) === checkpoint,
      "persistent initializer was not idempotent");
  }
  const checkpoint = instance.exports.fir_heap_frontier() >>> 0;
  const initialization = Object.freeze({
    entry: persistentInitializer,
    freshFrontier,
    reservedFrontier,
    reservedGrowth: reservedFrontier - freshFrontier,
    initialFrontier,
    checkpoint,
    frontierGrowth: checkpoint - initialFrontier,
    initializeMs,
    idempotenceMs,
    pages: instance.exports.memory.buffer.byteLength / PAGE_BYTES,
  });
  return new LeanZipByteArrayAdapter(instance, now, entry, initialization);
}

/** Fetch and instantiate any supported self-contained ByteArray entry. */
export async function fetchLeanZipByteArrayAdapter({
  entry, label, wasmUrl, descriptorUrl, parameterKinds,
  persistentInitializer, reservedMemoryBytes, now,
}) {
  const [wasmResponse, descriptorResponse] = await Promise.all([
    fetch(wasmUrl),
    fetch(descriptorUrl),
  ]);
  requireCondition(wasmResponse.ok,
    `failed to fetch ${wasmUrl}: HTTP ${wasmResponse.status}`);
  requireCondition(descriptorResponse.ok,
    `failed to fetch ${descriptorUrl}: HTTP ${descriptorResponse.status}`);
  return createLeanZipByteArrayAdapter({
    entry,
    label,
    bytes: await wasmResponse.arrayBuffer(),
    descriptor: await descriptorResponse.json(),
    parameterKinds,
    persistentInitializer,
    reservedMemoryBytes,
    now,
  });
}
