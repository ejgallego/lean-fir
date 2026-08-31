/** Browser/Node adapter for the pure FIR-native Blueprint manifest resolver. */

export const VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION =
  "fir.vbp-manifest-resolver.browser/v1";
export const VBP_MANIFEST_RESOLVER_INPUT_LAYOUT_VERSION =
  "lean-4.34-VersoBlueprint.ManifestResolver-json/v1";
export const VBP_MANIFEST_RESOLVER_OWNERSHIP_VERSION =
  "fir.stateless-rewound-call/v1";
export const VBP_MANIFEST_RESOLVER_ENTRY =
  "VersoBlueprint.Runtime.ManifestResolver.resolveBatchJson";

const PAGE_BYTES = 65536;
const HEAP_BASE = 1024;
const HEADER_BYTES = 32;
const STRING_KIND = 4;
const STRING_UTF8_MARKER = 1;
const SCRATCH_LIVE_FLAGS = 2;
const STATE = new WeakMap();

function fail(message, options) {
  throw new Error(`FIR VBP manifest resolver adapter: ${message}`, options);
}

function requireCondition(condition, message) {
  if (!condition) fail(message);
}

function errorMessage(error) {
  return error instanceof Error ? error.message : String(error);
}

function u32(value) { return Number(value) >>> 0; }
function i32(value) { return Number(value) | 0; }
function align8(value) { return Math.ceil(value / 8) * 8; }
function defaultNow() { return globalThis.performance?.now?.() ?? Date.now(); }
function elapsed(now, start) {
  const value = now() - start;
  return Number.isFinite(value) && value >= 0 ? value : 0;
}

function requiredFunction(exports, name) {
  const value = exports[name];
  requireCondition(typeof value === "function",
    `module is missing function export ${name}`);
  return value;
}

function requiredMemory(exports) {
  requireCondition(exports.memory instanceof WebAssembly.Memory,
    "module is missing its memory export");
  return exports.memory;
}

function writeHeader(view, address, { kind, flags, rc = 1, bytes, aux0 = 0,
  aux1 = 0, aux2 = 0, aux3 = 0 }) {
  [kind, flags, rc, bytes, aux0, aux1, aux2, aux3].forEach((word, index) =>
    view.setUint32(address + 4 * index, u32(word), true));
}

function readU32(view, address, label) {
  requireCondition(Number.isSafeInteger(address) && address >= 0 &&
    address + 4 <= view.byteLength, `${label} is outside module memory`);
  return view.getUint32(address, true);
}

function readString(memory, decoder, word, label) {
  const address = u32(word);
  requireCondition(address >= HEAP_BASE && address % 8 === 0,
    `${label} has invalid address ${address}`);
  const view = new DataView(memory.buffer);
  const kind = readU32(view, address, label);
  const flags = readU32(view, address + 4, label);
  const bytes = readU32(view, address + 12, label);
  const marker = readU32(view, address + 16, label);
  const payloadBytes = readU32(view, address + 20, label);
  const aux2 = readU32(view, address + 24, label);
  const aux3 = readU32(view, address + 28, label);
  requireCondition(kind === STRING_KIND && (flags & 2) !== 0 &&
    marker === STRING_UTF8_MARKER && aux2 === 0 && aux3 === 0,
  `${label} is not a live canonical UTF-8 String`);
  requireCondition(bytes >= HEADER_BYTES && bytes % 8 === 0 &&
    address + bytes <= view.byteLength &&
    HEADER_BYTES + payloadBytes <= bytes,
  `${label} has a malformed allocation extent`);
  return decoder.decode(new Uint8Array(
    memory.buffer, address + HEADER_BYTES, payloadBytes));
}

function readFrontier(state) {
  const value = u32(state.frontier());
  requireCondition(value >= HEAP_BASE && value % 8 === 0 &&
    value <= state.memory.buffer.byteLength,
  `resident frontier ${value} is invalid`);
  return value;
}

function rewind(state, checkpoint) {
  const frontierBeforeRewind = readFrontier(state);
  requireCondition(frontierBeforeRewind >= checkpoint,
    "resident frontier moved below the call checkpoint");
  const clearedBytes = frontierBeforeRewind - checkpoint;
  new Uint8Array(state.memory.buffer, checkpoint, clearedBytes).fill(0);
  state.rewind(checkpoint);
  const postRewindFrontier = readFrontier(state);
  requireCondition(postRewindFrontier === checkpoint,
    `resident frontier rewound to ${postRewindFrontier}, expected ${checkpoint}`);
  return { frontierBeforeRewind, clearedBytes, postRewindFrontier };
}

function encodeString(state, value) {
  requireCondition(typeof value === "string", "input argument must be a String");
  const utf8 = state.encoder.encode(value);
  const bytes = align8(HEADER_BYTES + utf8.byteLength);
  const address = u32(state.allocate(bytes));
  requireCondition(address >= HEAP_BASE && address % 8 === 0 &&
    address + bytes <= state.memory.buffer.byteLength,
  `resident allocator returned invalid address ${address}`);
  const allocation = new Uint8Array(state.memory.buffer, address, bytes);
  allocation.fill(0);
  const view = new DataView(state.memory.buffer);
  writeHeader(view, address, {
    kind: STRING_KIND,
    flags: SCRATCH_LIVE_FLAGS,
    bytes,
    aux0: STRING_UTF8_MARKER,
    aux1: utf8.byteLength,
  });
  new Uint8Array(state.memory.buffer, address + HEADER_BYTES,
    utf8.byteLength).set(utf8);
  return { address, utf8Bytes: utf8.byteLength, allocationBytes: bytes };
}

function validateManifest(manifest) {
  requireCondition(manifest !== null && typeof manifest === "object" &&
    !Array.isArray(manifest), "Wasm descriptor must be an object");
  requireCondition(manifest.entry === VBP_MANIFEST_RESOLVER_ENTRY,
    "Wasm descriptor has the wrong entry");
  requireCondition(Array.isArray(manifest.params) &&
    manifest.params.length === 1 && manifest.params[0] === "object" &&
    manifest.result === "object",
  "Wasm descriptor must expose physical object -> object");
  requireCondition(Array.isArray(manifest.imports) &&
    manifest.imports.length === 0,
  "production resolver descriptor must have zero imports");
}

function validateBuild(build) {
  requireCondition(build !== null && typeof build === "object" &&
    !Array.isArray(build), "BUILD.json must be an object");
  requireCondition(build.abi?.version === 1 &&
    build.abi?.logical === "String -> String",
  "BUILD.json has the wrong logical ABI");
  requireCondition(build.capabilities?.browserAdapter?.apiVersion ===
    VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION,
  "BUILD.json has the wrong adapter API version");
  requireCondition(build.capabilities?.inputLayout?.version ===
    VBP_MANIFEST_RESOLVER_INPUT_LAYOUT_VERSION,
  "BUILD.json has the wrong input-layout version");
  requireCondition(build.capabilities?.ownership?.version ===
    VBP_MANIFEST_RESOLVER_OWNERSHIP_VERSION,
  "BUILD.json has the wrong ownership version");
}

function invokeCore(adapter, entry, args) {
  const state = STATE.get(adapter);
  requireCondition(state !== undefined && state.status === "active",
    "adapter is disposed or invalid");
  requireCondition(entry === VBP_MANIFEST_RESOLVER_ENTRY,
    `unsupported entry ${String(entry)}`);
  requireCondition(Array.isArray(args) && args.length === 1,
    "invoke expects exactly one argument");
  const totalStarted = state.now();
  const checkpoint = readFrontier(state);
  state.setFrontier(checkpoint);
  const pagesBefore = state.memory.buffer.byteLength / PAGE_BYTES;
  let failure;
  let output;
  let encoded;
  let frontierAfterEncode;
  let frontierAfterExecute;
  const timings = { encodeMs: 0, executeMs: 0, decodeMs: 0, rewindMs: 0 };
  const memory = { checkpoint, pagesBefore };
  try {
    const encodeStarted = state.now();
    encoded = encodeString(state, args[0]);
    timings.encodeMs = elapsed(state.now, encodeStarted);
    frontierAfterEncode = readFrontier(state);
    const executeStarted = state.now();
    const resultWord = u32(state.entry(i32(encoded.address)));
    timings.executeMs = elapsed(state.now, executeStarted);
    frontierAfterExecute = readFrontier(state);
    const decodeStarted = state.now();
    output = readString(state.memory, state.decoder, resultWord, "resolver result");
    timings.decodeMs = elapsed(state.now, decodeStarted);
  } catch (error) {
    failure = error;
  } finally {
    try {
      const rewindStarted = state.now();
      Object.assign(memory, rewind(state, checkpoint));
      timings.rewindMs = elapsed(state.now, rewindStarted);
    } catch (error) {
      failure = error;
      state.status = "poisoned";
    }
  }
  if (failure !== undefined) {
    if (state.status === "poisoned") STATE.delete(adapter);
    fail(errorMessage(failure), { cause: failure });
  }
  const totalMs = elapsed(state.now, totalStarted);
  const measured = Object.values(timings).reduce((sum, value) => sum + value, 0);
  const diagnostic = Object.freeze({
    timings: Object.freeze({ ...timings, totalMs,
      overheadMs: totalMs - measured }),
    memory: Object.freeze({ ...memory,
      frontierAfterEncode,
      frontierAfterExecute,
      peakFrontier: Math.max(frontierAfterEncode, frontierAfterExecute),
      utf8Bytes: encoded.utf8Bytes,
      inputAllocationBytes: encoded.allocationBytes,
      pagesAfter: state.memory.buffer.byteLength / PAGE_BYTES,
    }),
  });
  state.lastCall = diagnostic;
  return output;
}

export class VbpManifestResolverAdapter {
  constructor(state, build, manifest, startupTimings) {
    this.build = build;
    this.manifest = manifest;
    this.startupTimings = Object.freeze(startupTimings);
    STATE.set(this, state);
  }

  invoke(entry, args) {
    return invokeCore(this, entry, args);
  }

  get lastCall() {
    return STATE.get(this)?.lastCall ?? null;
  }

  dispose() {
    const state = STATE.get(this);
    if (state === undefined) return;
    state.status = "disposed";
    STATE.delete(this);
  }
}

export async function createVbpManifestResolverAdapter({
  bytes,
  module,
  manifest,
  build,
  now = defaultNow,
  startupTimings = {},
}) {
  requireCondition(typeof now === "function", "now must be callable");
  validateManifest(manifest);
  validateBuild(build);
  const compileStarted = now();
  let compiled = module;
  if (compiled === undefined) {
    requireCondition(bytes instanceof ArrayBuffer || ArrayBuffer.isView(bytes),
      "bytes must be an ArrayBuffer or view when module is absent");
    compiled = await WebAssembly.compile(bytes);
  } else {
    requireCondition(compiled instanceof WebAssembly.Module,
      "module must be a WebAssembly.Module");
  }
  const compileMs = elapsed(now, compileStarted);
  requireCondition(WebAssembly.Module.imports(compiled).length === 0,
    "production resolver module must have zero imports");
  const instantiateStarted = now();
  const instance = await WebAssembly.instantiate(compiled, {});
  const instantiateMs = elapsed(now, instantiateStarted);
  const exports = instance.exports;
  const memory = requiredMemory(exports);
  const state = {
    status: "active",
    module: compiled,
    instance,
    memory,
    now,
    encoder: new TextEncoder(),
    decoder: new TextDecoder("utf-8", { fatal: true }),
    frontier: requiredFunction(exports, "fir_heap_frontier"),
    setFrontier: requiredFunction(exports, "fir_heap_set_frontier"),
    rewind: requiredFunction(exports, "fir_heap_rewind"),
    allocate: requiredFunction(exports, "fir_heap_alloc"),
    entry: requiredFunction(exports, VBP_MANIFEST_RESOLVER_ENTRY),
    lastCall: null,
  };
  readFrontier(state);
  return new VbpManifestResolverAdapter(state, build, manifest, {
    fetchMs: startupTimings.fetchMs ?? 0,
    compileMs,
    instantiateMs,
    totalMs: (startupTimings.fetchMs ?? 0) + compileMs + instantiateMs,
  });
}

function baseUrl() { return globalThis.location?.href ?? "file:///"; }

export async function fetchVbpManifestResolverAdapter(artifactUrl, {
  fetchImpl = globalThis.fetch,
  descriptorUrl,
  buildUrl,
  now = defaultNow,
} = {}) {
  requireCondition(typeof fetchImpl === "function",
    "fetchVbpManifestResolverAdapter requires Fetch");
  const wasmUrl = new URL(artifactUrl, baseUrl());
  const descriptor = descriptorUrl === undefined
    ? new URL(`${wasmUrl.href}.json`) : new URL(descriptorUrl, baseUrl());
  const metadata = buildUrl === undefined
    ? new URL("BUILD.json", wasmUrl) : new URL(buildUrl, baseUrl());
  const started = now();
  const [wasmResponse, descriptorResponse, buildResponse] = await Promise.all([
    fetchImpl(wasmUrl), fetchImpl(descriptor), fetchImpl(metadata),
  ]);
  requireCondition(wasmResponse.ok, `failed to fetch ${wasmUrl}`);
  requireCondition(descriptorResponse.ok, `failed to fetch ${descriptor}`);
  requireCondition(buildResponse.ok, `failed to fetch ${metadata}`);
  const [bytes, manifest, build] = await Promise.all([
    wasmResponse.arrayBuffer(), descriptorResponse.json(), buildResponse.json(),
  ]);
  return createVbpManifestResolverAdapter({
    bytes, manifest, build, now,
    startupTimings: { fetchMs: elapsed(now, started) },
  });
}
