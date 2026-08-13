/** Browser/Node adapter for FIR-native prepared Illuminate hit scenes. */

export const ILLUMINATE_SPATIAL_HIT_SCENE_ADAPTER_API_VERSION =
  "fir.illuminate-spatial-hit-scene.browser/v1";
export const ILLUMINATE_SPATIAL_HIT_SCENE_INPUT_LAYOUT_VERSION =
  "lean-4.33-Illuminate.SpatialHitScene/v1";
export const ILLUMINATE_SPATIAL_HIT_SCENE_OWNERSHIP_VERSION =
  "fir.illuminate-spatial-hit-scene.persistent-checkpoint/v1";

const PAGE_BYTES = 65536;
const HEAP_BASE = 1024;
const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const MAX_UINT32 = 0xffffffff;
const MAX_IMMEDIATE = 0x7fffffffn;
const ARRAY_MARKER = 0x41525259;
const STRING_MARKER = 1;
const PERSISTENT_FLAGS = 3;
const SCRATCH_FLAGS = 2;
const SCENE = Symbol("fir.illuminate-spatial-hit-scene.scene");
const ADAPTER_STATE = new WeakMap();
const SCENE_STATE = new WeakMap();
const FLOAT_BITS = new DataView(new ArrayBuffer(8));

const KIND = Object.freeze({
  constructor: 1,
  string: 4,
  natural: 5,
  opaque: 8,
});

function fail(message, options) {
  throw new Error(`FIR Illuminate SpatialHitScene adapter: ${message}`, options);
}

function requireCondition(condition, message) {
  if (!condition) fail(message);
}

function u32(value) { return Number(value) >>> 0; }
function i32(value) { return Number(value) | 0; }
function align8(value) { return Math.ceil(value / 8) * 8; }
function defaultNow() { return globalThis.performance?.now?.() ?? Date.now(); }
function elapsed(now, start) {
  const result = now() - start;
  return Number.isFinite(result) && result >= 0 ? result : 0;
}
function errorMessage(error) {
  return error instanceof Error ? error.message : String(error);
}

function requireObject(value, label) {
  requireCondition(value !== null && typeof value === "object" &&
    !Array.isArray(value), `${label} must be an object`);
  return value;
}

function requireArray(value, label) {
  requireCondition(Array.isArray(value), `${label} must be an array`);
  return value;
}

function requireFloat(value, label) {
  requireCondition(typeof value === "number" && Number.isFinite(value),
    `${label} must be a finite binary64 number`);
  return value;
}

function requireBoolean(value, label) {
  requireCondition(typeof value === "boolean", `${label} must be a boolean`);
  return value;
}

function requireString(value, label) {
  requireCondition(typeof value === "string", `${label} must be a string`);
  return value;
}

function requireNatural(value, label) {
  requireCondition(Number.isSafeInteger(value) && value >= 0 &&
    value <= MAX_UINT32, `${label} must be a uint32 safe integer`);
  return BigInt(value);
}

function floatBits(value, label) {
  requireCondition(typeof value === "number", `${label} must be a number`);
  FLOAT_BITS.setFloat64(0, value, true);
  return FLOAT_BITS.getBigUint64(0, true);
}

function scalarBytes(floats, booleans = []) {
  const result = new Uint8Array(8 * floats.length + booleans.length);
  const view = new DataView(result.buffer);
  floats.forEach((value, index) =>
    view.setBigUint64(8 * index, floatBits(value, `Float ${index}`), true));
  booleans.forEach((value, index) => {
    requireCondition(typeof value === "boolean", "scalar Bool is invalid");
    result[8 * floats.length + index] = value ? 1 : 0;
  });
  return result;
}

function immediate(tag) {
  requireCondition(Number.isSafeInteger(tag) && tag >= 0 && tag <= 0x7fffffff,
    `constructor tag ${tag} is invalid`);
  return u32(2 * tag + 1);
}

function writeHeader(view, address, { kind, bytes, flags, aux0 = 0,
  aux1 = 0, aux2 = 0, aux3 = 0 }) {
  [kind, flags, 0, bytes, aux0, aux1, aux2, aux3].forEach((word, index) =>
    view.setUint32(address + 4 * index, u32(word), true));
}

function writeWord(view, address, value) {
  view.setUint32(address, u32(value), true);
  view.setUint32(address + 4, 0, true);
}

class Encoder {
  constructor(exports, memory, textEncoder, reservedFrontier,
    { persistent = true } = {}) {
    this.exports = exports;
    this.memory = memory;
    this.textEncoder = textEncoder;
    this.flags = persistent ? PERSISTENT_FLAGS : SCRATCH_FLAGS;
    this.bytes = 0;
    this.objects = 0;
    this.allocations = 0;
    this.reservedFrontier = reservedFrontier;
  }

  allocate(bytes, label) {
    requireCondition(bytes >= HEADER_BYTES && bytes % 8 === 0,
      `${label} has invalid allocation size`);
    const address = u32(this.exports.fir_heap_alloc(bytes));
    requireCondition(address >= this.reservedFrontier && address % 8 === 0 &&
      address + bytes <= this.memory.buffer.byteLength,
    `${label} returned invalid allocation ${address}`);
    new Uint8Array(this.memory.buffer, address, bytes).fill(0);
    this.bytes += bytes;
    this.objects += 1;
    this.allocations += 1;
    return address;
  }

  natural(value, label) {
    const natural = requireNatural(value, label);
    if (natural <= MAX_IMMEDIATE) return u32(Number(2n * natural + 1n));
    const address = this.allocate(40, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, { kind: KIND.natural, bytes: 40,
      flags: this.flags, aux0: 1, aux1: 1 });
    view.setBigUint64(address + HEADER_BYTES, natural, true);
    return address;
  }

  string(value, label) {
    const bytes = this.textEncoder.encode(requireString(value, label));
    const allocationBytes = align8(HEADER_BYTES + bytes.length);
    const address = this.allocate(allocationBytes, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, { kind: KIND.string, bytes: allocationBytes,
      flags: this.flags, aux0: STRING_MARKER, aux1: bytes.length });
    new Uint8Array(this.memory.buffer, address + HEADER_BYTES,
      bytes.length).set(bytes);
    return address;
  }

  ctor(tag, fields, scalars, label) {
    requireArray(fields, `${label} fields`);
    requireCondition(scalars instanceof Uint8Array,
      `${label} scalar payload must be bytes`);
    if (fields.length === 0 && scalars.length === 0) return immediate(tag);
    const bytes = align8(HEADER_BYTES + SLOT_BYTES * fields.length +
      scalars.length);
    const address = this.allocate(bytes, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, { kind: KIND.constructor, bytes,
      flags: this.flags, aux0: tag, aux1: fields.length,
      aux3: scalars.length });
    fields.forEach((field, index) =>
      writeWord(view, address + HEADER_BYTES + SLOT_BYTES * index, field));
    new Uint8Array(this.memory.buffer,
      address + HEADER_BYTES + SLOT_BYTES * fields.length,
      scalars.length).set(scalars);
    return address;
  }

  array(values, label) {
    requireArray(values, label);
    const bytes = align8(HEADER_BYTES + SLOT_BYTES * values.length);
    const address = this.allocate(bytes, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, { kind: KIND.opaque, bytes,
      flags: this.flags, aux0: ARRAY_MARKER, aux1: values.length,
      aux2: values.length });
    values.forEach((value, index) =>
      writeWord(view, address + HEADER_BYTES + SLOT_BYTES * index, value));
    return address;
  }

  vec(value, label) {
    requireObject(value, label);
    return this.ctor(0, [], scalarBytes([
      requireFloat(value.x, `${label}.x`),
      requireFloat(value.y, `${label}.y`),
    ]), label);
  }

  matrix(value, label) {
    requireObject(value, label);
    return this.ctor(0, [], scalarBytes([
      requireFloat(value.a, `${label}.a`),
      requireFloat(value.b, `${label}.b`),
      requireFloat(value.tx, `${label}.tx`),
      requireFloat(value.c, `${label}.c`),
      requireFloat(value.d, `${label}.d`),
      requireFloat(value.ty, `${label}.ty`),
    ]), label);
  }

  pathCommand(command, label) {
    requireObject(command, label);
    switch (command.kind) {
      case "moveTo":
        return this.ctor(0, [this.vec(command.point, `${label}.point`)],
          new Uint8Array(0), label);
      case "lineTo":
        return this.ctor(1, [this.vec(command.point, `${label}.point`)],
          new Uint8Array(0), label);
      case "curveTo":
        return this.ctor(2, [
          this.vec(command.control1, `${label}.control1`),
          this.vec(command.control2, `${label}.control2`),
          this.vec(command.endpoint, `${label}.endpoint`),
        ], new Uint8Array(0), label);
      case "arcTo":
        return this.ctor(3, [this.vec(command.endpoint, `${label}.endpoint`)],
          scalarBytes([
            requireFloat(command.rx, `${label}.rx`),
            requireFloat(command.ry, `${label}.ry`),
            requireFloat(command.rotation, `${label}.rotation`),
          ], [
            requireBoolean(command.largeArc, `${label}.largeArc`),
            requireBoolean(command.sweep, `${label}.sweep`),
          ]), label);
      case "closePath": return immediate(4);
      default: fail(`${label}.kind ${String(command.kind)} is unsupported`);
    }
  }

  pathData(commands, label) {
    const values = requireArray(commands, label).map((command, index) =>
      this.pathCommand(command, `${label}[${index}]`));
    // Lean erases PathData's single-field structure wrapper in final LCNF.
    return this.array(values, `${label}.commands`);
  }

  primitive(value, label) {
    requireObject(value, label);
    switch (value.kind) {
      case "path":
        return this.ctor(0, [this.pathData(value.data, `${label}.data`)],
          scalarBytes([
            requireFloat(value.strokeWidth, `${label}.strokeWidth`),
            requireFloat(value.left, `${label}.left`),
            requireFloat(value.right, `${label}.right`),
            requireFloat(value.bottom, `${label}.bottom`),
            requireFloat(value.top, `${label}.top`),
          ], [requireBoolean(value.hasFill, `${label}.hasFill`)]), label);
      case "bounds":
        return this.ctor(1, [], scalarBytes([
          requireFloat(value.left, `${label}.left`),
          requireFloat(value.right, `${label}.right`),
          requireFloat(value.bottom, `${label}.bottom`),
          requireFloat(value.top, `${label}.top`),
        ]), label);
      default: fail(`${label}.kind ${String(value.kind)} is unsupported`);
    }
  }

  tree(value, label, budget) {
    requireCondition(budget.remaining-- > 0,
      `scene exceeds the ${budget.maximum} node limit`);
    requireObject(value, label);
    switch (value.kind) {
      case "empty": return immediate(0);
      case "primitive":
        return this.ctor(1, [this.primitive(value.value, `${label}.value`)],
          new Uint8Array(0), label);
      case "tag":
        return this.ctor(2, [
          this.natural(value.value, `${label}.value`),
          this.tree(value.child, `${label}.child`, budget),
        ], new Uint8Array(0), label);
      case "transform":
        return this.ctor(3, [
          this.matrix(value.inverse, `${label}.inverse`),
          this.tree(value.child, `${label}.child`, budget),
        ], new Uint8Array(0), label);
      case "compose":
        return this.ctor(4, [
          this.tree(value.back, `${label}.back`, budget),
          this.tree(value.front, `${label}.front`, budget),
        ], new Uint8Array(0), label);
      case "clip":
        return this.ctor(5, [
          this.pathData(value.boundary, `${label}.boundary`),
          this.tree(value.child, `${label}.child`, budget),
        ], new Uint8Array(0), label);
      default: fail(`${label}.kind ${String(value.kind)} is unsupported`);
    }
  }

  scene(value, maximumNodes) {
    requireObject(value, "scene");
    const labels = requireArray(value.labels, "scene.labels").map(
      (entry, index) => {
        const label = `scene.labels[${index}]`;
        requireObject(entry, label);
        return this.ctor(0, [
          this.natural(entry.value, `${label}.value`),
          this.string(entry.label, `${label}.label`),
        ], new Uint8Array(0), label);
      });
    const budget = { maximum: maximumNodes, remaining: maximumNodes };
    const tree = this.tree(value.tree, "scene.tree", budget);
    return this.ctor(0, [tree, this.array(labels, "scene.labels")],
      new Uint8Array(0), "scene");
  }
}

function classify(word) {
  const value = u32(word);
  if (value === 0) return "sentinel";
  if ((value & 1) === 1) return "immediate";
  if ((value & 7) === 0) return "heap";
  return "invalid";
}

function readU32(view, address, label) {
  requireCondition(Number.isInteger(address) && address >= 0 &&
    address + 4 <= view.byteLength, `${label} is outside module memory`);
  return view.getUint32(address, true);
}

function readHeader(view, word, label) {
  const address = u32(word);
  requireCondition(classify(address) === "heap",
    `${label} has invalid address ${address}`);
  const flags = readU32(view, address + 4, label);
  const header = {
    address,
    kind: readU32(view, address, label),
    live: (flags & 2) !== 0,
    bytes: readU32(view, address + 12, label),
    aux0: readU32(view, address + 16, label),
    aux1: readU32(view, address + 20, label),
    aux2: readU32(view, address + 24, label),
    aux3: readU32(view, address + 28, label),
  };
  requireCondition(header.live && header.bytes >= HEADER_BYTES &&
    header.bytes % 8 === 0 && address + header.bytes <= view.byteLength,
  `${label} has an invalid live allocation`);
  return header;
}

function readWord(view, address, label) {
  const result = readU32(view, address, label);
  requireCondition(readU32(view, address + 4, label) === 0,
    `${label} has nonzero slot padding`);
  return result;
}

function readNatural(view, word, label) {
  if (classify(word) === "immediate") return BigInt(u32(word) >>> 1);
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.natural && header.aux1 === 1 &&
    header.bytes >= 40, `${label} is not a one-limb Natural`);
  return view.getBigUint64(header.address + HEADER_BYTES, true);
}

function numberNatural(view, word, label) {
  const value = readNatural(view, word, label);
  requireCondition(value <= BigInt(Number.MAX_SAFE_INTEGER),
    `${label} exceeds JavaScript's safe integer range`);
  return Number(value);
}

function readString(view, word, decoder, label) {
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.string && header.aux0 === STRING_MARKER &&
    header.aux2 === 0 && header.aux3 === 0 &&
    HEADER_BYTES + header.aux1 <= header.bytes,
  `${label} is not a canonical UTF-8 String`);
  return decoder.decode(new Uint8Array(view.buffer,
    header.address + HEADER_BYTES, header.aux1));
}

function decodeResult(memory, decoder, word) {
  if (classify(word) === "immediate") {
    const tag = u32(word) >>> 1;
    if (tag === 0) return { kind: "nothing" };
    if (tag === 1) return { kind: "something" };
    fail(`result has unknown nullary tag ${tag}`);
  }
  const view = new DataView(memory.buffer);
  const header = readHeader(view, word, "HitSceneResult");
  requireCondition(header.kind === KIND.constructor && header.aux0 === 2 &&
    header.aux1 === 2 && header.aux2 === 0 && header.aux3 === 0,
  "result is not HitSceneResult.tag");
  const value = readWord(view, header.address + HEADER_BYTES,
    "HitSceneResult.tag.value");
  const label = readWord(view, header.address + HEADER_BYTES + SLOT_BYTES,
    "HitSceneResult.tag.label");
  return {
    kind: "tag",
    value: numberNatural(view, value, "HitSceneResult.tag.value"),
    label: readString(view, label, decoder, "HitSceneResult.tag.label"),
  };
}

function readFrontier(state) {
  const frontier = u32(state.frontier());
  requireCondition(frontier >= state.reservedFrontier && frontier % 8 === 0 &&
    frontier <= state.memory.buffer.byteLength,
  `resident frontier ${frontier} is invalid`);
  return frontier;
}

function rewind(state, checkpoint) {
  const before = readFrontier(state);
  requireCondition(before >= checkpoint, "frontier moved below checkpoint");
  const clearedBytes = before - checkpoint;
  new Uint8Array(state.memory.buffer, checkpoint, clearedBytes).fill(0);
  state.rewind(checkpoint);
  const after = readFrontier(state);
  requireCondition(after === checkpoint,
    `frontier rewound to ${after}, expected ${checkpoint}`);
  return { frontierBeforeRewind: before, clearedBytes,
    postRewindFrontier: after };
}

function instantiate(module, reservedFrontier) {
  const instance = new WebAssembly.Instance(module, {});
  const exports = instance.exports;
  const required = [
    "Illuminate.SpatialHitScene.ofHitScene",
    "IlluminateFirSpatialHitScene.queryBorrowed._fir_bit_exact",
    "fir_heap_frontier",
    "fir_heap_set_frontier",
    "fir_heap_rewind",
    "fir_heap_alloc",
  ];
  requireCondition(exports.memory instanceof WebAssembly.Memory,
    "module does not export memory");
  for (const name of required) {
    requireCondition(typeof exports[name] === "function",
      `module is missing export ${name}`);
  }
  const freshFrontier = u32(exports.fir_heap_frontier());
  requireCondition(freshFrontier >= HEAP_BASE && freshFrontier % 8 === 0 &&
    freshFrontier <= reservedFrontier,
  "fresh instance frontier overlaps the external runtime reservation");
  requireCondition(reservedFrontier <= exports.memory.buffer.byteLength,
    "external runtime reservation exceeds module memory");
  if (freshFrontier !== reservedFrontier) {
    exports.fir_heap_set_frontier(reservedFrontier);
  }
  return {
    instance,
    exports,
    memory: exports.memory,
    frontier: exports.fir_heap_frontier,
    rewind: exports.fir_heap_rewind,
    prepare: exports["Illuminate.SpatialHitScene.ofHitScene"],
    queryBits: exports["IlluminateFirSpatialHitScene.queryBorrowed._fir_bit_exact"],
    decoder: new TextDecoder("utf-8", { fatal: true }),
    reservedFrontier,
  };
}

function invalidate(state, status) {
  state.status = status;
  state.instance = undefined;
  state.exports = undefined;
  state.memory = undefined;
  state.frontier = undefined;
  state.rewind = undefined;
  state.prepare = undefined;
  state.queryBits = undefined;
  state.sceneAddress = 0;
  state.checkpoint = 0;
}

function requireScene(adapter, scene) {
  const state = SCENE_STATE.get(scene);
  requireCondition(scene?.[SCENE] === adapter && state?.owner === adapter,
    "scene handle belongs to another adapter");
  requireCondition(state.status === "active",
    `scene is ${state.status ?? "invalid"}`);
  return state;
}

function queryCore(adapter, scene, x, y, diagnostic) {
  const state = requireScene(adapter, scene);
  const now = ADAPTER_STATE.get(adapter).now;
  const totalStarted = diagnostic ? now() : 0;
  const timings = { inputMs: 0, executeMs: 0, decodeMs: 0, rewindMs: 0 };
  const memory = { persistentCheckpoint: state.checkpoint,
    frontierBefore: readFrontier(state), frontierAfterExecute: undefined,
    peakFrontier: undefined, frontierBeforeRewind: undefined,
    clearedBytes: 0, postRewindFrontier: undefined };
  requireCondition(memory.frontierBefore === state.checkpoint,
    "query did not begin at the persistent checkpoint");
  let result;
  let failure;
  let phase = "input";
  try {
    const inputStarted = diagnostic ? now() : 0;
    const xBits = floatBits(x, "x");
    const yBits = floatBits(y, "y");
    if (diagnostic) timings.inputMs = elapsed(now, inputStarted);
    phase = "execute";
    const executeStarted = diagnostic ? now() : 0;
    const word = u32(state.queryBits(i32(state.sceneAddress), xBits, yBits));
    if (diagnostic) timings.executeMs = elapsed(now, executeStarted);
    memory.frontierAfterExecute = readFrontier(state);
    memory.peakFrontier = memory.frontierAfterExecute;
    phase = "decode";
    const decodeStarted = diagnostic ? now() : 0;
    result = decodeResult(state.memory, state.decoder, word);
    if (diagnostic) timings.decodeMs = elapsed(now, decodeStarted);
    phase = "done";
  } catch (error) {
    failure = error;
    if (phase === "execute" || phase === "decode") state.status = "poisoned";
  } finally {
    try {
      const rewindStarted = diagnostic ? now() : 0;
      Object.assign(memory, rewind(state, state.checkpoint));
      if (diagnostic) timings.rewindMs = elapsed(now, rewindStarted);
    } catch (error) {
      failure = error;
      state.status = "poisoned";
    }
  }
  if (failure !== undefined) {
    if (state.status === "poisoned") invalidate(state, "poisoned");
    fail(errorMessage(failure), { cause: failure });
  }
  if (!diagnostic) return result;
  const totalMs = elapsed(now, totalStarted);
  const measured = Object.values(timings).reduce((sum, value) => sum + value, 0);
  return { result, timings: Object.freeze({ ...timings, totalMs,
    overheadMs: totalMs - measured }), memory: Object.freeze(memory) };
}

export class IlluminateSpatialHitSceneAdapter {
  constructor(module, build, now, maximumNodes, startupTimings,
    reservedFrontier) {
    this.build = build;
    this.startupTimings = Object.freeze(startupTimings);
    ADAPTER_STATE.set(this, { module, now, maximumNodes, reservedFrontier });
  }

  createHitScene(encodedScene) {
    const adapter = ADAPTER_STATE.get(this);
    requireCondition(adapter !== undefined, "invalid adapter receiver");
    requireCondition(typeof encodedScene === "string",
      "createHitScene expects the canonical encoded scene string");
    const totalStarted = adapter.now();
    const timings = {
      instantiateMs: 0,
      parseProjectMs: 0,
      encodeMs: 0,
      prepareMs: 0,
    };
    const instantiateStarted = adapter.now();
    const state = instantiate(adapter.module, adapter.reservedFrontier);
    timings.instantiateMs = elapsed(adapter.now, instantiateStarted);
    const parseStarted = adapter.now();
    const projected = JSON.parse(encodedScene);
    timings.parseProjectMs = elapsed(adapter.now, parseStarted);
    const writer = new Encoder(state.exports, state.memory, new TextEncoder(),
      adapter.reservedFrontier, { persistent: true });
    const encodeStarted = adapter.now();
    const sourceAddress = writer.scene(projected, adapter.maximumNodes);
    timings.encodeMs = elapsed(adapter.now, encodeStarted);
    const encodedFrontier = readFrontier(state);
    const prepareStarted = adapter.now();
    const sceneAddress = u32(state.prepare(i32(sourceAddress)));
    timings.prepareMs = elapsed(adapter.now, prepareStarted);
    requireCondition(classify(sceneAddress) === "heap",
      "spatial preparation did not return a heap object");
    const preparedHeader = readHeader(new DataView(state.memory.buffer),
      sceneAddress, "SpatialHitScene");
    requireCondition(preparedHeader.kind === KIND.constructor &&
      preparedHeader.aux0 === 0 && preparedHeader.aux1 === 2,
    "spatial preparation returned an invalid SpatialHitScene");
    const checkpoint = readFrontier(state);
    state.sceneAddress = sceneAddress;
    state.checkpoint = checkpoint;
    state.status = "active";
    state.owner = this;
    const scene = Object.freeze({ [SCENE]: this });
    SCENE_STATE.set(scene, state);
    const totalMs = elapsed(adapter.now, totalStarted);
    const measured = Object.values(timings).reduce((sum, value) => sum + value, 0);
    return {
      scene,
      timings: Object.freeze({ ...timings, totalMs,
        overheadMs: totalMs - measured }),
      memory: Object.freeze({
        reservedFrontier: adapter.reservedFrontier,
        persistentCheckpoint: checkpoint,
        encodedBytes: writer.bytes,
        encodedFrontier,
        preparationBytes: checkpoint - encodedFrontier,
        persistentBytes: checkpoint - adapter.reservedFrontier,
        encodedObjects: writer.objects,
        allocationCalls: writer.allocations,
        pages: state.memory.buffer.byteLength / PAGE_BYTES,
      }),
    };
  }

  hitTest(scene, x, y) {
    return queryCore(this, scene, x, y, false);
  }

  hitTestDiagnostic(scene, x, y) {
    return queryCore(this, scene, x, y, true);
  }

  disposeHitScene(scene) {
    const state = SCENE_STATE.get(scene);
    requireCondition(scene?.[SCENE] === this && state?.owner === this,
      "disposeHitScene requires this adapter's scene handle");
    if (state.status === "disposed") return;
    invalidate(state, "disposed");
  }
}

function validateBuild(build) {
  requireObject(build, "BUILD.json");
  requireCondition(build.capabilities?.browserAdapter?.apiVersion ===
    ILLUMINATE_SPATIAL_HIT_SCENE_ADAPTER_API_VERSION,
  "BUILD.json has the wrong adapter API version");
  requireCondition(build.capabilities?.inputLayout?.version ===
    ILLUMINATE_SPATIAL_HIT_SCENE_INPUT_LAYOUT_VERSION,
  "BUILD.json has the wrong input-layout version");
  requireCondition(build.capabilities?.ownership?.version ===
    ILLUMINATE_SPATIAL_HIT_SCENE_OWNERSHIP_VERSION,
  "BUILD.json has the wrong ownership version");
  const runtime = requireObject(
    build.capabilities?.completeRuntime?.externalRuntime,
    "BUILD.json complete-runtime externalRuntime");
  requireCondition(Number.isSafeInteger(runtime.reservedMemoryBytes) &&
    runtime.reservedMemoryBytes >= HEAP_BASE &&
    runtime.reservedMemoryBytes <= MAX_UINT32 &&
    runtime.reservedMemoryBytes % 8 === 0,
  "external-runtime reservedMemoryBytes is invalid");
  return runtime.reservedMemoryBytes;
}

export async function createIlluminateSpatialHitSceneAdapter({
  bytes,
  build,
  now = defaultNow,
  maximumNodes = 1_000_000,
}) {
  requireCondition(bytes instanceof ArrayBuffer || ArrayBuffer.isView(bytes),
    "bytes must be an ArrayBuffer or view");
  requireCondition(typeof now === "function", "now must be a function");
  requireCondition(Number.isSafeInteger(maximumNodes) && maximumNodes > 0,
    "maximumNodes must be a positive safe integer");
  const reservedFrontier = validateBuild(build);
  const started = now();
  const module = await WebAssembly.compile(bytes);
  const compileMs = elapsed(now, started);
  requireCondition(WebAssembly.Module.imports(module).length === 0,
    "complete runtime module has imports");
  return new IlluminateSpatialHitSceneAdapter(module, build, now, maximumNodes,
    { fetchMs: 0, compileMs, totalMs: compileMs }, reservedFrontier);
}

function baseUrl() { return globalThis.location?.href ?? "file:///"; }

export async function fetchIlluminateSpatialHitSceneAdapter(artifactUrl, {
  fetchImpl = globalThis.fetch,
  buildUrl,
  now = defaultNow,
  maximumNodes = 1_000_000,
} = {}) {
  requireCondition(typeof fetchImpl === "function",
    "fetchIlluminateSpatialHitSceneAdapter requires fetch");
  const wasmUrl = new URL(artifactUrl, baseUrl());
  const metadataUrl = buildUrl === undefined
    ? new URL("BUILD.json", wasmUrl)
    : new URL(buildUrl, baseUrl());
  const started = now();
  const [wasmResponse, buildResponse] = await Promise.all([
    fetchImpl(wasmUrl), fetchImpl(metadataUrl),
  ]);
  requireCondition(wasmResponse.ok, `failed to fetch ${wasmUrl}`);
  requireCondition(buildResponse.ok, `failed to fetch ${metadataUrl}`);
  const [bytes, build] = await Promise.all([
    wasmResponse.arrayBuffer(), buildResponse.json(),
  ]);
  const fetchMs = elapsed(now, started);
  const adapter = await createIlluminateSpatialHitSceneAdapter({
    bytes, build, now, maximumNodes,
  });
  adapter.startupTimings = Object.freeze({
    fetchMs,
    compileMs: adapter.startupTimings.compileMs,
    totalMs: fetchMs + adapter.startupTimings.compileMs,
  });
  return adapter;
}
