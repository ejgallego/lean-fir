/** Browser/Node adapter for the FIR-native Illuminate trace player. */

export const ILLUMINATE_PLAYER_ADAPTER_API_VERSION =
  "fir.illuminate-player.browser/v2";
export const ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION =
  "lean-4.32-Illuminate.Animation.PlayerAnimation/v2";
export const ILLUMINATE_PLAYER_OWNERSHIP_VERSION =
  "fir.illuminate-player.module-owned-arena/v1";

const PAGE_BYTES = 65536;
const HEAP_BASE = 1024;
const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const MAX_UINT32 = 0xffffffff;
const MAX_IMMEDIATE = 0x7fffffffn;
const ARRAY_MARKER = 0x41525259;
const STRING_MARKER = 1;
const PERSISTENT_LIVE_FLAGS = 3;

const KIND = Object.freeze({
  constructor: 1,
  boxed: 3,
  string: 4,
  natural: 5,
  opaque: 8,
});

const PREPARED = Symbol("fir.illuminate-player.prepared");
const EXECUTED = Symbol("fir.illuminate-player.executed");
const ADAPTER_STATE = new WeakMap();
const PREPARED_STATE = new WeakMap();
const EXECUTED_STATE = new WeakMap();

function fail(message) {
  throw new Error(`FIR Illuminate player adapter: ${message}`);
}

function requireCondition(condition, message) {
  if (!condition) fail(message);
}

function u32(value) {
  return Number(value) >>> 0;
}

function i32(value) {
  return Number(value) | 0;
}

function align8(value) {
  return Math.ceil(value / 8) * 8;
}

function defaultNow() {
  return globalThis.performance?.now?.() ?? Date.now();
}

function elapsed(now, started) {
  const value = now() - started;
  return Number.isFinite(value) && value >= 0 ? value : 0;
}

function requireObject(value, label) {
  requireCondition(value !== null && typeof value === "object" &&
    !Array.isArray(value), `${label} must be an object`);
  return value;
}

function natural(value, label) {
  requireCondition(Number.isSafeInteger(value) && value >= 0 &&
    value <= MAX_UINT32, `${label} must be a uint32 safe integer`);
  return BigInt(value);
}

function boolean(value, label) {
  requireCondition(typeof value === "boolean", `${label} must be a boolean`);
  return value;
}

function string(value, label) {
  requireCondition(typeof value === "string", `${label} must be a string`);
  return value;
}

function projectNatural(value, label) {
  natural(value, label);
  return value;
}

function projectAnimation(animation) {
  requireObject(animation, "animation");
  requireCondition(Array.isArray(animation.segments),
    "animation.segments must be an array");
  requireCondition(Array.isArray(animation.steps),
    "animation.steps must be an array");
  return {
    fps: projectNatural(animation.fps, "animation.fps"),
    totalFrames: projectNatural(animation.totalFrames, "animation.totalFrames"),
    segments: animation.segments.map((segment, segmentIndex) => {
      const label = `animation.segments[${segmentIndex}]`;
      requireObject(segment, label);
      requireCondition(Array.isArray(segment.pmap), `${label}.pmap must be an array`);
      requireCondition(Array.isArray(segment.params), `${label}.params must be an array`);
      return {
        startFrame: projectNatural(segment.sf, `${label}.sf`),
        frameCount: projectNatural(segment.fc, `${label}.fc`),
        paramMap: segment.pmap.map((binding, bindingIndex) => {
          const bindingLabel = `${label}.pmap[${bindingIndex}]`;
          requireObject(binding, bindingLabel);
          const name = string(binding.a, `${bindingLabel}.a`);
          return {
            element: projectNatural(binding.e, `${bindingLabel}.e`),
            target: name === "textContent"
              ? { kind: "textContent" }
              : { kind: "attribute", name },
          };
        }),
        params: segment.params.map((row, rowIndex) => {
          const rowLabel = `${label}.params[${rowIndex}]`;
          requireCondition(Array.isArray(row), `${rowLabel} must be an array`);
          return row.map((value, valueIndex) =>
            string(value, `${rowLabel}[${valueIndex}]`));
        }),
      };
    }),
    steps: animation.steps.map((step, stepIndex) => {
      const label = `animation.steps[${stepIndex}]`;
      requireObject(step, label);
      return {
        frame: projectNatural(step.frame, `${label}.frame`),
        pause: boolean(step.pause, `${label}.pause`),
        loop: boolean(step.loop, `${label}.loop`),
      };
    }),
  };
}

function writeHeader(view, address, {
  kind,
  bytes,
  aux0 = 0,
  aux1 = 0,
  aux2 = 0,
  aux3 = 0,
}) {
  const words = [kind, PERSISTENT_LIVE_FLAGS, 0, bytes,
    aux0, aux1, aux2, aux3];
  words.forEach((word, index) =>
    view.setUint32(address + 4 * index, u32(word), true));
}

function writeWord(view, address, value) {
  view.setUint32(address, u32(value), true);
  view.setUint32(address + 4, 0, true);
}

function immediate(tag) {
  requireCondition(Number.isSafeInteger(tag) && tag >= 0 && tag <= 0x7fffffff,
    `immediate constructor tag ${tag} is invalid`);
  return u32(2 * tag + 1);
}

class Encoder {
  constructor(exports, memory, encoder) {
    this.exports = exports;
    this.memory = memory;
    this.encoder = encoder;
    this.allocations = 0;
    this.bytes = 0;
  }

  allocate(bytes, label) {
    requireCondition(Number.isSafeInteger(bytes) && bytes >= HEADER_BYTES &&
      bytes % 8 === 0, `${label} allocation size is invalid`);
    const address = u32(this.exports.fir_heap_alloc(bytes));
    requireCondition(address >= HEAP_BASE && address % 8 === 0,
      `${label} allocation returned invalid address ${address}`);
    requireCondition(address + bytes <= this.memory.buffer.byteLength,
      `${label} allocation exceeds module memory`);
    new Uint8Array(this.memory.buffer, address, bytes).fill(0);
    this.allocations += 1;
    this.bytes += bytes;
    return address;
  }

  natural(value, label) {
    const n = natural(value, label);
    return this.naturalValue(n, label);
  }

  naturalProjected(value, label) {
    return this.naturalValue(BigInt(value), label);
  }

  naturalValue(n, label) {
    if (n <= MAX_IMMEDIATE) return Number(n * 2n + 1n) >>> 0;
    const address = this.allocate(40, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, {
      kind: KIND.natural,
      bytes: 40,
      aux0: 1,
      aux1: 1,
    });
    view.setBigUint64(address + HEADER_BYTES, n, true);
    return address;
  }

  string(value, label) {
    const bytes = this.encoder.encode(string(value, label));
    const allocationBytes = align8(HEADER_BYTES + bytes.length);
    const address = this.allocate(allocationBytes, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, {
      kind: KIND.string,
      bytes: allocationBytes,
      aux0: STRING_MARKER,
      aux1: bytes.length,
    });
    new Uint8Array(this.memory.buffer, address + HEADER_BYTES,
      bytes.length).set(bytes);
    return address;
  }

  ctor(tag, fields, scalarBytes, label) {
    requireCondition(Array.isArray(fields), `${label} fields must be an array`);
    requireCondition(scalarBytes instanceof Uint8Array,
      `${label} scalar payload must be bytes`);
    if (fields.length === 0 && scalarBytes.length === 0) return immediate(tag);
    const bytes = align8(HEADER_BYTES + SLOT_BYTES * fields.length +
      scalarBytes.length);
    const address = this.allocate(bytes, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, {
      kind: KIND.constructor,
      bytes,
      aux0: tag,
      aux1: fields.length,
      aux3: scalarBytes.length,
    });
    fields.forEach((field, index) =>
      writeWord(view, address + HEADER_BYTES + SLOT_BYTES * index, field));
    new Uint8Array(this.memory.buffer,
      address + HEADER_BYTES + SLOT_BYTES * fields.length,
      scalarBytes.length).set(scalarBytes);
    return address;
  }

  array(values, label) {
    requireCondition(Array.isArray(values), `${label} must be an array`);
    const bytes = align8(HEADER_BYTES + SLOT_BYTES * values.length);
    const address = this.allocate(bytes, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, {
      kind: KIND.opaque,
      bytes,
      aux0: ARRAY_MARKER,
      aux1: values.length,
      aux2: values.length,
    });
    values.forEach((value, index) =>
      writeWord(view, address + HEADER_BYTES + SLOT_BYTES * index, value));
    return address;
  }

  paramBinding(binding, label) {
    const target = binding.target.kind === "textContent"
      ? immediate(0)
      : this.ctor(1, [this.string(binding.target.name,
        `${label}.target.name`)], new Uint8Array(0), `${label}.target`);
    return this.ctor(0, [
      this.naturalProjected(binding.element, `${label}.element`),
      target,
    ], new Uint8Array(0), label);
  }

  segment(segment, label) {
    const map = segment.paramMap;
    const params = segment.params;
    const mapWord = this.array(map.map((binding, index) =>
      this.paramBinding(binding, `${label}.paramMap[${index}]`)),
    `${label}.paramMap`);
    const paramsWord = this.array(params.map((row, rowIndex) => {
      return this.array(row.map((value, index) =>
        this.string(value, `${label}.params[${rowIndex}][${index}]`)),
      `${label}.params[${rowIndex}]`);
    }), `${label}.params`);
    return this.ctor(0, [
      this.naturalProjected(segment.startFrame, `${label}.startFrame`),
      this.naturalProjected(segment.frameCount, `${label}.frameCount`),
      mapWord,
      paramsWord,
    ], new Uint8Array(0), label);
  }

  step(step, label) {
    return this.ctor(0, [this.naturalProjected(step.frame, `${label}.frame`)],
      Uint8Array.of(
        step.pause ? 1 : 0,
        step.loop ? 1 : 0), label);
  }

  animation(animation) {
    const segments = this.array(animation.segments.map((segment, index) =>
      this.segment(segment, `animation.segments[${index}]`)),
    "animation.segments");
    const steps = this.array(animation.steps.map((step, index) =>
      this.step(step, `animation.steps[${index}]`)), "animation.steps");
    return this.ctor(0, [
      this.naturalProjected(animation.fps, "animation.fps"),
      this.naturalProjected(animation.totalFrames, "animation.totalFrames"),
      segments,
      steps,
    ], new Uint8Array(0), "animation");
  }

  event(event, label) {
    requireObject(event, label);
    switch (event.kind) {
      case "advance": return immediate(0);
      case "pause": return immediate(1);
      case "seek":
        return this.ctor(2, [this.natural(event.frame,
          `${label}.frame`)], new Uint8Array(0), label);
      case "playTo":
        return this.ctor(3, [this.natural(event.frame,
          `${label}.frame`)], Uint8Array.of(
          boolean(event.loopAfter, `${label}.loopAfter`) ? 1 : 0), label);
      case "loopAt":
        return this.ctor(4, [this.natural(event.frame,
          `${label}.frame`)], new Uint8Array(0), label);
      case "tick": {
        requireCondition(typeof event.timestamp === "number" &&
          Number.isFinite(event.timestamp), `${label}.timestamp must be finite`);
        const bytes = new Uint8Array(8);
        new DataView(bytes.buffer).setFloat64(0, event.timestamp, true);
        return this.ctor(5, [], bytes, label);
      }
      default: fail(`${label}.kind ${String(event.kind)} is unsupported`);
    }
  }

  eventList(events) {
    requireCondition(Array.isArray(events), "events must be an array");
    let tail = immediate(0);
    for (let index = events.length - 1; index >= 0; --index) {
      const event = this.event(events[index], `events[${index}]`);
      tail = this.ctor(1, [event, tail], new Uint8Array(0),
        `events list node ${index}`);
    }
    return tail;
  }
}

function readU32(view, address, label) {
  requireCondition(Number.isInteger(address) && address >= 0 &&
    address + 4 <= view.byteLength, `${label} is outside module memory`);
  return view.getUint32(address, true);
}

function classify(word) {
  const value = u32(word);
  if (value === 0) return "sentinel";
  if ((value & 1) === 1) return "immediate";
  if ((value & 7) === 0) return "heap";
  return "invalid";
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

function readConstructor(view, word, tag, fields, scalarBytes, label) {
  if (fields === 0 && scalarBytes === 0) {
    requireCondition(classify(word) === "immediate" && (u32(word) >>> 1) === tag,
      `${label} is not immediate constructor ${tag}`);
    return { fields: [], scalarAddress: 0 };
  }
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.constructor && header.aux0 === tag &&
    header.aux1 === fields && header.aux2 === 0 && header.aux3 === scalarBytes,
  `${label} has an unexpected constructor layout`);
  return {
    fields: Array.from({ length: fields }, (_, index) =>
      readWord(view, header.address + HEADER_BYTES + SLOT_BYTES * index,
        `${label} field ${index}`)),
    scalarAddress: header.address + HEADER_BYTES + SLOT_BYTES * fields,
  };
}

function readNatural(view, word, label) {
  if (classify(word) === "immediate") return BigInt(u32(word) >>> 1);
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.natural && header.aux1 > 0,
    `${label} is not a Natural`);
  let value = 0n;
  for (let index = header.aux1 - 1; index >= 0; --index) {
    value = (value << 64n) + view.getBigUint64(
      header.address + HEADER_BYTES + SLOT_BYTES * index, true);
  }
  return value;
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

function readArray(view, word, label, maximumNodes) {
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.opaque && header.aux0 === ARRAY_MARKER &&
    header.aux1 <= maximumNodes && header.aux2 >= header.aux1 &&
    HEADER_BYTES + SLOT_BYTES * header.aux1 <= header.bytes,
  `${label} is not a resident Array`);
  return Array.from({ length: header.aux1 }, (_, index) =>
    readWord(view, header.address + HEADER_BYTES + SLOT_BYTES * index,
      `${label}[${index}]`));
}

const PLAYBACK = ["paused", "playing", "waiting", "looping",
  "finishingLoop", "finished"];

function decodePatchTarget(view, word, decoder, label) {
  if (classify(word) === "immediate") {
    requireCondition((u32(word) >>> 1) === 0,
      `${label} has invalid immediate tag`);
    return "textContent";
  }
  const { fields } = readConstructor(view, word, 1, 1, 0, label);
  return readString(view, fields[0], decoder, `${label}.attribute`);
}

function decodeUpdate(view, word, decoder, label) {
  const { fields } = readConstructor(view, word, 0, 3, 0, label);
  return {
    e: numberNatural(view, fields[0], `${label}.element`),
    a: decodePatchTarget(view, fields[1], decoder, `${label}.target`),
    v: readString(view, fields[2], decoder, `${label}.value`),
  };
}

function decodeAction(view, word, decoder, maximumNodes, label) {
  const { fields, scalarAddress } =
    readConstructor(view, word, 0, 5, 2, label);
  const playback = view.getUint8(scalarAddress + 1);
  requireCondition(playback < PLAYBACK.length,
    `${label}.playback tag ${playback} is invalid`);
  return {
    frame: numberNatural(view, fields[0], `${label}.frame`),
    step: numberNatural(view, fields[1], `${label}.step`),
    segment: numberNatural(view, fields[2], `${label}.segment`),
    localFrame: numberNatural(view, fields[3], `${label}.localFrame`),
    segmentChanged: view.getUint8(scalarAddress) !== 0,
    updates: readArray(view, fields[4], `${label}.updates`, maximumNodes)
      .map((update, index) =>
        decodeUpdate(view, update, decoder, `${label}.updates[${index}]`)),
    playback: PLAYBACK[playback],
  };
}

function validateManifest(manifest) {
  requireObject(manifest, "module descriptor");
  requireCondition(manifest.entry ===
    "Illuminate.AnimationPlayer.replayTrace",
  "module descriptor has the wrong entry");
  requireCondition(JSON.stringify(manifest.params) ===
    JSON.stringify(["object", "tobject"]) && manifest.result === "object",
  "module descriptor has the wrong structured ABI");
  requireCondition(Array.isArray(manifest.imports) && manifest.imports.length === 0,
    "complete runtime package must have zero imports");
}

function validateBuild(build) {
  requireObject(build, "BUILD.json");
  requireCondition(build.capabilities?.browserAdapter?.apiVersion ===
    ILLUMINATE_PLAYER_ADAPTER_API_VERSION,
  "BUILD.json has the wrong adapter API version");
  requireCondition(build.capabilities?.inputLayout?.version ===
    ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION,
  "BUILD.json has the wrong input-layout version");
  requireCondition(build.capabilities?.ownership?.version ===
    ILLUMINATE_PLAYER_OWNERSHIP_VERSION,
  "BUILD.json has the wrong ownership version");
}

export class IlluminatePlayerAdapter {
  constructor({ instance, manifest, build, now, startupTimings, maximumNodes }) {
    this.manifest = manifest;
    this.build = build;
    this.startupTimings = Object.freeze({ ...startupTimings });
    const memory = instance.exports.memory;
    requireCondition(memory instanceof WebAssembly.Memory,
      "module does not export its memory");
    for (const name of ["fir_heap_frontier", "fir_heap_set_frontier",
      "fir_heap_alloc", manifest.entry]) {
      requireCondition(typeof instance.exports[name] === "function",
        `module is missing export ${name}`);
    }
    ADAPTER_STATE.set(this, {
      now,
      maximumNodes,
      encoder: new TextEncoder(),
      decoder: new TextDecoder("utf-8", { fatal: true }),
      memory,
      frontier: instance.exports.fir_heap_frontier,
      setFrontier: instance.exports.fir_heap_set_frontier,
      allocate: instance.exports.fir_heap_alloc,
      entry: instance.exports[manifest.entry],
      lastFrontier: undefined,
    });
    this.synchronizeFrontier();
  }

  synchronizeFrontier() {
    const state = ADAPTER_STATE.get(this);
    requireCondition(state !== undefined, "invalid adapter receiver");
    const value = u32(state.frontier());
    requireCondition(value >= HEAP_BASE && value % 8 === 0,
      `resident frontier ${value} is invalid`);
    if (state.lastFrontier !== undefined) {
      requireCondition(value >= state.lastFrontier,
        `resident frontier moved backwards from ${state.lastFrontier}`);
    }
    state.setFrontier(value);
    state.lastFrontier = value;
    return value;
  }

  prepare(animation, events) {
    const state = ADAPTER_STATE.get(this);
    requireCondition(state !== undefined, "invalid adapter receiver");
    const started = state.now();
    const frontierBefore = this.synchronizeFrontier();
    const pagesBefore = state.memory.buffer.byteLength / PAGE_BYTES;
    const projectStarted = state.now();
    const projectedAnimation = projectAnimation(animation);
    const projectMs = elapsed(state.now, projectStarted);
    const encodeStarted = state.now();
    const writer = new Encoder({
      fir_heap_alloc: state.allocate,
    }, state.memory, state.encoder);
    const animationWord = writer.animation(projectedAnimation);
    const eventsWord = writer.eventList(events);
    const encodeMs = elapsed(state.now, encodeStarted);
    const frontierAfterPrepare = this.synchronizeFrontier();
    const timings = Object.freeze({
      projectMs,
      encodeMs,
      prepareMs: elapsed(state.now, started),
    });
    const memory = Object.freeze({
      frontierBefore,
      frontierAfterPrepare,
      pagesBefore,
      pagesAfterPrepare: state.memory.buffer.byteLength / PAGE_BYTES,
      inputBytes: writer.bytes,
      residentAllocationCalls: writer.allocations,
      frontierGrowthPrepare: frontierAfterPrepare - frontierBefore,
    });
    const prepared = Object.freeze({
      [PREPARED]: this,
      state: "prepared",
      timings,
      memory,
    });
    PREPARED_STATE.set(prepared, {
      owner: this,
      args: [i32(animationWord), i32(eventsWord)],
      timings,
      memory,
    });
    return prepared;
  }

  execute(prepared) {
    const state = ADAPTER_STATE.get(this);
    const preparedState = PREPARED_STATE.get(prepared);
    requireCondition(state !== undefined && prepared?.[PREPARED] === this &&
      preparedState?.owner === this, "execute requires a fresh prepared handle");
    PREPARED_STATE.delete(prepared);
    const frontierBeforeExecute = this.synchronizeFrontier();
    const started = state.now();
    const physicalResult = u32(state.entry(...preparedState.args));
    const executeMs = elapsed(state.now, started);
    const frontierAfterExecute = this.synchronizeFrontier();
    const timings = Object.freeze({ ...preparedState.timings, executeMs });
    const memory = Object.freeze({
      ...preparedState.memory,
      frontierBeforeExecute,
      frontierAfterExecute,
      frontierGrowthExecute: frontierAfterExecute - frontierBeforeExecute,
      pagesAfterExecute: state.memory.buffer.byteLength / PAGE_BYTES,
    });
    const executed = Object.freeze({
      [EXECUTED]: this,
      state: "executed",
      timings,
      memory,
    });
    EXECUTED_STATE.set(executed, {
      owner: this,
      physicalResult,
      timings,
      memory,
    });
    return executed;
  }

  decode(executed) {
    const state = ADAPTER_STATE.get(this);
    const executedState = EXECUTED_STATE.get(executed);
    requireCondition(state !== undefined && executed?.[EXECUTED] === this &&
      executedState?.owner === this, "decode requires a fresh execution handle");
    EXECUTED_STATE.delete(executed);
    const started = state.now();
    const view = new DataView(state.memory.buffer);
    const header = readHeader(view, executedState.physicalResult, "Except result");
    requireCondition(header.kind === KIND.constructor && header.aux1 === 1,
      "entry did not return Except String (Array FrameAction)");
    const payload = readWord(view, header.address + HEADER_BYTES,
      "Except payload");
    let result;
    if (header.aux0 === 0) {
      result = { ok: false, error: readString(view, payload, state.decoder,
        "Except.error") };
    } else {
      requireCondition(header.aux0 === 1, "Except result has an invalid tag");
      result = {
        ok: true,
        actions: readArray(view, payload, "FrameAction array", state.maximumNodes)
          .map((action, index) => decodeAction(view, action, state.decoder,
            state.maximumNodes, `actions[${index}]`)),
      };
    }
    const decodeMs = elapsed(state.now, started);
    const timings = { ...executedState.timings, decodeMs };
    const frontierAfterDecode = this.synchronizeFrontier();
    return {
      ...result,
      timings,
      memory: {
        ...executedState.memory,
        frontierAfterDecode,
        frontierGrowthTotal:
          frontierAfterDecode - executedState.memory.frontierBefore,
        pagesAfterDecode: state.memory.buffer.byteLength / PAGE_BYTES,
      },
    };
  }

  replayTrace(animation, events) {
    const state = ADAPTER_STATE.get(this);
    requireCondition(state !== undefined, "invalid adapter receiver");
    const started = state.now();
    const decoded = this.decode(this.execute(this.prepare(animation, events)));
    const totalMs = elapsed(state.now, started);
    const { projectMs, encodeMs, executeMs, decodeMs } = decoded.timings;
    return {
      ...decoded,
      timings: {
        ...decoded.timings,
        totalMs,
        overheadMs: totalMs - projectMs - encodeMs - executeMs - decodeMs,
      },
    };
  }
}

export async function createIlluminatePlayerAdapter({
  bytes,
  manifest,
  build,
  now = defaultNow,
  maximumNodes = 1_000_000,
  startupTimings = {},
}) {
  requireCondition(bytes instanceof ArrayBuffer || ArrayBuffer.isView(bytes),
    "bytes must be an ArrayBuffer or view");
  requireCondition(typeof now === "function", "now must be a function");
  requireCondition(Number.isSafeInteger(maximumNodes) && maximumNodes > 0,
    "maximumNodes must be a positive safe integer");
  validateManifest(manifest);
  validateBuild(build);
  const compileStarted = now();
  const module = await WebAssembly.compile(bytes);
  const compileMs = elapsed(now, compileStarted);
  requireCondition(WebAssembly.Module.imports(module).length === 0,
    "complete runtime module has imports");
  const instantiateStarted = now();
  const instance = await WebAssembly.instantiate(module, {});
  const instantiateMs = elapsed(now, instantiateStarted);
  return new IlluminatePlayerAdapter({
    instance,
    manifest,
    build,
    now,
    maximumNodes,
    startupTimings: {
      fetchMs: startupTimings.fetchMs ?? 0,
      compileMs,
      instantiateMs,
      totalMs: (startupTimings.fetchMs ?? 0) + compileMs + instantiateMs,
    },
  });
}

function baseUrl() {
  return globalThis.location?.href ?? "file:///";
}

export async function fetchIlluminatePlayerAdapter(artifactUrl, {
  fetchImpl = globalThis.fetch,
  descriptorUrl,
  buildUrl,
  now = defaultNow,
  maximumNodes = 1_000_000,
} = {}) {
  requireCondition(typeof fetchImpl === "function",
    "fetchIlluminatePlayerAdapter requires fetch");
  const wasmUrl = new URL(artifactUrl, baseUrl());
  const descriptor = descriptorUrl === undefined
    ? new URL(`${wasmUrl.href}.json`)
    : new URL(descriptorUrl, baseUrl());
  const metadata = buildUrl === undefined
    ? new URL("BUILD.json", wasmUrl)
    : new URL(buildUrl, baseUrl());
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
  return createIlluminatePlayerAdapter({
    bytes,
    manifest,
    build,
    now,
    maximumNodes,
    startupTimings: { fetchMs: elapsed(now, started) },
  });
}
