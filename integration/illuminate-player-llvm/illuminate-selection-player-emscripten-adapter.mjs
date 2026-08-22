import { loadEmscriptenModule } from "./emscripten-loader.mjs";

export const ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION =
  "fir.illuminate-player.browser/v4";
export const ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION =
  "lean-4.32-Illuminate.Animation.SelectionAnimation/v4";
export const ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION =
  "fir.illuminate-player.persistent-checkpoint/v2";
export const ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION =
  "fir.illuminate-player.hot-event/v1";
export const ILLUMINATE_SELECTION_PLAYER_EMSCRIPTEN_WIRE_VERSION =
  "fir.illuminate-player.emscripten-wire/v1";

const MAX_UINT32 = 0xffffffff;
const MAXIMUM_BYTES = 64 * 1024 * 1024;
const PLAYER = Symbol("fir.illuminate-selection-player.emscripten-player");
const PLAYER_STATE = new WeakMap();

const REQUIRED_EXPORTS = Object.freeze([
  "fir_illuminate_selection_input_alloc",
  "fir_illuminate_selection_create",
  "fir_illuminate_selection_created_handle",
  "fir_illuminate_selection_dispatch",
  "fir_illuminate_selection_dispatch_tick_scalar",
  "fir_illuminate_selection_result_ptr",
  "fir_illuminate_selection_result_len",
  "fir_illuminate_selection_dispose",
  "fir_illuminate_selection_live_count",
  "fir_illuminate_selection_release",
]);

const PLAYBACK = Object.freeze([
  "paused",
  "playing",
  "waiting",
  "looping",
  "finishingLoop",
  "finished",
]);

function fail(message) {
  throw new Error(`FIR LLVM Illuminate selection-player adapter: ${message}`);
}

function requireCondition(condition, message) {
  if (!condition) fail(message);
}

function defaultNow() {
  return globalThis.performance?.now?.() ?? Date.now();
}

function elapsed(now, started) {
  const value = now() - started;
  return Number.isFinite(value) && value >= 0 ? value : 0;
}

function errorMessage(error) {
  return error instanceof Error ? error.message : String(error);
}

function object(value, label) {
  requireCondition(
    value !== null && typeof value === "object" && !Array.isArray(value),
    `${label} must be an object`,
  );
  return value;
}

function natural(value, label) {
  requireCondition(
    Number.isSafeInteger(value) && value >= 0 && value <= MAX_UINT32,
    `${label} must be a uint32 safe integer`,
  );
  return value;
}

function boolean(value, label) {
  requireCondition(typeof value === "boolean", `${label} must be a Boolean`);
  return value;
}

function timestamp(value, label) {
  requireCondition(
    typeof value === "number" && Number.isFinite(value),
    `${label} must be a finite binary64 number`,
  );
  return value;
}

function projectSelectionAnimation(animation) {
  object(animation, "animation");
  requireCondition(Array.isArray(animation.segments), "animation.segments must be an array");
  requireCondition(Array.isArray(animation.steps), "animation.steps must be an array");
  return {
    fps: natural(animation.fps, "animation.fps"),
    totalFrames: natural(animation.totalFrames, "animation.totalFrames"),
    segments: animation.segments.map((segment, index) => {
      const label = `animation.segments[${index}]`;
      object(segment, label);
      return {
        startFrame: natural(segment.sf, `${label}.sf`),
        frameCount: natural(segment.fc, `${label}.fc`),
      };
    }),
    steps: animation.steps.map((step, index) => {
      const label = `animation.steps[${index}]`;
      object(step, label);
      return {
        frame: natural(step.frame, `${label}.frame`),
        pause: boolean(step.pause, `${label}.pause`),
        loop: boolean(step.loop, `${label}.loop`),
      };
    }),
  };
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
    const next = new Uint8Array(capacity);
    next.set(this.buffer.subarray(0, this.length));
    this.buffer = next;
  }

  u8(value) {
    this.ensure(1);
    this.buffer[this.length] = value;
    this.length += 1;
  }

  u32(value) {
    natural(value, "wire UInt32");
    this.ensure(4);
    new DataView(this.buffer.buffer).setUint32(this.length, value, true);
    this.length += 4;
  }

  f64(value) {
    timestamp(value, "tick timestamp");
    this.ensure(8);
    new DataView(this.buffer.buffer).setFloat64(this.length, value, true);
    this.length += 8;
  }

  finish() {
    return this.buffer.slice(0, this.length);
  }
}

function encodeAnimation(animation, maximumBytes) {
  const writer = new ByteWriter(maximumBytes);
  writer.u8(0x46);
  writer.u8(0x49);
  writer.u8(0x41);
  writer.u8(0x31);
  writer.u32(animation.fps);
  writer.u32(animation.totalFrames);
  writer.u32(animation.segments.length);
  for (const segment of animation.segments) {
    writer.u32(segment.startFrame);
    writer.u32(segment.frameCount);
  }
  writer.u32(animation.steps.length);
  for (const step of animation.steps) {
    writer.u32(step.frame);
    writer.u8(step.pause ? 1 : 0);
    writer.u8(step.loop ? 1 : 0);
  }
  return writer.finish();
}

function encodeEvent(event, maximumBytes) {
  object(event, "event");
  const writer = new ByteWriter(maximumBytes);
  writer.u8(0x46);
  writer.u8(0x49);
  writer.u8(0x45);
  writer.u8(0x31);
  switch (event.kind) {
    case "advance":
      writer.u8(0);
      break;
    case "pause":
      writer.u8(1);
      break;
    case "seek":
      writer.u8(2);
      writer.u32(natural(event.frame, "event.frame"));
      break;
    case "playTo":
      writer.u8(3);
      writer.u32(natural(event.frame, "event.frame"));
      writer.u8(boolean(event.loopAfter ?? false, "event.loopAfter") ? 1 : 0);
      break;
    case "loopAt":
      writer.u8(4);
      writer.u32(natural(event.frame, "event.frame"));
      break;
    case "tick":
      writer.u8(5);
      writer.f64(event.timestamp);
      break;
    default:
      fail(`unknown PlayerEvent kind ${String(event.kind)}`);
  }
  return writer.finish();
}

class ByteReader {
  constructor(bytes, decoder) {
    this.bytes = bytes;
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
    const value = new DataView(
      this.bytes.buffer,
      this.bytes.byteOffset + this.position,
      4,
    ).getUint32(0, true);
    this.position += 4;
    return value;
  }

  expect(value, label) {
    requireCondition(this.u8(label) === value, `invalid ${label}`);
  }

  string(label) {
    const length = this.u32(`${label} length`);
    this.require(length, label);
    const value = this.decoder.decode(
      this.bytes.subarray(this.position, this.position + length),
    );
    this.position += length;
    return value;
  }

  done() {
    requireCondition(this.position === this.bytes.length, "wire response has trailing bytes");
  }
}

function decodeResponse(bytes, decoder) {
  const reader = new ByteReader(bytes, decoder);
  reader.expect(0x46, "response magic");
  reader.expect(0x49, "response magic");
  reader.expect(0x52, "response magic");
  reader.expect(0x31, "response wire version");
  const status = reader.u8("response status");
  if (status === 1) {
    const error = reader.string("error");
    reader.done();
    return { ok: false, error };
  }
  requireCondition(status === 0, `unknown response status ${status}`);
  const action = {
    frame: reader.u32("selection frame"),
    step: reader.u32("selection step"),
    segment: reader.u32("selection segment"),
    localFrame: reader.u32("selection local frame"),
    segmentChanged: reader.u8("selection segmentChanged") !== 0,
    playback: undefined,
  };
  const playback = reader.u8("selection playback");
  requireCondition(playback < PLAYBACK.length, `unknown playback tag ${playback}`);
  action.playback = PLAYBACK[playback];
  const schedule = reader.u8("selection scheduleNextFrame");
  requireCondition(schedule <= 1, "scheduleNextFrame is not a Boolean");
  reader.done();
  return { ok: true, action, scheduleNextFrame: schedule === 1 };
}

function validateManifest(manifest) {
  requireCondition(manifest?.profile === "emscripten", "manifest profile is not Emscripten");
  requireCondition(manifest.runtime?.threads === false, "selection player must be unthreaded");
  requireCondition(
    manifest.runtime?.crossOriginIsolated !== true,
    "selection player unexpectedly requires cross-origin isolation",
  );
  const exports = new Set(manifest.abi?.exports);
  for (const symbol of REQUIRED_EXPORTS) {
    requireCondition(exports.has(symbol), `manifest does not declare ${symbol}`);
  }
  requireCondition(
    manifest.abi?.runtimeMethods?.includes("HEAPU8"),
    "manifest does not declare the HEAPU8 transfer view",
  );
  const capabilities = manifest.capabilities;
  requireCondition(
    capabilities?.browserAdapter?.apiVersion ===
      ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
    "manifest browser API version mismatch",
  );
  requireCondition(
    capabilities?.inputLayout?.version ===
      ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
    "manifest input layout version mismatch",
  );
  requireCondition(
    capabilities?.ownership?.version ===
      ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
    "manifest ownership version mismatch",
  );
  requireCondition(
    capabilities?.hotEvent?.version === ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION,
    "manifest hot-event version mismatch",
  );
  requireCondition(
    capabilities?.emscriptenWire?.version ===
      ILLUMINATE_SELECTION_PLAYER_EMSCRIPTEN_WIRE_VERSION,
    "manifest Emscripten wire version mismatch",
  );
}

class EmscriptenIlluminateSelectionPlayerAdapter {
  constructor(loaded, { now = defaultNow, maximumBytes = MAXIMUM_BYTES } = {}) {
    requireCondition(typeof now === "function", "now must be a function");
    requireCondition(
      Number.isSafeInteger(maximumBytes) && maximumBytes > 0 && maximumBytes <= MAXIMUM_BYTES,
      `maximumBytes must be between 1 and ${MAXIMUM_BYTES}`,
    );
    validateManifest(loaded.manifest);
    requireCondition(loaded.module.HEAPU8 instanceof Uint8Array, "module does not expose HEAPU8");
    this.loaded = loaded;
    this.module = loaded.module;
    this.exports = loaded.exports;
    this.now = now;
    this.maximumBytes = maximumBytes;
    this.decoder = new TextDecoder("utf-8", { fatal: true });
    this.peakBytes = this.module.HEAPU8.byteLength;
    this.busy = false;
  }

  memory(extra = {}) {
    const currentBytes = this.module.HEAPU8.byteLength;
    this.peakBytes = Math.max(this.peakBytes, currentBytes);
    return Object.freeze({
      currentBytes,
      peakBytes: this.peakBytes,
      livePlayers: this.exports.fir_illuminate_selection_live_count() >>> 0,
      ...extra,
    });
  }

  transfer(bytes) {
    const pointer = this.exports.fir_illuminate_selection_input_alloc(bytes.length) >>> 0;
    requireCondition(pointer !== 0, "could not allocate the wire request");
    requireCondition(
      pointer <= this.module.HEAPU8.byteLength - bytes.length,
      "wire request allocation is outside module memory",
    );
    this.module.HEAPU8.set(bytes, pointer);
  }

  response() {
    const pointer = this.exports.fir_illuminate_selection_result_ptr() >>> 0;
    const length = this.exports.fir_illuminate_selection_result_len() >>> 0;
    requireCondition(
      length <= this.module.HEAPU8.byteLength &&
        pointer <= this.module.HEAPU8.byteLength - length,
      "C bridge returned an out-of-bounds result",
    );
    return this.module.HEAPU8.slice(pointer, pointer + length);
  }

  withOperation(operation) {
    requireCondition(!this.busy, "adapter operations are not reentrant");
    this.busy = true;
    try {
      return operation();
    } finally {
      this.busy = false;
    }
  }

  createPlayer(animation) {
    return this.withOperation(() => {
      const totalStarted = this.now();
      const timings = { projectMs: 0, encodeMs: 0, executeMs: 0, decodeMs: 0 };
      let requestBytes = 0;
      let responseBytes = 0;
      try {
        const projectStarted = this.now();
        const projected = projectSelectionAnimation(animation);
        timings.projectMs = elapsed(this.now, projectStarted);

        const encodeStarted = this.now();
        const request = encodeAnimation(projected, this.maximumBytes);
        requestBytes = request.length;
        this.transfer(request);
        timings.encodeMs = elapsed(this.now, encodeStarted);

        const executeStarted = this.now();
        const transportStatus = this.exports.fir_illuminate_selection_create(request.length) >>> 0;
        timings.executeMs = elapsed(this.now, executeStarted);
        requireCondition(transportStatus === 0, `C create bridge failed with status ${transportStatus}`);

        const decodeStarted = this.now();
        const response = this.response();
        responseBytes = response.length;
        const decoded = decodeResponse(response, this.decoder);
        timings.decodeMs = elapsed(this.now, decodeStarted);
        if (!decoded.ok) {
          return this.finalizeFailure(decoded.error, timings, totalStarted, {
            requestBytes,
            responseBytes,
          });
        }
        const handle = this.exports.fir_illuminate_selection_created_handle() >>> 0;
        requireCondition(handle !== 0, "C bridge returned no retained player handle");
        const player = Object.freeze({ [PLAYER]: this });
        PLAYER_STATE.set(player, { owner: this, handle, disposed: false });
        return this.finalizeSuccess({ player, ...decoded }, timings, totalStarted, {
          requestBytes,
          responseBytes,
        });
      } catch (error) {
        return this.finalizeFailure(errorMessage(error), timings, totalStarted, {
          requestBytes,
          responseBytes,
        });
      }
    });
  }

  playerState(player) {
    const state = PLAYER_STATE.get(player);
    requireCondition(player?.[PLAYER] === this && state?.owner === this, "player belongs to another adapter");
    requireCondition(!state.disposed, "player has been disposed");
    return state;
  }

  dispatch(player, event) {
    return this.dispatchOperation(player, () => encodeEvent(event, this.maximumBytes), false);
  }

  dispatchTick(player, value) {
    return this.dispatchOperation(player, () => timestamp(value, "timestamp"), true);
  }

  dispatchOperation(player, prepareArgument, scalarTick) {
    return this.withOperation(() => {
      const totalStarted = this.now();
      const timings = { encodeMs: 0, executeMs: 0, decodeMs: 0 };
      let requestBytes = 0;
      let responseBytes = 0;
      try {
        const state = this.playerState(player);
        const encodeStarted = this.now();
        const argument = prepareArgument();
        if (!scalarTick) {
          requestBytes = argument.length;
          this.transfer(argument);
        }
        timings.encodeMs = elapsed(this.now, encodeStarted);

        const executeStarted = this.now();
        const transportStatus = scalarTick
          ? this.exports.fir_illuminate_selection_dispatch_tick_scalar(state.handle, argument) >>> 0
          : this.exports.fir_illuminate_selection_dispatch(state.handle, argument.length) >>> 0;
        timings.executeMs = elapsed(this.now, executeStarted);
        requireCondition(transportStatus === 0, `C dispatch bridge failed with status ${transportStatus}`);

        const decodeStarted = this.now();
        const response = this.response();
        responseBytes = response.length;
        const decoded = decodeResponse(response, this.decoder);
        timings.decodeMs = elapsed(this.now, decodeStarted);
        if (!decoded.ok) {
          return this.finalizeFailure(decoded.error, timings, totalStarted, {
            requestBytes,
            responseBytes,
          });
        }
        return this.finalizeSuccess(decoded, timings, totalStarted, {
          requestBytes,
          responseBytes,
        });
      } catch (error) {
        return this.finalizeFailure(errorMessage(error), timings, totalStarted, {
          requestBytes,
          responseBytes,
        });
      }
    });
  }

  finalizeTimings(timings, totalStarted) {
    const totalMs = elapsed(this.now, totalStarted);
    const measured = Object.values(timings).reduce((sum, value) => sum + value, 0);
    return Object.freeze({ ...timings, totalMs, overheadMs: totalMs - measured });
  }

  finalizeSuccess(value, timings, totalStarted, memory) {
    return {
      ok: true,
      ...value,
      timings: this.finalizeTimings(timings, totalStarted),
      memory: this.memory(memory),
    };
  }

  finalizeFailure(error, timings, totalStarted, memory) {
    return {
      ok: false,
      error,
      timings: this.finalizeTimings(timings, totalStarted),
      memory: this.memory(memory),
    };
  }

  disposePlayer(player) {
    const state = PLAYER_STATE.get(player);
    requireCondition(player?.[PLAYER] === this && state?.owner === this, "player belongs to another adapter");
    if (state.disposed) return;
    const status = this.exports.fir_illuminate_selection_dispose(state.handle) >>> 0;
    requireCondition(status === 0, `C dispose bridge failed with status ${status}`);
    state.disposed = true;
  }

  replayTrace(animation, events) {
    requireCondition(Array.isArray(events), "events must be an array");
    const totalStarted = this.now();
    const created = this.createPlayer(animation);
    if (!created.ok) return created;
    const actions = [created.action];
    const dispatches = [];
    try {
      for (const event of events) {
        const dispatched = this.dispatch(created.player, event);
        dispatches.push(dispatched);
        if (!dispatched.ok) return dispatched;
        actions.push(dispatched.action);
      }
      return {
        ok: true,
        actions,
        timings: {
          creation: created.timings,
          dispatches: dispatches.map((result) => result.timings),
          totalMs: elapsed(this.now, totalStarted),
        },
        memory: {
          creation: created.memory,
          dispatches: dispatches.map((result) => result.memory),
          ...this.memory(),
        },
      };
    } finally {
      this.disposePlayer(created.player);
    }
  }
}

export async function loadEmscriptenIlluminateSelectionPlayerAdapter(
  manifestSource,
  options = {},
) {
  const loaded = await loadEmscriptenModule(manifestSource, options.loader);
  return new EmscriptenIlluminateSelectionPlayerAdapter(loaded, options);
}
