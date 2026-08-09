/** Browser/Node adapter for the FIR-native Illuminate selection player. */

export const ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION =
  "fir.illuminate-player.browser/v4";
export const ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION =
  "lean-4.32-Illuminate.Animation.SelectionAnimation/v4";
export const ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION =
  "fir.illuminate-player.persistent-checkpoint/v2";
export const ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION =
  "fir.illuminate-player.hot-event/v1";

const PAGE_BYTES = 65536;
const HEAP_BASE = 1024;
const FLOAT64_BITS = new DataView(new ArrayBuffer(8));
const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const MAX_UINT32 = 0xffffffff;
const MAX_IMMEDIATE = 0x7fffffffn;
const ARRAY_MARKER = 0x41525259;
const STRING_MARKER = 1;
const FLOAT_BOX_MARKER = 6;
const PERSISTENT_LIVE_FLAGS = 3;

const KIND = Object.freeze({
  constructor: 1,
  boxed: 3,
  string: 4,
  natural: 5,
  opaque: 8,
});

const PLAYER = Symbol("fir.illuminate-selection-player.live-player");
const ADAPTER_STATE = new WeakMap();
const PLAYER_STATE = new WeakMap();

function fail(message) {
  throw new Error(`FIR Illuminate selection-player adapter: ${message}`);
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

function float64Bits(value, label) {
  requireCondition(typeof value === "number" && Number.isFinite(value),
    `${label} must be finite`);
  FLOAT64_BITS.setFloat64(0, value, true);
  return FLOAT64_BITS.getBigUint64(0, true);
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

function projectSelectionAnimation(animation) {
  requireObject(animation, "animation");
  requireCondition(Array.isArray(animation.segments),
    "animation.segments must be an array");
  requireCondition(Array.isArray(animation.steps),
    "animation.steps must be an array");
  return { timeline: {
    fps: projectNatural(animation.fps, "animation.fps"),
    totalFrames: projectNatural(animation.totalFrames, "animation.totalFrames"),
    segments: animation.segments.map((segment, segmentIndex) => {
      const label = `animation.segments[${segmentIndex}]`;
      requireObject(segment, label);
      return {
        startFrame: projectNatural(segment.sf, `${label}.sf`),
        frameCount: projectNatural(segment.fc, `${label}.fc`),
        paramMap: [],
        params: [],
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
  } };
}

function writeHeader(view, address, {
  kind,
  bytes,
  flags = PERSISTENT_LIVE_FLAGS,
  refCount = 0,
  aux0 = 0,
  aux1 = 0,
  aux2 = 0,
  aux3 = 0,
}) {
  const words = [kind, flags, refCount, bytes,
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
  constructor(exports, memory, encoder, { persistent = false } = {}) {
    this.exports = exports;
    this.memory = memory;
    this.encoder = encoder;
    this.flags = persistent ? PERSISTENT_LIVE_FLAGS : 2;
    this.refCount = persistent ? 0 : 1;
    this.allocations = 0;
    this.objects = 0;
    this.bytes = 0;
    this.reservation = undefined;
    this.preencodedStrings = new Map();
  }

  allocateResident(bytes, label) {
    requireCondition(Number.isSafeInteger(bytes) && bytes >= HEADER_BYTES &&
      bytes <= MAX_UINT32 && bytes % 8 === 0,
    `${label} allocation size is invalid`);
    const address = u32(this.exports.fir_heap_alloc(bytes));
    requireCondition(address >= HEAP_BASE && address % 8 === 0,
      `${label} allocation returned invalid address ${address}`);
    requireCondition(address + bytes <= this.memory.buffer.byteLength,
      `${label} allocation exceeds module memory`);
    new Uint8Array(this.memory.buffer, address, bytes).fill(0);
    this.allocations += 1;
    return address;
  }

  reserve(bytes, label) {
    requireCondition(this.reservation === undefined,
      `${label} overlaps an active encoder reservation`);
    const address = this.allocateResident(bytes, label);
    this.reservation = { cursor: address, end: address + bytes, label };
  }

  finishReservation() {
    const reservation = this.reservation;
    requireCondition(reservation !== undefined,
      "encoder has no active reservation");
    requireCondition(reservation.cursor === reservation.end,
      `${reservation.label} used ${reservation.cursor} of ${reservation.end}`);
    this.reservation = undefined;
  }

  allocate(bytes, label) {
    let address;
    if (this.reservation === undefined) {
      address = this.allocateResident(bytes, label);
    } else {
      address = this.reservation.cursor;
      requireCondition(address + bytes <= this.reservation.end,
        `${label} exceeds ${this.reservation.label}`);
      this.reservation.cursor += bytes;
    }
    this.objects += 1;
    this.bytes += bytes;
    return address;
  }

  naturalProjectedBytes(value) {
    return BigInt(value) <= MAX_IMMEDIATE ? 0 : 40;
  }

  preencodedString(value, label) {
    const text = string(value, label);
    let bytes = this.preencodedStrings.get(text);
    if (bytes === undefined) {
      bytes = this.encoder.encode(text);
      this.preencodedStrings.set(text, bytes);
    }
    return bytes;
  }

  stringBytes(value, label) {
    return align8(HEADER_BYTES + this.preencodedString(value, label).length);
  }

  ctorBytes(fields, scalarBytes) {
    if (fields === 0 && scalarBytes === 0) return 0;
    return align8(HEADER_BYTES + SLOT_BYTES * fields + scalarBytes);
  }

  arrayBytes(values) {
    return align8(HEADER_BYTES + SLOT_BYTES * values);
  }

  paramBindingBytes(binding, label) {
    const targetBytes = binding.target.kind === "textContent" ? 0 :
      this.stringBytes(binding.target.name, `${label}.target.name`) +
        this.ctorBytes(1, 0);
    return this.naturalProjectedBytes(binding.element) + targetBytes +
      this.ctorBytes(2, 0);
  }

  segmentBytes(segment, label) {
    let bytes = this.arrayBytes(segment.paramMap.length) +
      this.arrayBytes(segment.params.length) + this.ctorBytes(4, 0) +
      this.naturalProjectedBytes(segment.startFrame) +
      this.naturalProjectedBytes(segment.frameCount);
    segment.paramMap.forEach((binding, index) => {
      bytes += this.paramBindingBytes(binding,
        `${label}.paramMap[${index}]`);
    });
    segment.params.forEach((row, rowIndex) => {
      bytes += this.arrayBytes(row.length);
      row.forEach((value, index) => {
        bytes += this.stringBytes(value,
          `${label}.params[${rowIndex}][${index}]`);
      });
    });
    return bytes;
  }

  stepBytes(step) {
    return this.naturalProjectedBytes(step.frame) + this.ctorBytes(1, 2);
  }

  selectionBytes(animation) {
    let bytes = this.arrayBytes(animation.segments.length) +
      this.arrayBytes(animation.steps.length) + this.ctorBytes(4, 0) +
      this.naturalProjectedBytes(animation.fps) +
      this.naturalProjectedBytes(animation.totalFrames);
    animation.segments.forEach((segment, index) => {
      bytes += this.segmentBytes(segment, `animation.segments[${index}]`);
    });
    animation.steps.forEach((step) => {
      bytes += this.stepBytes(step);
    });
    return bytes;
  }

  selectionAnimationBytes(animation) {
    return this.selectionBytes(animation.timeline);
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
      flags: this.flags,
      refCount: this.refCount,
      aux0: 1,
      aux1: 1,
    });
    view.setBigUint64(address + HEADER_BYTES, n, true);
    return address;
  }

  string(value, label) {
    const bytes = this.preencodedString(value, label);
    const allocationBytes = align8(HEADER_BYTES + bytes.length);
    const address = this.allocate(allocationBytes, label);
    const view = new DataView(this.memory.buffer);
    writeHeader(view, address, {
      kind: KIND.string,
      bytes: allocationBytes,
      flags: this.flags,
      refCount: this.refCount,
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
      flags: this.flags,
      refCount: this.refCount,
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
      flags: this.flags,
      refCount: this.refCount,
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

  selectionAnimation(animation) {
    return this.animation(animation.timeline);
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
        const bytes = new Uint8Array(8);
        new DataView(bytes.buffer).setBigUint64(0,
          float64Bits(event.timestamp, `${label}.timestamp`), true);
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
  const padding = readU32(view, address + 4, label);
  requireCondition(padding === 0,
    `${label} has nonzero slot padding ${padding} at ${address} (word ${result})`);
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

function allocatePersistentStateSlot(writer) {
  const naturalAddresses = Array.from({ length: 5 }, (_, index) => {
    const address = writer.allocate(40, `persistent state Nat ${index}`);
    const view = new DataView(writer.memory.buffer);
    writeHeader(view, address, {
      kind: KIND.natural,
      bytes: 40,
      aux0: 1,
      aux1: 1,
    });
    view.setBigUint64(address + HEADER_BYTES, 0n, true);
    return address;
  });
  const floatBoxAddress = writer.allocate(40, "persistent state boxed Float");
  let view = new DataView(writer.memory.buffer);
  writeHeader(view, floatBoxAddress, {
    kind: KIND.boxed,
    bytes: 40,
    aux0: FLOAT_BOX_MARKER,
    aux1: 8,
  });
  const floatSomeAddress = writer.allocate(40, "persistent state Option Float");
  view = new DataView(writer.memory.buffer);
  writeHeader(view, floatSomeAddress, {
    kind: KIND.constructor,
    bytes: 40,
    aux0: 1,
    aux1: 1,
  });
  writeWord(view, floatSomeAddress + HEADER_BYTES, floatBoxAddress);
  const naturalSomeAddresses = Array.from({ length: 2 }, (_, index) => {
    const address = writer.allocate(40, `persistent state Option Nat ${index}`);
    view = new DataView(writer.memory.buffer);
    writeHeader(view, address, {
      kind: KIND.constructor,
      bytes: 40,
      aux0: 1,
      aux1: 1,
    });
    writeWord(view, address + HEADER_BYTES, naturalAddresses[3 + index]);
    return address;
  });
  const stateAddress = writer.allocate(88, "persistent PlayerState");
  view = new DataView(writer.memory.buffer);
  writeHeader(view, stateAddress, {
    kind: KIND.constructor,
    bytes: 88,
    aux0: 0,
    aux1: 6,
    aux3: 3,
  });
  writeWord(view, stateAddress + HEADER_BYTES, naturalAddresses[0]);
  writeWord(view, stateAddress + HEADER_BYTES + SLOT_BYTES, naturalAddresses[1]);
  writeWord(view, stateAddress + HEADER_BYTES + 2 * SLOT_BYTES, immediate(0));
  writeWord(view, stateAddress + HEADER_BYTES + 3 * SLOT_BYTES,
    naturalAddresses[2]);
  writeWord(view, stateAddress + HEADER_BYTES + 4 * SLOT_BYTES, immediate(0));
  writeWord(view, stateAddress + HEADER_BYTES + 5 * SLOT_BYTES, immediate(0));
  return Object.freeze({
    stateAddress,
    naturalAddresses,
    floatBoxAddress,
    floatSomeAddress,
    naturalSomeAddresses,
  });
}

function readOptionFloatBits(view, word, label) {
  if (classify(word) === "immediate") {
    requireCondition((u32(word) >>> 1) === 0, `${label} has invalid None tag`);
    return null;
  }
  const { fields } = readConstructor(view, word, 1, 1, 0, label);
  const boxed = readHeader(view, fields[0], `${label}.value`);
  requireCondition(boxed.kind === KIND.boxed && boxed.bytes === 40 &&
    boxed.aux0 === FLOAT_BOX_MARKER && boxed.aux1 === 8 &&
    boxed.aux2 === 0 && boxed.aux3 === 0,
  `${label}.value is not a canonical boxed Float`);
  return view.getBigUint64(boxed.address + HEADER_BYTES, true);
}

function readOptionNatural(view, word, label) {
  if (classify(word) === "immediate") {
    requireCondition((u32(word) >>> 1) === 0, `${label} has invalid None tag`);
    return null;
  }
  const { fields } = readConstructor(view, word, 1, 1, 0, label);
  return readNatural(view, fields[0], `${label}.value`);
}

function writePersistentNatural(view, address, value, label) {
  requireCondition(value >= 0n && value <= BigInt(MAX_UINT32),
    `${label} is outside the persistent uint32 state domain`);
  requireCondition(value > MAX_IMMEDIATE,
    `${label} should use the immediate Natural representation`);
  view.setBigUint64(address + HEADER_BYTES, value, true);
}

function persistentNaturalWord(view, address, value, label) {
  requireCondition(value >= 0n && value <= BigInt(MAX_UINT32),
    `${label} is outside the persistent uint32 state domain`);
  if (value <= MAX_IMMEDIATE) return Number(value * 2n + 1n) >>> 0;
  writePersistentNatural(view, address, value, label);
  return address;
}

function copyPlayerStateToSlot(view, word, slot, label) {
  const { fields, scalarAddress } = readConstructor(view, word, 0, 6, 3, label);
  const naturals = [
    readNatural(view, fields[0], `${label}.frame`),
    readNatural(view, fields[1], `${label}.step`),
    readNatural(view, fields[3], `${label}.pauseFrame`),
    readOptionNatural(view, fields[4], `${label}.targetFrame`),
    readOptionNatural(view, fields[5], `${label}.renderedSegment`),
  ];
  const startTimeBits = readOptionFloatBits(view, fields[2],
    `${label}.startTime`);
  const playback = view.getUint8(scalarAddress);
  const loopExitPending = view.getUint8(scalarAddress + 1);
  const loopAfterTarget = view.getUint8(scalarAddress + 2);
  requireCondition(playback < 6 && loopExitPending < 2 && loopAfterTarget < 2,
    `${label} has invalid scalar state`);

  const naturalWords = naturals.map((value, index) => value === null
    ? null
    : persistentNaturalWord(view, slot.naturalAddresses[index], value,
      `${label} Nat ${index}`));
  if (startTimeBits !== null) {
    view.setBigUint64(slot.floatBoxAddress + HEADER_BYTES,
      startTimeBits, true);
  }
  writeWord(view, slot.stateAddress + HEADER_BYTES,
    naturalWords[0]);
  writeWord(view, slot.stateAddress + HEADER_BYTES + SLOT_BYTES,
    naturalWords[1]);
  writeWord(view, slot.stateAddress + HEADER_BYTES + 2 * SLOT_BYTES,
    startTimeBits === null ? immediate(0) : slot.floatSomeAddress);
  writeWord(view, slot.stateAddress + HEADER_BYTES + 3 * SLOT_BYTES,
    naturalWords[2]);
  if (naturalWords[3] !== null) {
    writeWord(view, slot.naturalSomeAddresses[0] + HEADER_BYTES,
      naturalWords[3]);
  }
  if (naturalWords[4] !== null) {
    writeWord(view, slot.naturalSomeAddresses[1] + HEADER_BYTES,
      naturalWords[4]);
  }
  writeWord(view, slot.stateAddress + HEADER_BYTES + 4 * SLOT_BYTES,
    naturals[3] === null ? immediate(0) : slot.naturalSomeAddresses[0]);
  writeWord(view, slot.stateAddress + HEADER_BYTES + 5 * SLOT_BYTES,
    naturals[4] === null ? immediate(0) : slot.naturalSomeAddresses[1]);
  const stateScalars = slot.stateAddress + HEADER_BYTES + 6 * SLOT_BYTES;
  view.setUint8(stateScalars, playback);
  view.setUint8(stateScalars + 1, loopExitPending);
  view.setUint8(stateScalars + 2, loopAfterTarget);
}

const PLAYBACK = ["paused", "playing", "waiting", "looping",
  "finishingLoop", "finished"];

function decodeSelection(view, word, label) {
  const { fields, scalarAddress } =
    readConstructor(view, word, 0, 4, 2, label);
  const playback = view.getUint8(scalarAddress + 1);
  requireCondition(playback < PLAYBACK.length,
    `${label}.playback tag ${playback} is invalid`);
  return {
    frame: numberNatural(view, fields[0], `${label}.frame`),
    step: numberNatural(view, fields[1], `${label}.step`),
    segment: numberNatural(view, fields[2], `${label}.segment`),
    localFrame: numberNatural(view, fields[3], `${label}.localFrame`),
    segmentChanged: view.getUint8(scalarAddress) !== 0,
    playback: PLAYBACK[playback],
  };
}

function decodeLiveSelectionTransition(view, word, stateSlot, label) {
  const { fields, scalarAddress } =
    readConstructor(view, word, 0, 2, 1, label);
  const scheduleNextFrame = view.getUint8(scalarAddress);
  requireCondition(scheduleNextFrame < 2,
    `${label}.scheduleNextFrame is not a Bool`);
  const action = decodeSelection(view, fields[1], `${label}.selection`);
  copyPlayerStateToSlot(view, fields[0], stateSlot, `${label}.state`);
  return {
    action,
    scheduleNextFrame: scheduleNextFrame !== 0,
  };
}

function decodeInitialResult(view, word, stateSlot, decoder, maximumNodes) {
  const header = readHeader(view, word, "initialSelectionLive Except result");
  requireCondition(header.kind === KIND.constructor && header.aux1 === 1 &&
    header.aux3 === 0,
  "initialSelectionLive did not return Except String LiveSelectionTransition");
  const payload = readWord(view, header.address + HEADER_BYTES,
    "initialSelectionLive Except payload");
  if (header.aux0 === 0) {
    return {
      ok: false,
      error: readString(view, payload, decoder, "initialSelectionLive error"),
    };
  }
  requireCondition(header.aux0 === 1,
    "initialSelectionLive Except result has an invalid tag");
  return {
    ok: true,
    ...decodeLiveSelectionTransition(view, payload, stateSlot,
      "initialSelectionLive transition"),
  };
}

function validateManifest(manifest) {
  requireObject(manifest, "module descriptor");
  requireCondition(manifest.entry ===
    "Illuminate.AnimationPlayer.initialSelectionLive",
  "module descriptor has the wrong entry");
  requireCondition(JSON.stringify(manifest.params) ===
    JSON.stringify(["object"]) && manifest.result === "object",
  "module descriptor has the wrong structured ABI");
  requireCondition(Array.isArray(manifest.imports) && manifest.imports.length === 0,
    "complete runtime package must have zero imports");
}

function validateBuild(build) {
  requireObject(build, "BUILD.json");
  requireCondition(build.capabilities?.browserAdapter?.apiVersion ===
    ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
  "BUILD.json has the wrong adapter API version");
  requireCondition(build.capabilities?.inputLayout?.version ===
    ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
  "BUILD.json has the wrong input-layout version");
  requireCondition(build.capabilities?.ownership?.version ===
    ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
  "BUILD.json has the wrong ownership version");
  requireCondition(build.capabilities?.hotEvent?.version ===
    ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION,
  "BUILD.json has the wrong hot-event version");
}

function errorMessage(error) {
  return error instanceof Error ? error.message : String(error);
}

function instanceState(module, now, maximumNodes) {
  const started = now();
  const instance = new WebAssembly.Instance(module, {});
  const instantiateMs = elapsed(now, started);
  const memory = instance.exports.memory;
  requireCondition(memory instanceof WebAssembly.Memory,
    "module does not export its memory");
  const required = [
    "Illuminate.AnimationPlayer.initialSelectionLive",
    "Illuminate.AnimationPlayer.transitionSelectionLive",
    "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact",
    "fir_heap_frontier",
    "fir_heap_set_frontier",
    "fir_heap_rewind",
    "fir_heap_alloc",
  ];
  for (const name of required) {
    requireCondition(typeof instance.exports[name] === "function",
      `module is missing export ${name}`);
  }
  const state = {
    instance,
    memory,
    initialLive:
      instance.exports["Illuminate.AnimationPlayer.initialSelectionLive"],
    transitionLive:
      instance.exports["Illuminate.AnimationPlayer.transitionSelectionLive"],
    transitionTickLiveBits:
      instance.exports[
        "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact"],
    frontier: instance.exports.fir_heap_frontier,
    setFrontier: instance.exports.fir_heap_set_frontier,
    rewindFrontier: instance.exports.fir_heap_rewind,
    allocate: instance.exports.fir_heap_alloc,
    encoder: new TextEncoder(),
    decoder: new TextDecoder("utf-8", { fatal: true }),
    maximumNodes,
    instantiateMs,
  };
  readFrontier(state);
  return state;
}

function readFrontier(state) {
  const value = u32(state.frontier());
  requireCondition(value >= HEAP_BASE && value % 8 === 0,
    `resident frontier ${value} is invalid`);
  requireCondition(value <= state.memory.buffer.byteLength,
    `resident frontier ${value} exceeds module memory`);
  return value;
}

function rewind(state, checkpoint, now) {
  const started = now();
  const frontierBeforeRewind = readFrontier(state);
  requireCondition(frontierBeforeRewind >= checkpoint,
    `frontier ${frontierBeforeRewind} is below checkpoint ${checkpoint}`);
  const clearedBytes = frontierBeforeRewind - checkpoint;
  new Uint8Array(state.memory.buffer, checkpoint, clearedBytes).fill(0);
  state.rewindFrontier(checkpoint);
  const postRewindFrontier = readFrontier(state);
  requireCondition(postRewindFrontier === checkpoint,
    `frontier rewind stopped at ${postRewindFrontier}, expected ${checkpoint}`);
  return {
    rewindMs: elapsed(now, started),
    frontierBeforeRewind,
    clearedBytes,
    postRewindFrontier,
  };
}

function invalidatePlayer(state, status) {
  state.status = status;
  state.instance = undefined;
  state.memory = undefined;
  state.initialLive = undefined;
  state.transitionLive = undefined;
  state.transitionTickLiveBits = undefined;
  state.frontier = undefined;
  state.setFrontier = undefined;
  state.rewindFrontier = undefined;
  state.allocate = undefined;
  state.selectionAddress = 0;
  state.checkpoint = 0;
  state.stateSlot = undefined;
}

function dispatchCore(owner, player, operation, encode, execute) {
  const adapter = ADAPTER_STATE.get(owner);
  const state = PLAYER_STATE.get(player);
  requireCondition(adapter !== undefined && player?.[PLAYER] === owner &&
    state?.owner === owner,
    `${operation} requires this adapter's player handle`);
  requireCondition(state.status === "active",
    `player is ${state.status ?? "invalid"}`);
  const totalStarted = adapter.now();
  const timings = { encodeMs: 0, executeMs: 0, decodeMs: 0, rewindMs: 0 };
  const memory = {
    persistentCheckpoint: state.checkpoint,
    frontierBefore: undefined,
    frontierAfterEncode: undefined,
    frontierAfterExecute: undefined,
    peakFrontier: undefined,
    frontierBeforeRewind: undefined,
    clearedBytes: 0,
    postRewindFrontier: undefined,
    scratchBytes: 0,
    scratchAllocationCalls: 0,
    pagesBefore: state.memory.buffer.byteLength / PAGE_BYTES,
    pagesAfter: undefined,
  };
  let phase = "encode";
  let decoded;
  let failure;
  try {
    memory.frontierBefore = readFrontier(state);
    requireCondition(memory.frontierBefore === state.checkpoint,
      `${operation} began at ${memory.frontierBefore}, expected ${state.checkpoint}`);
    const encodeStarted = adapter.now();
    const encoded = encode(state);
    timings.encodeMs = elapsed(adapter.now, encodeStarted);
    memory.frontierAfterEncode = readFrontier(state);
    memory.scratchBytes = encoded.scratchBytes;
    memory.scratchAllocationCalls = encoded.scratchAllocationCalls;

    phase = "execute";
    const executeStarted = adapter.now();
    const physicalResult = u32(execute(state, encoded.argument));
    timings.executeMs = elapsed(adapter.now, executeStarted);
    memory.frontierAfterExecute = readFrontier(state);
    memory.peakFrontier = Math.max(memory.frontierAfterEncode,
      memory.frontierAfterExecute);

    phase = "decode";
    const decodeStarted = adapter.now();
    decoded = decodeLiveSelectionTransition(new DataView(state.memory.buffer),
      physicalResult, state.stateSlot, `${operation} result`);
    timings.decodeMs = elapsed(adapter.now, decodeStarted);
    phase = "done";
  } catch (error) {
    failure = errorMessage(error);
    if (phase === "execute" || phase === "decode") state.status = "poisoned";
  } finally {
    try {
      const rewound = rewind(state, state.checkpoint, adapter.now);
      timings.rewindMs = rewound.rewindMs;
      memory.frontierBeforeRewind = rewound.frontierBeforeRewind;
      memory.clearedBytes = rewound.clearedBytes;
      memory.postRewindFrontier = rewound.postRewindFrontier;
    } catch (error) {
      failure = errorMessage(error);
      state.status = "poisoned";
    }
  }
  memory.pagesAfter = state.memory?.buffer.byteLength / PAGE_BYTES;
  const totalMs = elapsed(adapter.now, totalStarted);
  const measured = Object.values(timings).reduce((sum, value) => sum + value, 0);
  const final = {
    timings: Object.freeze({
      ...timings,
      totalMs,
      overheadMs: totalMs - measured,
    }),
    memory: Object.freeze(memory),
  };
  if (failure !== undefined) {
    if (state.status === "poisoned") invalidatePlayer(state, "poisoned");
    return { ok: false, error: failure, ...final };
  }
  return { ok: true, ...decoded, ...final };
}

export class IlluminateSelectionPlayerAdapter {
  constructor({ module, manifest, build, now, startupTimings, maximumNodes }) {
    this.manifest = manifest;
    this.build = build;
    this.startupTimings = Object.freeze({ ...startupTimings });
    ADAPTER_STATE.set(this, {
      module,
      now,
      maximumNodes,
    });
  }

  createPlayer(animation) {
    const adapter = ADAPTER_STATE.get(this);
    requireCondition(adapter !== undefined, "invalid adapter receiver");
    const totalStarted = adapter.now();
    let state;
    let checkpoint;
    let result;
    let rewindResult = {
      rewindMs: 0,
      frontierBeforeRewind: undefined,
      clearedBytes: 0,
      postRewindFrontier: undefined,
    };
    const timings = {
      instantiateMs: 0,
      projectMs: 0,
      selectionEncodeMs: 0,
      stateSlotMs: 0,
      executeMs: 0,
      decodeMs: 0,
      rewindMs: 0,
    };
    const memory = {
      frontierBefore: undefined,
      frontierAfterSelection: undefined,
      persistentCheckpoint: undefined,
      peakFrontier: undefined,
      frontierBeforeRewind: undefined,
      clearedBytes: 0,
      postRewindFrontier: undefined,
      selectionBytes: 0,
      selectionObjectCount: 0,
      selectionAllocationCalls: 0,
      stateSlotBytes: 0,
      stateSlotObjectCount: 0,
      stateSlotAllocationCalls: 0,
      persistentObjectCount: 0,
      persistentAllocationCalls: 0,
      pagesBefore: undefined,
      pagesAfter: undefined,
    };
    try {
      state = instanceState(adapter.module, adapter.now, adapter.maximumNodes);
      timings.instantiateMs = state.instantiateMs;
      memory.frontierBefore = readFrontier(state);
      memory.pagesBefore = state.memory.buffer.byteLength / PAGE_BYTES;

      const projectStarted = adapter.now();
      const projectedAnimation = projectSelectionAnimation(animation);
      timings.projectMs = elapsed(adapter.now, projectStarted);

      const writer = new Encoder({ fir_heap_alloc: state.allocate },
        state.memory, state.encoder, { persistent: true });
      const encodeStarted = adapter.now();
      const selectionBytes = writer.selectionAnimationBytes(projectedAnimation);
      writer.reserve(selectionBytes, "persistent selection animation arena");
      const selectionAddress = writer.selectionAnimation(projectedAnimation);
      writer.finishReservation();
      timings.selectionEncodeMs = elapsed(adapter.now, encodeStarted);
      memory.frontierAfterSelection = readFrontier(state);
      memory.selectionBytes = writer.bytes;
      memory.selectionObjectCount = writer.objects;
      memory.selectionAllocationCalls = writer.allocations;
      const selectionAllocations = writer.allocations;

      const stateSlotStarted = adapter.now();
      const stateSlot = allocatePersistentStateSlot(writer);
      timings.stateSlotMs = elapsed(adapter.now, stateSlotStarted);
      checkpoint = readFrontier(state);
      memory.persistentCheckpoint = checkpoint;
      memory.stateSlotBytes = writer.bytes - memory.selectionBytes;
      memory.stateSlotObjectCount = writer.objects -
        memory.selectionObjectCount;
      memory.stateSlotAllocationCalls = writer.allocations -
        memory.selectionAllocationCalls;
      memory.persistentObjectCount = writer.objects;
      memory.persistentAllocationCalls = writer.allocations;

      const executeStarted = adapter.now();
      const physicalResult = u32(state.initialLive(i32(selectionAddress)));
      timings.executeMs = elapsed(adapter.now, executeStarted);
      memory.peakFrontier = readFrontier(state);

      const decodeStarted = adapter.now();
      result = decodeInitialResult(new DataView(state.memory.buffer),
        physicalResult, stateSlot, state.decoder, state.maximumNodes);
      timings.decodeMs = elapsed(adapter.now, decodeStarted);

      state.selectionAddress = selectionAddress;
      state.stateSlot = stateSlot;
      state.checkpoint = checkpoint;
      state.status = result.ok ? "active" : "rejected";
      state.selectionAllocations = selectionAllocations;
    } catch (error) {
      result = { ok: false, error: errorMessage(error) };
      if (state !== undefined) state.status = "rejected";
    } finally {
      if (state !== undefined && checkpoint !== undefined) {
        try {
          rewindResult = rewind(state, checkpoint, adapter.now);
        } catch (error) {
          result = { ok: false, error: errorMessage(error) };
          state.status = "poisoned";
        }
      }
    }
    timings.rewindMs = rewindResult.rewindMs;
    memory.postRewindFrontier = rewindResult.postRewindFrontier;
    memory.frontierBeforeRewind = rewindResult.frontierBeforeRewind;
    memory.clearedBytes = rewindResult.clearedBytes;
    memory.pagesAfter = state?.memory?.buffer.byteLength / PAGE_BYTES;
    const totalMs = elapsed(adapter.now, totalStarted);
    const measured = Object.values(timings).reduce((sum, value) => sum + value, 0);
    const finalTimings = Object.freeze({
      ...timings,
      totalMs,
      overheadMs: totalMs - measured,
    });
    const finalMemory = Object.freeze(memory);
    if (!result?.ok) {
      if (state !== undefined) invalidatePlayer(state, state.status ?? "rejected");
      return { ...result, timings: finalTimings, memory: finalMemory };
    }
    const player = Object.freeze({ [PLAYER]: this });
    state.owner = this;
    PLAYER_STATE.set(player, state);
    return {
      ok: true,
      player,
      action: result.action,
      scheduleNextFrame: result.scheduleNextFrame,
      timings: finalTimings,
      memory: finalMemory,
    };
  }

  dispatch(player, event) {
    return dispatchCore(this, player, "transitionSelectionLive", (state) => {
      const writer = new Encoder({ fir_heap_alloc: state.allocate },
        state.memory, state.encoder, { persistent: false });
      const eventAddress = writer.event(event, "event");
      return {
        argument: i32(eventAddress),
        scratchBytes: writer.bytes,
        scratchAllocationCalls: writer.allocations,
      };
    }, (state, eventAddress) => state.transitionLive(
        i32(state.selectionAddress), i32(state.stateSlot.stateAddress),
        eventAddress));
  }

  dispatchTick(player, timestamp) {
    return dispatchCore(this, player, "transitionSelectionTickLive",
      () => ({
        argument: float64Bits(timestamp, "timestamp"),
        scratchBytes: 0,
        scratchAllocationCalls: 0,
      }),
      (state, timestampBits) => state.transitionTickLiveBits(
        i32(state.selectionAddress), i32(state.stateSlot.stateAddress),
        timestampBits));
  }

  disposePlayer(player) {
    const state = PLAYER_STATE.get(player);
    requireCondition(player?.[PLAYER] === this && state?.owner === this,
      "disposePlayer requires this adapter's player handle");
    if (state.status === "disposed") return;
    invalidatePlayer(state, "disposed");
  }

  replayTrace(animation, events) {
    requireCondition(Array.isArray(events), "events must be an array");
    const adapter = ADAPTER_STATE.get(this);
    requireCondition(adapter !== undefined, "invalid adapter receiver");
    const started = adapter.now();
    const created = this.createPlayer(animation);
    if (!created.ok) return created;
    const actions = [created.action];
    const dispatches = [];
    let peakFrontier = created.memory.peakFrontier;
    try {
      for (const event of events) {
        const dispatched = this.dispatch(created.player, event);
        dispatches.push(dispatched);
        if (!dispatched.ok) return dispatched;
        actions.push(dispatched.action);
        peakFrontier = Math.max(peakFrontier,
          dispatched.memory.peakFrontier);
      }
      return {
        ok: true,
        actions,
        timings: {
          creation: created.timings,
          dispatches: dispatches.map((dispatch) => dispatch.timings),
          totalMs: elapsed(adapter.now, started),
        },
        memory: {
          creation: created.memory,
          dispatches: dispatches.map((dispatch) => dispatch.memory),
          persistentCheckpoint: created.memory.persistentCheckpoint,
          peakFrontier,
          postRewindFrontier: dispatches.at(-1)?.memory.postRewindFrontier ??
            created.memory.postRewindFrontier,
          dispatchCount: dispatches.length,
          reclamation: "player instance dropped by disposePlayer",
        },
      };
    } finally {
      this.disposePlayer(created.player);
    }
  }
}

export async function createIlluminateSelectionPlayerAdapter({
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
  return new IlluminateSelectionPlayerAdapter({
    module,
    manifest,
    build,
    now,
    maximumNodes,
    startupTimings: {
      fetchMs: startupTimings.fetchMs ?? 0,
      compileMs,
      totalMs: (startupTimings.fetchMs ?? 0) + compileMs,
    },
  });
}

function baseUrl() {
  return globalThis.location?.href ?? "file:///";
}

export async function fetchIlluminateSelectionPlayerAdapter(artifactUrl, {
  fetchImpl = globalThis.fetch,
  descriptorUrl,
  buildUrl,
  now = defaultNow,
  maximumNodes = 1_000_000,
} = {}) {
  requireCondition(typeof fetchImpl === "function",
    "fetchIlluminateSelectionPlayerAdapter requires fetch");
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
  return createIlluminateSelectionPlayerAdapter({
    bytes,
    manifest,
    build,
    now,
    maximumNodes,
    startupTimings: { fetchMs: elapsed(now, started) },
  });
}
