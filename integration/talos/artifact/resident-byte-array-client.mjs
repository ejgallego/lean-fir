const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const KIND_OPAQUE = 8;
const KIND_BYTE_ARRAY = 7;
const KIND_FREED = 255;
const LIVE = 2;
const LIVE_PERSISTENT = 3;
const ARRAY_MARKER = 0x41525259;
const BYTE_ARRAY_MARKER = 0x42595445;

function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function deepEqual(actual, expected, message) {
  expect(actual.length === expected.length &&
    actual.every((value, index) => value === expected[index]),
  `${message}: expected [${expected}], got [${actual}]`);
}

function align8(bytes) {
  return Math.ceil(bytes / 8) * 8;
}

function nat(value) {
  expect(Number.isInteger(value) && value >= 0 && value <= 0x3fffffff,
    `test Nat is out of immediate range: ${value}`);
  return 2 * value + 1;
}

function expectTrap(action, message) {
  let trapped = false;
  try {
    action();
  } catch (error) {
    trapped = error instanceof WebAssembly.RuntimeError;
  }
  expect(trapped, message);
}

function writeHeader(view, address, kind, allocation, aux0, aux1, aux2) {
  for (const [index, value] of [
    kind, LIVE_PERSISTENT, 0, allocation, aux0, aux1, aux2, 0,
  ].entries()) {
    view.setUint32(address + 4 * index, value, true);
  }
}

function encodeArray(exports, bytes) {
  const allocation = align8(HEADER_BYTES + SLOT_BYTES * bytes.length);
  const address = exports.fir_heap_alloc(allocation) >>> 0;
  const view = new DataView(exports.memory.buffer);
  writeHeader(view, address, KIND_OPAQUE, allocation,
    ARRAY_MARKER, bytes.length, bytes.length);
  bytes.forEach((byte, index) => {
    view.setUint32(address + HEADER_BYTES + SLOT_BYTES * index,
      2 * byte + 1, true);
    view.setUint32(address + HEADER_BYTES + SLOT_BYTES * index + 4, 0, true);
  });
  return address;
}

function decodeByteArray(exports, address) {
  const view = new DataView(exports.memory.buffer);
  equal(view.getUint32(address, true), KIND_BYTE_ARRAY,
    "ByteArray kind");
  const flags = view.getUint32(address + 4, true);
  const refCount = view.getUint32(address + 8, true);
  expect(flags === LIVE || flags === LIVE_PERSISTENT,
    `ByteArray flags: expected ${LIVE} or ${LIVE_PERSISTENT}, got ${flags}`);
  if (flags === LIVE_PERSISTENT) {
    equal(refCount, 0, "persistent ByteArray reference count");
  } else {
    expect(refCount > 0, "ordinary ByteArray has zero references");
  }
  equal(view.getUint32(address + 16, true), BYTE_ARRAY_MARKER,
    "ByteArray marker");
  equal(view.getUint32(address + 28, true), 0, "ByteArray reserved metadata");
  const size = view.getUint32(address + 20, true);
  const capacity = view.getUint32(address + 24, true);
  expect(size <= capacity, "ByteArray size exceeds capacity");
  equal(view.getUint32(address + 12, true), align8(HEADER_BYTES + capacity),
    "ByteArray allocation size");
  return {
    flags,
    refCount,
    size,
    capacity,
    bytes: [...new Uint8Array(exports.memory.buffer, address + HEADER_BYTES, size)],
  };
}

/** Exercise the packed module-owned ByteArray runtime without host imports. */
export async function checkResidentByteArray(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident ByteArray module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  for (const name of [
    "fir_heap_alloc",
    "fir_heap_frontier",
    "fir_ext_ByteArray_copySlice",
    "fir_ext_ByteArray_size",
    "fir_ext_ByteArray_mk",
    "fir_ext_ByteArray_emptyWithCapacity",
  ]) {
    equal(typeof exports[name], "function", `missing export ${name}`);
  }

  const sourceBytes = [0, 1, 127, 128, 255];
  const sourceArray = encodeArray(exports, sourceBytes);
  const source = exports.fir_ext_ByteArray_mk(sourceArray) >>> 0;
  const decodedSource = decodeByteArray(exports, source);
  deepEqual(decodedSource.bytes, sourceBytes, "ByteArray.mk bytes");
  equal(decodedSource.capacity, sourceBytes.length, "ByteArray.mk capacity");
  equal(exports.fir_ext_ByteArray_size(source) >>> 0,
    nat(sourceBytes.length), "ByteArray.size tagged result");

  const makeByteArray = (bytes) =>
    exports.fir_ext_ByteArray_mk(encodeArray(exports, bytes)) >>> 0;

  const empty = exports.fir_ext_ByteArray_emptyWithCapacity(nat(10)) >>> 0;
  const decodedEmpty = decodeByteArray(exports, empty);
  equal(decodedEmpty.size, 0, "emptyWithCapacity size");
  equal(decodedEmpty.capacity, 10, "emptyWithCapacity capacity");

  const uniqueDestination =
    exports.fir_ext_ByteArray_emptyWithCapacity(nat(10)) >>> 0;
  const uniqueView = new DataView(exports.memory.buffer);
  equal(uniqueView.getUint32(uniqueDestination + 4, true), LIVE,
    "emptyWithCapacity unique flags");
  equal(uniqueView.getUint32(uniqueDestination + 8, true), 1,
    "emptyWithCapacity unique reference count");
  const uniqueFrontier = exports.fir_heap_frontier() >>> 0;
  const uniqueResult = exports.fir_ext_ByteArray_copySlice(
    source, nat(0), uniqueDestination, nat(0), nat(2), 1) >>> 0;
  equal(uniqueResult, uniqueDestination,
    "copySlice did not preserve an exclusive destination");
  equal(exports.fir_heap_frontier() >>> 0, uniqueFrontier,
    "copySlice allocated despite sufficient exclusive capacity");
  deepEqual(decodeByteArray(exports, uniqueResult).bytes, [0, 1],
    "copySlice exclusive bytes");

  const src = exports.fir_ext_ByteArray_mk(
    encodeArray(exports, [9, 8, 7, 6])) >>> 0;
  const exactDestination = makeByteArray([1, 2, 3]);
  const exact = exports.fir_ext_ByteArray_copySlice(
    src, nat(1), exactDestination, nat(2), nat(9), 1) >>> 0;
  const decodedExact = decodeByteArray(exports, exact);
  deepEqual(decodedExact.bytes, [1, 2, 8, 7, 6], "copySlice exact bytes");
  equal(decodedExact.capacity, 5, "copySlice exact capacity");
  expect(exact !== exactDestination,
    "copySlice retained a destination that required growth");
  equal(new DataView(exports.memory.buffer).getUint32(exactDestination, true),
    KIND_FREED, "copySlice did not consume grown exclusive destination");

  const geometricDestination = makeByteArray([1, 2, 3]);
  const geometric = exports.fir_ext_ByteArray_copySlice(
    src, nat(1), geometricDestination, nat(2), nat(9), 0) >>> 0;
  const decodedGeometric = decodeByteArray(exports, geometric);
  deepEqual(decodedGeometric.bytes, decodedExact.bytes,
    "copySlice geometric bytes");
  equal(decodedGeometric.capacity, 10, "copySlice geometric capacity");

  const roomySource = makeByteArray([1, 2, 3]);
  const roomy = exports.fir_ext_ByteArray_copySlice(
    roomySource, nat(0), empty, nat(0), nat(3), 1) >>> 0;
  const decodedRoomy = decodeByteArray(exports, roomy);
  deepEqual(decodedRoomy.bytes, [1, 2, 3], "copySlice retained capacity bytes");
  equal(decodedRoomy.capacity, 10, "copySlice retained capacity");
  equal(roomy, empty, "copySlice failed to reuse roomy exclusive destination");

  const clampedDestination = makeByteArray([1, 2, 3]);
  const clamped = exports.fir_ext_ByteArray_copySlice(
    src, nat(0), clampedDestination, nat(99), nat(2), 1) >>> 0;
  deepEqual(decodeByteArray(exports, clamped).bytes, [1, 2, 3, 9, 8],
    "copySlice destination offset clamp");

  const unchangedDestination = makeByteArray([1, 2, 3]);
  const unchanged = exports.fir_ext_ByteArray_copySlice(
    src, nat(99), unchangedDestination, nat(0), nat(1), 1) >>> 0;
  equal(unchanged, unchangedDestination,
    "copySlice past-source result identity");

  const sharedDestination = makeByteArray([1, 2, 3]);
  const sharedView = new DataView(exports.memory.buffer);
  sharedView.setUint32(sharedDestination + 8, 2, true);
  const sharedResult = exports.fir_ext_ByteArray_copySlice(
    src, nat(0), sharedDestination, nat(0), nat(2), 1) >>> 0;
  expect(sharedResult !== sharedDestination,
    "copySlice mutated a shared destination");
  const decodedSharedOriginal = decodeByteArray(exports, sharedDestination);
  equal(decodedSharedOriginal.refCount, 1,
    "copySlice did not consume one shared destination reference");
  deepEqual(decodedSharedOriginal.bytes, [1, 2, 3],
    "copySlice mutated the remaining shared alias");
  deepEqual(decodeByteArray(exports, sharedResult).bytes, [9, 8, 3],
    "copySlice shared copy bytes");

  const persistentDestination = makeByteArray([1, 2, 3]);
  const persistentView = new DataView(exports.memory.buffer);
  persistentView.setUint32(persistentDestination + 4, LIVE_PERSISTENT, true);
  persistentView.setUint32(persistentDestination + 8, 0, true);
  const persistentResult = exports.fir_ext_ByteArray_copySlice(
    src, nat(0), persistentDestination, nat(0), nat(2), 1) >>> 0;
  expect(persistentResult !== persistentDestination,
    "copySlice mutated a persistent destination");
  deepEqual(decodeByteArray(exports, persistentDestination).bytes, [1, 2, 3],
    "copySlice mutated persistent input");
  deepEqual(decodeByteArray(exports, persistentResult).bytes, [9, 8, 3],
    "copySlice persistent copy bytes");

  const malformedArray = encodeArray(exports, [0]);
  new DataView(exports.memory.buffer).setUint32(
    malformedArray + HEADER_BYTES, nat(256), true);
  expectTrap(() => exports.fir_ext_ByteArray_mk(malformedArray),
    "ByteArray.mk accepted an out-of-range UInt8 element");

  const frontier = exports.fir_heap_frontier() >>> 0;
  expect(frontier > 1024, "ByteArray checks did not advance the resident frontier");
  return "PASS zero-import resident packed ByteArrays";
}

export async function checkFetchedResidentByteArray(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentByteArray(await response.arrayBuffer());
}
