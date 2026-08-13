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

function writeHeader(view, address, kind, allocation, aux0, aux1, aux2,
    flags = LIVE_PERSISTENT, refCount = 0) {
  for (const [index, value] of [
    kind, flags, refCount, allocation, aux0, aux1, aux2, 0,
  ].entries()) {
    view.setUint32(address + 4 * index, value, true);
  }
}

function encodeArray(exports, bytes, { persistent = true } = {}) {
  const allocation = align8(HEADER_BYTES + SLOT_BYTES * bytes.length);
  const address = exports.fir_heap_alloc(allocation) >>> 0;
  const view = new DataView(exports.memory.buffer);
  writeHeader(view, address, KIND_OPAQUE, allocation,
    ARRAY_MARKER, bytes.length, bytes.length,
    persistent ? LIVE_PERSISTENT : LIVE, persistent ? 0 : 1);
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
    "fir_ext_ByteArray_get",
    "fir_ext_ByteArray_uget",
    "fir_ext_ByteArray_ugetUInt32LE",
    "fir_ext_ByteArray_ugetUInt64LE",
    "fir_ext_ByteArray_usetUInt32LE",
    "fir_ext_ByteArray_usetUInt64LE",
    "fir_ext_ByteArray_push",
    "fir_ext_ByteArray_pushUInt64LE",
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

  const liveSourceArray = encodeArray(
    exports, [3, 2, 1], { persistent: false });
  const liveSource = exports.fir_ext_ByteArray_mk(liveSourceArray) >>> 0;
  deepEqual(decodeByteArray(exports, liveSource).bytes, [3, 2, 1],
    "ByteArray.mk live Array bytes");
  equal(new DataView(exports.memory.buffer).getUint32(liveSourceArray, true),
    KIND_FREED, "ByteArray.mk did not consume its exclusive Array input");

  const sharedSourceArray = encodeArray(
    exports, [4, 5], { persistent: false });
  new DataView(exports.memory.buffer).setUint32(
    sharedSourceArray + 8, 2, true);
  const sharedSource = exports.fir_ext_ByteArray_mk(sharedSourceArray) >>> 0;
  deepEqual(decodeByteArray(exports, sharedSource).bytes, [4, 5],
    "ByteArray.mk shared Array bytes");
  equal(new DataView(exports.memory.buffer).getUint32(
    sharedSourceArray + 8, true), 1,
  "ByteArray.mk did not consume one shared Array reference");

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

  const sharedPastSource = makeByteArray([1, 2, 3]);
  new DataView(exports.memory.buffer).setUint32(
    sharedPastSource + 8, 2, true);
  const sharedPastSourceResult = exports.fir_ext_ByteArray_copySlice(
    src, nat(99), sharedPastSource, nat(0), nat(1), 1) >>> 0;
  equal(sharedPastSourceResult, sharedPastSource,
    "copySlice past-source changed shared destination identity");
  equal(decodeByteArray(exports, sharedPastSource).refCount, 2,
    "copySlice past-source changed shared destination ownership");

  const sharedEmptySlice = makeByteArray([1, 2, 3]);
  new DataView(exports.memory.buffer).setUint32(
    sharedEmptySlice + 8, 2, true);
  const sharedEmptySliceResult = exports.fir_ext_ByteArray_copySlice(
    src, nat(4), sharedEmptySlice, nat(0), nat(7), 1) >>> 0;
  expect(sharedEmptySliceResult !== sharedEmptySlice,
    "copySlice retained a shared destination for an in-range empty slice");
  equal(decodeByteArray(exports, sharedEmptySlice).refCount, 1,
    "copySlice empty slice did not consume one shared destination reference");
  deepEqual(decodeByteArray(exports, sharedEmptySliceResult).bytes,
    [1, 2, 3], "copySlice in-range empty-slice contents");

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

  equal(exports.fir_ext_ByteArray_get(source, nat(4)) >>> 0, 255,
    "ByteArray.get last byte");
  equal(exports.fir_ext_ByteArray_uget(source, 3n) >>> 0, 128,
    "ByteArray.uget byte");
  expectTrap(() => exports.fir_ext_ByteArray_get(source, nat(5)),
    "ByteArray.get accepted its upper bound");
  expectTrap(() => exports.fir_ext_ByteArray_uget(source, 5n),
    "ByteArray.uget accepted its upper bound");

  const wide = makeByteArray([
    0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01, 0xde,
  ]);
  equal(exports.fir_ext_ByteArray_ugetUInt32LE(wide, 1n) >>> 0,
    0x6789abcd, "ByteArray.ugetUInt32LE unaligned bits");
  equal(BigInt.asUintN(64,
    exports.fir_ext_ByteArray_ugetUInt64LE(wide, 0n)),
  0x0123456789abcdefn, "ByteArray.ugetUInt64LE bits");
  expectTrap(() => exports.fir_ext_ByteArray_ugetUInt32LE(wide, 6n),
    "ByteArray.ugetUInt32LE accepted an incomplete word");
  expectTrap(() => exports.fir_ext_ByteArray_ugetUInt64LE(wide, 2n),
    "ByteArray.ugetUInt64LE accepted an incomplete word");

  const set32 = makeByteArray([0, 1, 2, 3, 4, 5, 6, 7]);
  const set32Frontier = exports.fir_heap_frontier() >>> 0;
  const set32Result = exports.fir_ext_ByteArray_usetUInt32LE(
    set32, 2n, 0x89abcdef) >>> 0;
  equal(set32Result, set32, "exclusive usetUInt32LE identity");
  equal(exports.fir_heap_frontier() >>> 0, set32Frontier,
    "exclusive usetUInt32LE allocated");
  deepEqual(decodeByteArray(exports, set32).bytes,
    [0, 1, 0xef, 0xcd, 0xab, 0x89, 6, 7],
  "exclusive usetUInt32LE bytes");

  const set64Shared = makeByteArray([0, 1, 2, 3, 4, 5, 6, 7, 8]);
  const set64SharedView = new DataView(exports.memory.buffer);
  set64SharedView.setUint32(set64Shared + 8, 2, true);
  const set64Result = exports.fir_ext_ByteArray_usetUInt64LE(
    set64Shared, 1n, 0x0123456789abcdefn) >>> 0;
  expect(set64Result !== set64Shared,
    "shared usetUInt64LE reused its input");
  equal(decodeByteArray(exports, set64Shared).refCount, 1,
    "shared usetUInt64LE did not consume one reference");
  deepEqual(decodeByteArray(exports, set64Shared).bytes,
    [0, 1, 2, 3, 4, 5, 6, 7, 8],
  "shared usetUInt64LE mutated its alias");
  deepEqual(decodeByteArray(exports, set64Result).bytes,
    [0, 0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01],
  "shared usetUInt64LE copied bytes");

  const set32Persistent = makeByteArray([0, 1, 2, 3, 4]);
  const set32PersistentView = new DataView(exports.memory.buffer);
  set32PersistentView.setUint32(
    set32Persistent + 4, LIVE_PERSISTENT, true);
  set32PersistentView.setUint32(set32Persistent + 8, 0, true);
  const set32PersistentResult = exports.fir_ext_ByteArray_usetUInt32LE(
    set32Persistent, 1n, 0x89abcdef) >>> 0;
  expect(set32PersistentResult !== set32Persistent,
    "persistent usetUInt32LE reused its input");
  deepEqual(decodeByteArray(exports, set32Persistent).bytes,
    [0, 1, 2, 3, 4], "persistent usetUInt32LE mutated its input");
  deepEqual(decodeByteArray(exports, set32PersistentResult).bytes,
    [0, 0xef, 0xcd, 0xab, 0x89],
  "persistent usetUInt32LE copied bytes");
  expectTrap(() => exports.fir_ext_ByteArray_usetUInt32LE(
    set32, 5n, 0), "usetUInt32LE accepted an incomplete destination");

  const pushRoomy = exports.fir_ext_ByteArray_emptyWithCapacity(nat(8)) >>> 0;
  const pushSeed = makeByteArray([1, 2, 3]);
  const pushPrepared = exports.fir_ext_ByteArray_copySlice(
    pushSeed, nat(0), pushRoomy, nat(0), nat(3), 1) >>> 0;
  equal(pushPrepared, pushRoomy, "push roomy preparation identity");
  const pushFrontier = exports.fir_heap_frontier() >>> 0;
  const pushed = exports.fir_ext_ByteArray_push(pushPrepared, 0xfe) >>> 0;
  equal(pushed, pushPrepared, "exclusive ByteArray.push identity");
  equal(exports.fir_heap_frontier() >>> 0, pushFrontier,
    "exclusive ByteArray.push allocated despite capacity");
  deepEqual(decodeByteArray(exports, pushed).bytes, [1, 2, 3, 0xfe],
    "ByteArray.push bytes");

  const pushGrowthInput = makeByteArray([4, 5]);
  const pushGrowth = exports.fir_ext_ByteArray_push(
    pushGrowthInput, 6) >>> 0;
  expect(pushGrowth !== pushGrowthInput,
    "ByteArray.push failed to replace a full input");
  equal(new DataView(exports.memory.buffer).getUint32(
    pushGrowthInput, true), KIND_FREED,
  "ByteArray.push did not consume a grown exclusive input");
  const decodedPushGrowth = decodeByteArray(exports, pushGrowth);
  deepEqual(decodedPushGrowth.bytes, [4, 5, 6],
    "ByteArray.push growth bytes");
  equal(decodedPushGrowth.capacity, 6, "ByteArray.push growth capacity");

  const pushShared = makeByteArray([7, 8]);
  new DataView(exports.memory.buffer).setUint32(pushShared + 8, 2, true);
  const pushSharedResult = exports.fir_ext_ByteArray_push(
    pushShared, 9) >>> 0;
  expect(pushSharedResult !== pushShared,
    "ByteArray.push reused a shared input");
  equal(decodeByteArray(exports, pushShared).refCount, 1,
    "ByteArray.push did not consume one shared reference");
  deepEqual(decodeByteArray(exports, pushShared).bytes, [7, 8],
    "ByteArray.push mutated a shared alias");
  deepEqual(decodeByteArray(exports, pushSharedResult).bytes, [7, 8, 9],
    "ByteArray.push shared result");

  const pushPersistent = makeByteArray([10, 11]);
  const pushPersistentView = new DataView(exports.memory.buffer);
  pushPersistentView.setUint32(pushPersistent + 4, LIVE_PERSISTENT, true);
  pushPersistentView.setUint32(pushPersistent + 8, 0, true);
  const pushPersistentResult = exports.fir_ext_ByteArray_push(
    pushPersistent, 12) >>> 0;
  expect(pushPersistentResult !== pushPersistent,
    "ByteArray.push reused a persistent input");
  deepEqual(decodeByteArray(exports, pushPersistent).bytes, [10, 11],
    "ByteArray.push mutated a persistent input");
  deepEqual(decodeByteArray(exports, pushPersistentResult).bytes,
    [10, 11, 12], "ByteArray.push persistent result");

  const pushWide = exports.fir_ext_ByteArray_emptyWithCapacity(nat(16)) >>> 0;
  const zeroWideFrontier = exports.fir_heap_frontier() >>> 0;
  const zeroWide = exports.fir_ext_ByteArray_pushUInt64LE(
    pushWide, 0xffffffffffffffffn, 0n) >>> 0;
  equal(zeroWide, pushWide, "pushUInt64LE zero-count identity");
  equal(exports.fir_heap_frontier() >>> 0, zeroWideFrontier,
    "pushUInt64LE zero-count allocated");

  const zeroWideShared = makeByteArray([0x44]);
  new DataView(exports.memory.buffer).setUint32(
    zeroWideShared + 8, 2, true);
  const zeroWideSharedResult = exports.fir_ext_ByteArray_pushUInt64LE(
    zeroWideShared, 0xffffffffffffffffn, 0n) >>> 0;
  equal(zeroWideSharedResult, zeroWideShared,
    "pushUInt64LE zero-count changed shared identity");
  equal(decodeByteArray(exports, zeroWideShared).refCount, 2,
    "pushUInt64LE zero-count changed shared ownership");

  const oneWideShared = exports.fir_ext_ByteArray_pushUInt64LE(
    zeroWideShared, 0xaan, 1n) >>> 0;
  expect(oneWideShared !== zeroWideShared,
    "pushUInt64LE nonempty append reused a shared input");
  equal(decodeByteArray(exports, zeroWideShared).refCount, 1,
    "pushUInt64LE nonempty append did not consume one shared reference");
  deepEqual(decodeByteArray(exports, oneWideShared).bytes, [0x44, 0xaa],
    "pushUInt64LE shared append bytes");
  const pushedWide = exports.fir_ext_ByteArray_pushUInt64LE(
    zeroWide, 0x0123456789abcdefn, 8n) >>> 0;
  equal(pushedWide, pushWide, "exclusive pushUInt64LE identity");
  deepEqual(decodeByteArray(exports, pushedWide).bytes,
    [0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01],
  "pushUInt64LE bytes");
  expectTrap(() => exports.fir_ext_ByteArray_pushUInt64LE(
    pushedWide, 0n, 9n), "pushUInt64LE accepted a count above eight");

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
