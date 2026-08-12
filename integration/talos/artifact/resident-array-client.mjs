function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function expectTrap(action, label) {
  let trapped = false;
  try {
    action();
  } catch (error) {
    trapped = error instanceof WebAssembly.RuntimeError;
  }
  expect(trapped, `${label} did not trap`);
}

function immediateNatural(value) {
  return 2 * value + 1;
}

const KIND_OPAQUE = 8;
const KIND_CONSTRUCTOR = 1;
const KIND_FREED = 255;
const LIVE = 2;
const LIVE_PERSISTENT = 3;

function arrayState(memory, address) {
  const view = new DataView(memory.buffer);
  equal(view.getUint32(address, true), KIND_OPAQUE, "array object kind");
  const flags = view.getUint32(address + 4, true);
  const refCount = view.getUint32(address + 8, true);
  expect(flags === LIVE || flags === LIVE_PERSISTENT,
    `array flags: expected ${LIVE} or ${LIVE_PERSISTENT}, got ${flags}`);
  if (flags === LIVE) {
    expect(refCount > 0, "ordinary array has zero references");
  } else {
    equal(refCount, 0, "persistent array reference count");
  }
  equal(view.getUint32(address + 16, true), 0x41525259, "array marker");
  const size = view.getUint32(address + 20, true);
  const capacity = view.getUint32(address + 24, true);
  expect(size <= capacity, "array size exceeds capacity");
  equal(view.getUint32(address + 12, true), 32 + 8 * capacity,
    "array allocation size");
  return {
    flags,
    refCount,
    size,
    capacity,
    words: Array.from({ length: size }, (_, index) =>
      view.getUint32(address + 32 + 8 * index, true)),
  };
}

function heapObjectState(memory, address) {
  const view = new DataView(memory.buffer);
  return {
    kind: view.getUint32(address, true),
    flags: view.getUint32(address + 4, true),
    refCount: view.getUint32(address + 8, true),
  };
}

function listState(memory, root) {
  const view = new DataView(memory.buffer);
  const addresses = [];
  const words = [];
  let cursor = root;
  while (cursor !== 1) {
    expect(addresses.length < 10000, "resident List appears cyclic");
    equal(cursor & 7, 0, "List.cons alignment");
    equal(view.getUint32(cursor, true), KIND_CONSTRUCTOR,
      "List.cons object kind");
    equal(view.getUint32(cursor + 4, true), LIVE, "List.cons flags");
    expect(view.getUint32(cursor + 8, true) > 0,
      "List.cons reference count");
    equal(view.getUint32(cursor + 12, true), 48,
      "List.cons allocation bytes");
    equal(view.getUint32(cursor + 16, true), 1, "List.cons tag");
    equal(view.getUint32(cursor + 20, true), 2,
      "List.cons object-field count");
    equal(view.getUint32(cursor + 24, true), 0,
      "List.cons usize-field count");
    equal(view.getUint32(cursor + 28, true), 0,
      "List.cons scalar byte count");
    addresses.push(cursor);
    words.push(view.getUint32(cursor + 32, true));
    cursor = view.getUint32(cursor + 40, true);
  }
  return { addresses, words };
}

function allocateOwnedOpaque(exports) {
  const address = exports.fir_heap_alloc(32);
  const view = new DataView(exports.memory.buffer);
  view.setUint32(address, KIND_OPAQUE, true);
  view.setUint32(address + 4, LIVE, true);
  view.setUint32(address + 8, 1, true);
  view.setUint32(address + 12, 32, true);
  for (let offset = 16; offset < 32; offset += 4) {
    view.setUint32(address + offset, 0, true);
  }
  return address;
}

/** Check the zero-import resident Array.uget/uset/replicate/pop frontier. */
export async function checkResidentArrays(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident array module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident array memory export is missing");
  const replicate = exports.fir_ext_Array_replicate;
  const emptyWithCapacity = exports.fir_ext_Array_emptyWithCapacity;
  const push = exports.fir_ext_Array_push;
  const uget = exports.fir_ext_Array_uget;
  const uset = exports.fir_ext_Array_uset;
  const getInternal = exports.fir_ext_Array_getInternal;
  const set = exports.fir_ext_Array_set;
  const setBang = exports["fir_ext_Array_set!"];
  const swap = exports.fir_ext_Array_swap;
  const pop = exports.fir_ext_Array_pop;
  const arrayMk = exports.fir_ext_Array_mk;
  const arrayToList = exports.fir_ext_Array_toList;
  const allocateListCons = exports.fir_array_allocate_list_cons;
  const release = exports.resident_array_release;
  equal(typeof emptyWithCapacity, "function", "Array.emptyWithCapacity export");
  equal(typeof push, "function", "Array.push export");
  equal(typeof replicate, "function", "Array.replicate export");
  equal(typeof uget, "function", "Array.uget export");
  equal(typeof uset, "function", "Array.uset export");
  equal(typeof getInternal, "function", "Array.getInternal export");
  equal(typeof set, "function", "Array.set export");
  equal(typeof setBang, "function", "Array.set! export");
  equal(typeof swap, "function", "Array.swap export");
  equal(typeof pop, "function", "Array.pop export");
  equal(typeof arrayMk, "function", "Array.mk export");
  equal(typeof arrayToList, "function", "Array.toList export");
  equal(typeof allocateListCons, "function",
    "resident List.cons allocator export");
  equal(typeof release, "function", "array release export");

  let inputList = 1;
  const inputListAddresses = [];
  for (const value of [3, 2, 1]) {
    inputList = allocateListCons(immediateNatural(value), inputList);
    inputListAddresses.push(inputList);
  }
  equal(listState(exports.memory, inputList).words.join(","),
    [1, 2, 3].map(immediateNatural).join(","),
    "List.cons standalone construction");
  const convertedArray = arrayMk(0, inputList);
  equal(arrayState(exports.memory, convertedArray).words.join(","),
    [1, 2, 3].map(immediateNatural).join(","), "Array.mk ordering");
  for (const address of inputListAddresses) {
    equal(heapObjectState(exports.memory, address).kind, KIND_FREED,
      "Array.mk did not consume a unique List node");
  }
  const convertedList = arrayToList(0, convertedArray);
  equal(heapObjectState(exports.memory, convertedArray).kind, KIND_FREED,
    "Array.toList did not consume its unique Array");
  const convertedListState = listState(exports.memory, convertedList);
  equal(convertedListState.words.join(","),
    [1, 2, 3].map(immediateNatural).join(","), "Array.toList ordering");
  release(convertedList);
  for (const address of convertedListState.addresses) {
    equal(heapObjectState(exports.memory, address).kind, KIND_FREED,
      "released Array.toList node remained live");
  }

  const emptyFromList = arrayMk(0, 1);
  equal(arrayState(exports.memory, emptyFromList).size, 0,
    "Array.mk empty size");
  equal(arrayToList(0, emptyFromList), 1, "Array.toList empty result");
  equal(heapObjectState(exports.memory, emptyFromList).kind, KIND_FREED,
    "Array.toList empty did not consume its Array");
  expectTrap(() => arrayMk(0, 3), "Array.mk malformed immediate List");

  const sharedListChild = allocateOwnedOpaque(exports);
  const sharedList = allocateListCons(sharedListChild, 1);
  new DataView(exports.memory.buffer).setUint32(sharedList + 8, 2, true);
  const sharedListArray = arrayMk(0, sharedList);
  equal(heapObjectState(exports.memory, sharedList).refCount, 1,
    "Array.mk did not consume one shared List reference");
  equal(heapObjectState(exports.memory, sharedListChild).refCount, 2,
    "Array.mk did not retain a shared List element");
  release(sharedListArray);
  equal(heapObjectState(exports.memory, sharedListChild).refCount, 1,
    "Array.mk shared element did not survive its Array release");
  release(sharedList);
  equal(heapObjectState(exports.memory, sharedListChild).kind, KIND_FREED,
    "Array.mk shared element remained live after final List release");

  const persistentList = allocateListCons(immediateNatural(17), 1);
  const persistentListView = new DataView(exports.memory.buffer);
  persistentListView.setUint32(persistentList + 4, LIVE_PERSISTENT, true);
  persistentListView.setUint32(persistentList + 8, 0, true);
  const persistentListArray = arrayMk(0, persistentList);
  equal(arrayState(exports.memory, persistentListArray).words[0],
    immediateNatural(17), "Array.mk persistent List element");
  equal(heapObjectState(exports.memory, persistentList).kind, KIND_CONSTRUCTOR,
    "Array.mk retired a persistent List");
  release(persistentListArray);

  const sharedArrayChild = allocateOwnedOpaque(exports);
  const sharedArray = replicate(0, immediateNatural(1), sharedArrayChild);
  new DataView(exports.memory.buffer).setUint32(sharedArray + 8, 2, true);
  const sharedArrayList = arrayToList(0, sharedArray);
  equal(heapObjectState(exports.memory, sharedArray).refCount, 1,
    "Array.toList did not consume one shared Array reference");
  equal(heapObjectState(exports.memory, sharedArrayChild).refCount, 2,
    "Array.toList did not retain a shared Array element");
  release(sharedArrayList);
  equal(heapObjectState(exports.memory, sharedArrayChild).refCount, 1,
    "Array.toList element did not survive its List release");
  release(sharedArray);
  equal(heapObjectState(exports.memory, sharedArrayChild).kind, KIND_FREED,
    "Array.toList element remained live after final Array release");

  const persistentArray = replicate(
    0, immediateNatural(1), immediateNatural(23));
  const persistentArrayView = new DataView(exports.memory.buffer);
  persistentArrayView.setUint32(persistentArray + 4, LIVE_PERSISTENT, true);
  persistentArrayView.setUint32(persistentArray + 8, 0, true);
  const persistentArrayList = arrayToList(0, persistentArray);
  equal(listState(exports.memory, persistentArrayList).words[0],
    immediateNatural(23), "Array.toList persistent Array element");
  equal(heapObjectState(exports.memory, persistentArray).kind, KIND_OPAQUE,
    "Array.toList retired a persistent Array");
  release(persistentArrayList);

  const value = immediateNatural(21);
  const replacement = immediateNatural(49);
  let roomy = emptyWithCapacity(0, immediateNatural(4));
  const roomyInitial = arrayState(exports.memory, roomy);
  equal(roomyInitial.flags, LIVE, "emptyWithCapacity unique flags");
  equal(roomyInitial.refCount, 1,
    "emptyWithCapacity unique reference count");
  equal(roomyInitial.size, 0, "emptyWithCapacity size");
  equal(roomyInitial.capacity, 4, "emptyWithCapacity capacity");
  const roomyFrontier = exports.fir_heap_frontier();
  for (let index = 0; index < 4; index += 1) {
    const pushed = push(0, roomy, immediateNatural(index + 1));
    equal(pushed, roomy, `Array.push exclusive identity ${index}`);
    roomy = pushed;
  }
  equal(exports.fir_heap_frontier(), roomyFrontier,
    "Array.push allocated within exclusive capacity");
  equal(arrayState(exports.memory, roomy).words.join(","),
    [1, 2, 3, 4].map(immediateNatural).join(","),
    "Array.push exclusive elements");
  const grown = push(0, roomy, immediateNatural(5));
  expect(grown !== roomy, "Array.push retained a full array");
  const grownState = arrayState(exports.memory, grown);
  equal(grownState.capacity, 10, "Array.push geometric capacity");
  equal(grownState.words.join(","),
    [1, 2, 3, 4, 5].map(immediateNatural).join(","),
    "Array.push grown elements");
  equal(new DataView(exports.memory.buffer).getUint32(roomy, true), KIND_FREED,
    "Array.push did not consume the grown exclusive input");

  const original = replicate(0, immediateNatural(3), value);
  expect(original >= 1024 && original % 8 === 0,
    "Array.replicate returned an invalid address");
  const originalState = arrayState(exports.memory, original);
  equal(originalState.flags, LIVE, "Array.replicate unique flags");
  equal(originalState.refCount, 1, "Array.replicate unique reference count");
  expect(originalState.words.every((word) => word === value),
    "Array.replicate did not fill every element");
  equal(uget(0, original, 1n, 0), value, "Array.uget middle element");

  const updated = uset(0, original, 1n, replacement, 0);
  equal(updated, original, "Array.uset did not reuse its exclusive input");
  expect(arrayState(exports.memory, updated).words.join(",") ===
    [value, replacement, value].join(","),
    "Array.uset replaced the wrong element");
  equal(uget(0, updated, 1n, 0), replacement,
    "Array.uget updated element");

  const popped = pop(0, updated);
  equal(popped, updated, "Array.pop did not reuse its exclusive input");
  expect(arrayState(exports.memory, popped).words.join(",") ===
    [value, replacement].join(","),
    "Array.pop retained the wrong prefix");

  const shared = replicate(0, immediateNatural(3), value);
  const sharedView = new DataView(exports.memory.buffer);
  sharedView.setUint32(shared + 8, 2, true);
  const sharedUpdated = uset(0, shared, 1n, replacement, 0);
  expect(sharedUpdated !== shared, "Array.uset mutated a shared input");
  equal(arrayState(exports.memory, shared).refCount, 1,
    "Array.uset did not consume one shared input reference");
  equal(arrayState(exports.memory, shared).words.join(","),
    [value, value, value].join(","), "Array.uset mutated a shared alias");
  equal(arrayState(exports.memory, sharedUpdated).words.join(","),
    [value, replacement, value].join(","), "Array.uset shared copy");

  const persistent = replicate(0, immediateNatural(3), value);
  const persistentView = new DataView(exports.memory.buffer);
  persistentView.setUint32(persistent + 4, LIVE_PERSISTENT, true);
  persistentView.setUint32(persistent + 8, 0, true);
  const persistentUpdated = uset(0, persistent, 1n, replacement, 0);
  expect(persistentUpdated !== persistent,
    "Array.uset mutated a persistent input");
  equal(arrayState(exports.memory, persistent).words.join(","),
    [value, value, value].join(","), "Array.uset mutated persistent input");
  equal(arrayState(exports.memory, persistentUpdated).words.join(","),
    [value, replacement, value].join(","), "Array.uset persistent copy");

  const sharedPopInput = replicate(0, immediateNatural(3), value);
  const sharedPopView = new DataView(exports.memory.buffer);
  sharedPopView.setUint32(sharedPopInput + 8, 2, true);
  const sharedPopped = pop(0, sharedPopInput);
  expect(sharedPopped !== sharedPopInput, "Array.pop mutated a shared input");
  equal(arrayState(exports.memory, sharedPopInput).refCount, 1,
    "Array.pop did not consume one shared input reference");
  equal(arrayState(exports.memory, sharedPopInput).size, 3,
    "Array.pop mutated a shared alias");
  equal(arrayState(exports.memory, sharedPopped).size, 2,
    "Array.pop shared copy size");

  const empty = replicate(0, immediateNatural(0), value);
  expect(arrayState(exports.memory, empty).words.length === 0,
    "Array.replicate zero did not create an empty array");
  equal(pop(0, empty), empty, "Array.pop empty identity");
  expectTrap(() => uget(0, original, 3n, 0), "Array.uget out of bounds");
  expectTrap(() => uset(0, original, 3n, replacement, 0),
    "Array.uset out of bounds");
  expectTrap(() => replicate(0, 0, value), "Array.replicate invalid Nat");

  let naturalIndexed = emptyWithCapacity(0, immediateNatural(3));
  naturalIndexed = push(0, naturalIndexed, immediateNatural(10));
  naturalIndexed = push(0, naturalIndexed, immediateNatural(20));
  naturalIndexed = push(0, naturalIndexed, immediateNatural(30));
  equal(set(0, naturalIndexed, immediateNatural(1), immediateNatural(21), 0),
    naturalIndexed, "Array.set did not reuse its exclusive input");
  equal(arrayState(exports.memory, naturalIndexed).words.join(","),
    [10, 21, 30].map(immediateNatural).join(","),
    "Array.set Nat-indexed replacement");
  equal(setBang(0, naturalIndexed, immediateNatural(2), immediateNatural(31)),
    naturalIndexed, "Array.set! did not reuse its in-bounds exclusive input");
  equal(arrayState(exports.memory, naturalIndexed).words.join(","),
    [10, 21, 31].map(immediateNatural).join(","),
    "Array.set! in-bounds replacement");
  const discardedReplacement = allocateOwnedOpaque(exports);
  equal(setBang(
    0, naturalIndexed, immediateNatural(30), discardedReplacement),
  naturalIndexed, "Array.set! out-of-bounds identity");
  equal(heapObjectState(exports.memory, discardedReplacement).kind, KIND_FREED,
    "Array.set! out-of-bounds did not consume its replacement");
  equal(swap(
    0, naturalIndexed, immediateNatural(0), immediateNatural(2), 0, 0),
  naturalIndexed, "Array.swap did not reuse its exclusive input");
  equal(arrayState(exports.memory, naturalIndexed).words.join(","),
    [31, 21, 10].map(immediateNatural).join(","),
    "Array.swap exclusive elements");

  let sharedSwap = emptyWithCapacity(0, immediateNatural(3));
  sharedSwap = push(0, sharedSwap, immediateNatural(4));
  sharedSwap = push(0, sharedSwap, immediateNatural(5));
  sharedSwap = push(0, sharedSwap, immediateNatural(6));
  new DataView(exports.memory.buffer).setUint32(sharedSwap + 8, 2, true);
  const sharedSwapResult = swap(
    0, sharedSwap, immediateNatural(0), immediateNatural(2), 0, 0);
  expect(sharedSwapResult !== sharedSwap,
    "Array.swap mutated a shared input");
  equal(arrayState(exports.memory, sharedSwap).refCount, 1,
    "Array.swap did not consume one shared input reference");
  equal(arrayState(exports.memory, sharedSwap).words.join(","),
    [4, 5, 6].map(immediateNatural).join(","),
    "Array.swap mutated a shared alias");
  equal(arrayState(exports.memory, sharedSwapResult).words.join(","),
    [6, 5, 4].map(immediateNatural).join(","),
    "Array.swap shared copy");
  release(sharedSwap);
  release(sharedSwapResult);

  const getChild = allocateOwnedOpaque(exports);
  const getOwnedArray = replicate(0, immediateNatural(1), getChild);
  const getOwnedChild = getInternal(
    0, getOwnedArray, immediateNatural(0), 0);
  equal(getOwnedChild, getChild, "Array.getInternal owned child");
  equal(heapObjectState(exports.memory, getChild).refCount, 2,
    "Array.getInternal did not retain its result");
  release(getOwnedArray);
  equal(heapObjectState(exports.memory, getChild).refCount, 1,
    "Array.getInternal result did not survive its source");
  release(getOwnedChild);
  equal(heapObjectState(exports.memory, getChild).kind, KIND_FREED,
    "Array.getInternal result remained live after release");
  release(naturalIndexed);

  const child = allocateOwnedOpaque(exports);
  const owned = replicate(0, immediateNatural(3), child);
  equal(heapObjectState(exports.memory, child).refCount, 3,
    "Array.replicate child references");
  const ownedGet = uget(0, owned, 1n, 0);
  equal(ownedGet, child, "Array.uget owned child");
  equal(heapObjectState(exports.memory, child).refCount, 4,
    "Array.uget did not retain its owned result");
  const replacementChild = allocateOwnedOpaque(exports);
  equal(uset(0, owned, 1n, replacementChild, 0), owned,
    "Array.uset owned child identity");
  equal(heapObjectState(exports.memory, child).refCount, 3,
    "Array.uset did not release the replaced child");
  equal(heapObjectState(exports.memory, replacementChild).refCount, 1,
    "Array.uset did not transfer the replacement child");
  equal(pop(0, owned), owned, "Array.pop owned child identity");
  equal(heapObjectState(exports.memory, child).refCount, 2,
    "Array.pop did not release the removed child");
  release(owned);
  equal(heapObjectState(exports.memory, owned).kind, KIND_FREED,
    "final Array release did not retire its header");
  equal(heapObjectState(exports.memory, replacementChild).kind, KIND_FREED,
    "final Array release did not release replacement child");
  equal(heapObjectState(exports.memory, child).refCount, 1,
    "final Array release did not release retained child");
  release(ownedGet);
  equal(heapObjectState(exports.memory, child).kind, KIND_FREED,
    "released Array.uget result remained live");

  const zeroChild = allocateOwnedOpaque(exports);
  replicate(0, immediateNatural(0), zeroChild);
  equal(heapObjectState(exports.memory, zeroChild).kind, KIND_FREED,
    "Array.replicate zero did not consume its value");

  const sharedChild = allocateOwnedOpaque(exports);
  const sharedOwned = replicate(0, immediateNatural(3), sharedChild);
  new DataView(exports.memory.buffer).setUint32(sharedOwned + 8, 2, true);
  const sharedReplacement = allocateOwnedOpaque(exports);
  const sharedOwnedUpdated = uset(
    0, sharedOwned, 1n, sharedReplacement, 0);
  equal(heapObjectState(exports.memory, sharedChild).refCount, 5,
    "shared Array.uset did not retain copied children");
  equal(heapObjectState(exports.memory, sharedReplacement).refCount, 1,
    "shared Array.uset did not transfer replacement child");
  release(sharedOwned);
  equal(heapObjectState(exports.memory, sharedChild).refCount, 2,
    "shared Array.uset original release count");
  release(sharedOwnedUpdated);
  equal(heapObjectState(exports.memory, sharedChild).kind, KIND_FREED,
    "shared Array.uset copied children remained live");
  equal(heapObjectState(exports.memory, sharedReplacement).kind, KIND_FREED,
    "shared Array.uset replacement remained live");

  const sharedPopChild = allocateOwnedOpaque(exports);
  const sharedPopOwned = replicate(0, immediateNatural(3), sharedPopChild);
  new DataView(exports.memory.buffer).setUint32(sharedPopOwned + 8, 2, true);
  const sharedPopResult = pop(0, sharedPopOwned);
  equal(heapObjectState(exports.memory, sharedPopChild).refCount, 5,
    "shared Array.pop did not retain copied children");
  release(sharedPopOwned);
  equal(heapObjectState(exports.memory, sharedPopChild).refCount, 2,
    "shared Array.pop original release count");
  release(sharedPopResult);
  equal(heapObjectState(exports.memory, sharedPopChild).kind, KIND_FREED,
    "shared Array.pop copied children remained live");

  return "PASS zero-import resident arrays";
}

export async function checkFetchedResidentArrays(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentArrays(await response.arrayBuffer());
}
