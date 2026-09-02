function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function writeHeader(memory, address, {
  kind = 1,
  flags = 2,
  refCount = 1,
  allocationBytes = 40,
  aux0 = 0,
  aux1 = 0,
  aux2 = 0,
  aux3 = 0,
} = {}) {
  const memoryView = new DataView(memory.buffer);
  [kind, flags, refCount, allocationBytes, aux0, aux1, aux2, aux3]
    .forEach((value, index) =>
      memoryView.setUint32(address + 4 * index, value, true));
}

function writeSlot(memory, address, index, value) {
  const memoryView = new DataView(memory.buffer);
  memoryView.setUint32(address + 32 + 8 * index, value, true);
  memoryView.setUint32(address + 36 + 8 * index, 0, true);
}

export async function checkResidentRecyclingReleases(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident recycling release module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident recycling release memory export is missing");
  for (const name of ["fir_heap_frontier", "fir_heap_alloc",
    "resident_dec_checked", "resident_dec_unchecked", "resident_delete"]) {
    equal(typeof exports[name], "function", `missing ${name}`);
  }
  equal(exports.fir_heap_recycle, undefined,
    "private recycler escaped the production export surface");

  const allocate = (size) => exports.fir_heap_alloc(size) >>> 0;
  const frontier = () => exports.fir_heap_frontier() >>> 0;

  const parent = allocate(48);
  const child = allocate(40);
  writeHeader(exports.memory, parent, { allocationBytes: 48, aux1: 1 });
  writeHeader(exports.memory, child, { allocationBytes: 40 });
  writeSlot(exports.memory, parent, 0, child);
  const releasedFrontier = frontier();
  exports.resident_dec_checked(parent);
  equal(allocate(40), child,
    "recursive release did not recycle the exact child block");
  equal(allocate(48), parent,
    "recursive release did not recycle the exact parent block");
  equal(frontier(), releasedFrontier,
    "recursive release reuse advanced the bump frontier");

  const shared = allocate(40);
  writeHeader(exports.memory, shared, { allocationBytes: 40, refCount: 2 });
  exports.resident_dec_checked(shared);
  equal(new DataView(exports.memory.buffer).getUint32(shared + 8, true), 1,
    "shared decrement did not retain one reference");
  expect(allocate(40) !== shared,
    "shared block entered the reuse index");

  const persistent = allocate(40);
  writeHeader(exports.memory, persistent, {
    allocationBytes: 40,
    flags: 3,
  });
  exports.resident_dec_checked(persistent);
  expect(allocate(40) !== persistent,
    "persistent block entered the reuse index");

  const deleted = allocate(40);
  writeHeader(exports.memory, deleted, { allocationBytes: 40 });
  const beforeDelete = frontier();
  exports.resident_delete(deleted);
  equal(allocate(40), deleted,
    "explicit delete did not recycle its exact block");
  equal(frontier(), beforeDelete,
    "explicit-delete reuse advanced the bump frontier");

  return "PASS resident release feeds exact-size allocator reuse";
}
