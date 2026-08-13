import { ConcreteHost } from "./concrete-host.mjs";

const HEADER_BYTES = 32;
const SLOT_BYTES = 8;

function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function view(memory) {
  return new DataView(memory.buffer);
}

function writeHeader(memory, address, {
  kind = 1,
  flags = 2,
  refCount = 1,
  allocationBytes = HEADER_BYTES,
  aux0 = 0,
  aux1 = 0,
  aux2 = 0,
  aux3 = 0,
} = {}) {
  [kind, flags, refCount, allocationBytes, aux0, aux1, aux2, aux3]
    .forEach((value, index) =>
      view(memory).setUint32(address + 4 * index, value, true));
}

function writeSlot(memory, address, index, value) {
  view(memory).setUint32(address + HEADER_BYTES + SLOT_BYTES * index,
    value, true);
  view(memory).setUint32(address + HEADER_BYTES + SLOT_BYTES * index + 4,
    0, true);
}

function expectPersistent(memory, address, label) {
  equal(view(memory).getUint32(address + 4, true), 3,
    `${label} flags`);
  equal(view(memory).getUint32(address + 8, true), 0,
    `${label} reference count`);
}

function setFrontier(exports, frontier) {
  equal(typeof exports.fir_heap_set_frontier, "function",
    "resident frontier setter export is missing");
  exports.fir_heap_set_frontier(frontier);
}

async function expectTrap(module, prepare, invoke, label) {
  const { exports } = await WebAssembly.instantiate(module, {});
  prepare(exports);
  let trapped = false;
  try {
    invoke(exports);
  } catch (error) {
    trapped = error instanceof WebAssembly.RuntimeError;
  }
  expect(trapped, `${label} did not trap`);
}

/**
 * Check zero-import cache publication against raw W6 object graphs and an
 * independent ConcreteHost header decoder.
 */
export async function checkResidentCache(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident cache module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident cache memory export is missing");
  for (const entry of [
    "resident_cache_set",
    "fir_cache_set_0",
    "fir_cache_set_1",
    "fir_initialize_persistent_caches",
    "resident_lazy_object",
    "fir_heap_frontier",
    "fir_heap_alloc",
    "fir_heap_rewind",
  ]) {
    equal(typeof exports[entry], "function",
      `resident cache export ${entry} is missing`);
  }

  const { exports: lazy } = await WebAssembly.instantiate(module, {});
  const lazyInitialFrontier = lazy.fir_heap_frontier() >>> 0;
  const coldScratch = lazy.fir_heap_alloc(40) >>> 0;
  equal(coldScratch, lazyInitialFrontier,
    "cold scratch did not start at the initial frontier");
  const lazyRoot = lazy.resident_lazy_object() >>> 0;
  const lazyFloor = lazy.fir_heap_frontier() >>> 0;
  expect(lazyFloor > coldScratch + 40,
    "cold lazy cache did not advance the persistent floor");
  expectPersistent(lazy.memory, lazyRoot, "lazy cache root");
  lazy.fir_heap_rewind(lazyInitialFrontier);
  equal(lazy.fir_heap_frontier() >>> 0, lazyFloor,
    "cache-aware rewind crossed the cold persistent floor");
  equal(lazy.resident_lazy_object() >>> 0, lazyRoot,
    "warm lazy cache changed its persistent root");
  equal(lazy.fir_heap_frontier() >>> 0, lazyFloor,
    "warm lazy cache grew the persistent floor");
  const warmScratch = lazy.fir_heap_alloc(40) >>> 0;
  equal(warmScratch, lazyFloor,
    "warm scratch did not start at the persistent floor");
  lazy.fir_heap_rewind(lazyFloor);
  equal(lazy.fir_heap_frontier() >>> 0, lazyFloor,
    "warm scratch rewind did not stay flat");

  const { exports: persistent } = await WebAssembly.instantiate(module, {});
  const initialFrontier = persistent.fir_heap_frontier() >>> 0;
  persistent.fir_initialize_persistent_caches();
  const checkpoint = persistent.fir_heap_frontier() >>> 0;
  expect(checkpoint > initialFrontier,
    "persistent initializer did not allocate its cached object graph");
  const cachedRoot = persistent.resident_lazy_object() >>> 0;
  expect(cachedRoot >= initialFrontier && cachedRoot < checkpoint,
    "cached root is not below the persistent checkpoint");
  expectPersistent(persistent.memory, cachedRoot,
    "persistent initializer root");
  persistent.fir_initialize_persistent_caches();
  equal(persistent.fir_heap_frontier() >>> 0, checkpoint,
    "persistent initializer was not idempotent");

  const scratch = persistent.fir_heap_alloc(40) >>> 0;
  equal(scratch, checkpoint,
    "scratch allocation did not start at the persistent checkpoint");
  expect((persistent.fir_heap_frontier() >>> 0) > checkpoint,
    "scratch allocation did not advance the frontier");
  persistent.fir_heap_rewind(checkpoint);
  equal(persistent.fir_heap_frontier() >>> 0, checkpoint,
    "scratch rewind did not restore the persistent checkpoint");
  equal(persistent.resident_lazy_object() >>> 0, cachedRoot,
    "scratch rewind invalidated the persistent cached root");
  persistent.fir_initialize_persistent_caches();
  equal(persistent.fir_heap_frontier() >>> 0, checkpoint,
    "post-rewind initialization changed the persistent checkpoint");

  const parent = 1024;
  const childOne = 1072;
  const childTwo = 1104;
  writeHeader(exports.memory, parent, {
    refCount: 7,
    allocationBytes: 48,
    aux1: 2,
  });
  writeHeader(exports.memory, childOne, { refCount: 3 });
  writeHeader(exports.memory, childTwo, { refCount: 5 });
  writeSlot(exports.memory, parent, 0, childOne);
  writeSlot(exports.memory, parent, 1, childTwo);
  setFrontier(exports, 1136);
  equal(exports.resident_cache_set(parent) >>> 0, parent,
    "resident cache did not return the exact object lane");
  expectPersistent(exports.memory, parent, "constructor parent");
  expectPersistent(exports.memory, childOne, "constructor child one");
  expectPersistent(exports.memory, childTwo, "constructor child two");

  const cycle = 1136;
  writeHeader(exports.memory, cycle, {
    refCount: 9,
    allocationBytes: 40,
    aux1: 1,
  });
  writeSlot(exports.memory, cycle, 0, cycle);
  setFrontier(exports, 1176);
  equal(exports.fir_cache_set_0(cycle) >>> 0, cycle,
    "resident cache helper changed a cyclic root lane");
  expectPersistent(exports.memory, cycle, "cyclic constructor");

  const closure = 1176;
  const closureChildOne = 1232;
  const closureChildTwo = 1264;
  writeHeader(exports.memory, closure, {
    kind: 2,
    refCount: 11,
    allocationBytes: 56,
    aux2: 3,
    aux3: 0,
  });
  writeHeader(exports.memory, closureChildOne, { refCount: 13 });
  writeHeader(exports.memory, closureChildTwo, { refCount: 15 });
  writeSlot(exports.memory, closure, 0, closureChildOne);
  view(exports.memory).setUint8(
    closure + HEADER_BYTES + SLOT_BYTES,
    0xab,
  );
  writeSlot(exports.memory, closure, 2, closureChildTwo);
  setFrontier(exports, 1296);
  equal(exports.resident_cache_set(closure) >>> 0, closure,
    "resident cache changed a closure root lane");
  expectPersistent(exports.memory, closure, "closure root");
  expectPersistent(exports.memory, closureChildOne, "closure child one");
  expectPersistent(exports.memory, closureChildTwo, "closure child two");

  const alreadyPersistent = 1296;
  writeHeader(exports.memory, alreadyPersistent, {
    flags: 3,
    refCount: 0,
  });
  setFrontier(exports, 1328);
  exports.resident_cache_set(alreadyPersistent);
  expectPersistent(exports.memory, alreadyPersistent,
    "already-persistent object");

  const staleParent = 1328;
  const staleChild = 1368;
  writeHeader(exports.memory, staleParent, {
    allocationBytes: 40,
    aux1: 1,
  });
  writeHeader(exports.memory, staleChild, {
    kind: 255,
    flags: 0,
    refCount: 0,
  });
  writeSlot(exports.memory, staleParent, 0, staleChild);
  setFrontier(exports, 1400);
  exports.resident_cache_set(staleParent);
  expectPersistent(exports.memory, staleParent, "stale-parent root");
  equal(view(exports.memory).getUint32(staleChild, true), 255,
    "resident cache changed a canonical freed child");
  equal(view(exports.memory).getUint32(staleChild + 4, true), 0,
    "resident cache revived a canonical freed child");

  const host = new ConcreteHost();
  const { exports: concrete } = await WebAssembly.instantiate(module, {});
  host.attachMemory(concrete.memory);
  writeHeader(concrete.memory, parent, {
    refCount: 7,
    allocationBytes: 48,
    aux1: 2,
  });
  writeHeader(concrete.memory, childOne, { refCount: 3 });
  writeHeader(concrete.memory, childTwo, { refCount: 5 });
  writeSlot(concrete.memory, parent, 0, childOne);
  writeSlot(concrete.memory, parent, 1, childTwo);
  setFrontier(concrete, 1136);
  concrete.resident_cache_set(parent);
  for (const [address, label] of [
    [parent, "constructor parent"],
    [childOne, "constructor child one"],
    [childTwo, "constructor child two"],
  ]) {
    const header = host.readHeader(address);
    expect(header.persistent && header.live && header.rc === 0,
      `ConcreteHost disagrees with resident cache for ${label}`);
  }

  await expectTrap(
    module,
    () => {},
    (candidate) => candidate.resident_cache_set(0),
    "zero cache root",
  );
  await expectTrap(
    module,
    (candidate) => {
      writeHeader(candidate.memory, parent);
      setFrontier(candidate, 1056);
    },
    (candidate) => candidate.resident_cache_set(parent + 4),
    "misaligned cache root",
  );
  await expectTrap(
    module,
    (candidate) => {
      writeHeader(candidate.memory, parent, { flags: 0 });
      setFrontier(candidate, 1056);
    },
    (candidate) => candidate.resident_cache_set(parent),
    "noncanonical dead cache root",
  );
  await expectTrap(
    module,
    (candidate) => {
      writeHeader(candidate.memory, parent, {
        kind: 2,
        allocationBytes: 40,
        aux2: 1,
        aux3: 1,
      });
      setFrontier(candidate, 1064);
    },
    (candidate) => candidate.resident_cache_set(parent),
    "unknown closure descriptor",
  );
  await expectTrap(
    module,
    (candidate) => {
      writeHeader(candidate.memory, parent, {
        kind: 2,
        allocationBytes: 48,
        aux2: 2,
        aux3: 0,
      });
      setFrontier(candidate, 1072);
    },
    (candidate) => candidate.resident_cache_set(parent),
    "closure descriptor count mismatch",
  );
  await expectTrap(
    module,
    (candidate) => {
      writeHeader(candidate.memory, parent, {
        allocationBytes: 296,
        aux1: 33,
      });
      setFrontier(candidate, 1320);
    },
    (candidate) => candidate.resident_cache_set(parent),
    "constructor beyond resident cache field limit",
  );

  return "PASS zero-import recursive Wasm-resident lazy-cache publication";
}

export async function checkFetchedResidentCache(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentCache(await response.arrayBuffer());
}
