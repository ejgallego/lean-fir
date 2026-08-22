import { ConcreteHost } from "./concrete-host.mjs";

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
  allocationBytes = 32,
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
  view(memory).setUint32(address + 32 + 8 * index, value, true);
  view(memory).setUint32(address + 36 + 8 * index, 0, true);
}

function expectReleased(memory, address, bytes, label) {
  const memoryView = view(memory);
  equal(memoryView.getUint32(address, true), 255, `${label} kind`);
  equal(memoryView.getUint32(address + 4, true), 0, `${label} flags`);
  equal(memoryView.getUint32(address + 8, true), 0, `${label} reference count`);
  equal(memoryView.getUint32(address + 12, true), bytes,
    `${label} allocation extent`);
  for (const offset of [16, 20, 24, 28]) {
    equal(memoryView.getUint32(address + offset, true), 0,
      `${label} auxiliary word ${offset}`);
  }
}

async function expectTrap(module, prepare, invoke, label) {
  const { exports } = await WebAssembly.instantiate(module, {});
  prepare(exports.memory);
  let trapped = false;
  try {
    invoke(exports);
  } catch (error) {
    trapped = error instanceof WebAssembly.RuntimeError;
  }
  expect(trapped, `${label} did not trap`);
}

/**
 * Check zero-import recursive decrements and nonrecursive delete against raw
 * W6 constructor/closure graphs and an independent ConcreteHost decoder.
 */
export async function checkResidentReleases(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident release module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident release memory export is missing");
  for (const entry of [
    "resident_dec_checked",
    "resident_dec_unchecked",
    "resident_delete",
  ]) {
    equal(typeof exports[entry], "function",
      `resident release export ${entry} is missing`);
  }

  const parent = 1024;
  const childOne = 1088;
  const childTwo = 1152;
  writeHeader(exports.memory, parent, {
    allocationBytes: 48,
    aux1: 2,
  });
  writeHeader(exports.memory, childOne);
  writeHeader(exports.memory, childTwo, { refCount: 2 });
  writeSlot(exports.memory, parent, 0, childOne);
  writeSlot(exports.memory, parent, 1, childTwo);
  exports.resident_dec_checked(parent);
  expectReleased(exports.memory, parent, 48, "released constructor parent");
  expectReleased(exports.memory, childOne, 32, "released constructor child");
  equal(view(exports.memory).getUint32(childTwo + 8, true), 1,
    "shared constructor child did not decrement once");

  const closure = 1216;
  const closureChildOne = 1280;
  const closureChildTwo = 1344;
  writeHeader(exports.memory, closure, {
    kind: 2,
    allocationBytes: 56,
    aux2: 3,
    aux3: 0,
  });
  writeHeader(exports.memory, closureChildOne);
  writeHeader(exports.memory, closureChildTwo, { refCount: 2 });
  writeSlot(exports.memory, closure, 0, closureChildOne);
  view(exports.memory).setUint8(closure + 40, 0xab);
  writeSlot(exports.memory, closure, 2, closureChildTwo);
  exports.resident_dec_checked(closure);
  expectReleased(exports.memory, closure, 56, "released closure parent");
  expectReleased(exports.memory, closureChildOne, 32, "released closure child");
  equal(view(exports.memory).getUint32(closureChildTwo + 8, true), 1,
    "shared closure child did not decrement once");

  exports.resident_dec_checked(0);
  exports.resident_dec_checked(3);

  const aboveOne = 1408;
  const persistent = 1472;
  writeHeader(exports.memory, aboveOne, { refCount: 2 });
  writeHeader(exports.memory, persistent, { flags: 3, refCount: 41 });
  exports.resident_dec_unchecked(aboveOne);
  exports.resident_dec_unchecked(persistent);
  equal(view(exports.memory).getUint32(aboveOne + 8, true), 1,
    "unchecked above-one decrement wrote the wrong count");
  equal(view(exports.memory).getUint32(persistent + 8, true), 41,
    "resident decrement changed a persistent object");

  const deleteParent = 1536;
  const deleteChild = 1600;
  writeHeader(exports.memory, deleteParent, {
    allocationBytes: 40,
    aux1: 1,
  });
  writeHeader(exports.memory, deleteChild);
  writeSlot(exports.memory, deleteParent, 0, deleteChild);
  exports.resident_delete(0);
  exports.resident_delete(deleteParent);
  expectReleased(exports.memory, deleteParent, 40, "deleted parent");
  equal(view(exports.memory).getUint32(deleteChild + 8, true), 1,
    "delete recursively changed its child");
  equal(view(exports.memory).getUint32(deleteChild + 4, true), 2,
    "delete marked its child dead");

  const host = new ConcreteHost();
  const { exports: concrete } = await WebAssembly.instantiate(module, {});
  host.attachMemory(concrete.memory);
  writeHeader(concrete.memory, parent, {
    allocationBytes: 48,
    aux1: 2,
  });
  writeHeader(concrete.memory, childOne);
  writeHeader(concrete.memory, childTwo, { refCount: 2 });
  writeSlot(concrete.memory, parent, 0, childOne);
  writeSlot(concrete.memory, parent, 1, childTwo);
  concrete.resident_dec_checked(parent);
  equal(host.readHeader(parent, false).kind, 255,
    "ConcreteHost disagrees with released parent kind");
  equal(host.readHeader(parent, false).live, false,
    "ConcreteHost disagrees with released parent liveness");
  equal(host.readHeader(childTwo).rc, 1,
    "ConcreteHost disagrees with recursively decremented child");

  await expectTrap(module,
    () => {},
    (candidate) => candidate.resident_dec_unchecked(3),
    "unchecked immediate decrement");
  await expectTrap(module,
    () => {},
    (candidate) => candidate.resident_dec_checked(4),
    "misaligned checked decrement");
  await expectTrap(module,
    (memory) => writeHeader(memory, parent, { flags: 0 }),
    (candidate) => candidate.resident_dec_checked(parent),
    "dead checked decrement");
  await expectTrap(module,
    (memory) => writeHeader(memory, parent, { refCount: 0 }),
    (candidate) => candidate.resident_dec_checked(parent),
    "underflowing checked decrement");
  await expectTrap(module,
    (memory) => {
      const address = memory.buffer.byteLength - 16;
      const memoryView = view(memory);
      memoryView.setUint32(address, 1, true);
      memoryView.setUint32(address + 4, 2, true);
      memoryView.setUint32(address + 8, 2, true);
      memoryView.setUint32(address + 12, 32, true);
    },
    (candidate) => candidate.resident_dec_checked(
      candidate.memory.buffer.byteLength - 16),
    "truncated shared-object header");
  await expectTrap(module,
    (memory) => writeHeader(memory, closure, {
      kind: 2,
      allocationBytes: 40,
      aux2: 1,
      aux3: 9,
    }),
    (candidate) => candidate.resident_dec_checked(closure),
    "unknown closure descriptor");
  await expectTrap(module,
    (memory) => writeHeader(memory, closure, {
      kind: 2,
      allocationBytes: 56,
      aux2: 2,
      aux3: 0,
    }),
    (candidate) => candidate.resident_dec_checked(closure),
    "closure descriptor count mismatch");
  await expectTrap(module,
    (memory) => {
      writeHeader(memory, parent, {
        allocationBytes: 40,
        aux1: 1,
      });
      writeSlot(memory, parent, 0, parent);
    },
    (candidate) => candidate.resident_dec_checked(parent),
    "cyclic constructor release");
  await expectTrap(module,
    () => {},
    (candidate) => candidate.resident_delete(3),
    "delete immediate");
  await expectTrap(module,
    (memory) => writeHeader(memory, parent, { flags: 0 }),
    (candidate) => candidate.resident_delete(parent),
    "delete dead object");
  await expectTrap(module,
    (memory) => writeHeader(memory, parent, {
      kind: 5,
      flags: 3,
      allocationBytes: 40,
      aux0: 1,
    }),
    (candidate) => candidate.resident_delete(parent),
    "delete promoted tag");

  return "PASS zero-import resident recursive release and delete";
}

export async function checkFetchedResidentReleases(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentReleases(await response.arrayBuffer());
}
