import { ConcreteHost } from "./concrete-host.mjs";

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
  allocationBytes = 32,
  aux0 = 0,
  aux1 = 0,
  aux2 = 0,
  aux3 = 0,
} = {}) {
  const view = new DataView(memory.buffer);
  [kind, flags, refCount, allocationBytes, aux0, aux1, aux2, aux3]
    .forEach((value, index) =>
      view.setUint32(address + 4 * index, value, true));
}

/**
 * Check zero-import nonrecursive increments against exact W6 headers and the
 * independent ConcreteHost decoder.
 */
export async function checkResidentIncrements(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident increment module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident increment memory export is missing");
  equal(typeof exports.resident_inc_checked, "function",
    "resident checked increment export is missing");
  equal(typeof exports.resident_inc_unchecked, "function",
    "resident unchecked increment export is missing");

  const checkedAddress = 1024;
  const uncheckedAddress = 1088;
  const persistentAddress = 1152;
  const promotedAddress = 1216;
  writeHeader(exports.memory, checkedAddress, { refCount: 1 });
  writeHeader(exports.memory, uncheckedAddress, { refCount: 7 });
  writeHeader(exports.memory, persistentAddress, {
    flags: 3,
    refCount: 41,
  });
  writeHeader(exports.memory, promotedAddress, {
    kind: 5,
    flags: 3,
    refCount: 0,
    allocationBytes: 40,
    aux0: 1,
  });
  exports.resident_inc_checked(checkedAddress);
  exports.resident_inc_unchecked(uncheckedAddress);
  exports.resident_inc_checked(3);
  exports.resident_inc_checked(persistentAddress);
  exports.resident_inc_unchecked(persistentAddress);
  exports.resident_inc_checked(promotedAddress);

  const view = new DataView(exports.memory.buffer);
  equal(view.getUint32(checkedAddress + 8, true), 2,
    "resident checked increment wrote the wrong count");
  equal(view.getUint32(uncheckedAddress + 8, true), 10,
    "resident unchecked increment wrote the wrong count");
  equal(view.getUint32(persistentAddress + 8, true), 41,
    "resident increment changed a persistent count");
  equal(view.getUint32(promotedAddress + 8, true), 0,
    "resident checked increment changed a promoted tag");

  const host = new ConcreteHost();
  const { exports: concrete } = await WebAssembly.instantiate(module, {});
  host.attachMemory(concrete.memory);
  writeHeader(concrete.memory, checkedAddress, { refCount: 1 });
  writeHeader(concrete.memory, uncheckedAddress, { refCount: 7 });
  concrete.resident_inc_checked(checkedAddress);
  concrete.resident_inc_unchecked(uncheckedAddress);
  equal(host.readHeader(checkedAddress).rc, 2,
    "ConcreteHost disagrees with the checked resident increment");
  equal(host.readHeader(uncheckedAddress).rc, 10,
    "ConcreteHost disagrees with the unchecked resident increment");

  const invalid = async (prepare, invoke, label) => {
    const { exports: candidate } = await WebAssembly.instantiate(module, {});
    prepare(candidate.memory);
    let trapped = false;
    try {
      invoke(candidate);
    } catch (error) {
      trapped = error instanceof WebAssembly.RuntimeError;
    }
    expect(trapped, `${label} did not trap`);
  };
  await invalid(
    () => {},
    (candidate) => candidate.resident_inc_checked(0),
    "zero checked increment",
  );
  await invalid(
    (memory) => writeHeader(memory, checkedAddress),
    (candidate) => candidate.resident_inc_checked(checkedAddress + 4),
    "misaligned checked increment",
  );
  await invalid(
    (memory) => writeHeader(memory, checkedAddress, { flags: 0 }),
    (candidate) => candidate.resident_inc_checked(checkedAddress),
    "dead checked increment",
  );
  await invalid(
    () => {},
    (candidate) => candidate.resident_inc_unchecked(3),
    "unchecked immediate increment",
  );
  await invalid(
    (memory) => writeHeader(memory, promotedAddress, {
      kind: 5,
      flags: 3,
      refCount: 0,
      allocationBytes: 40,
      aux0: 1,
    }),
    (candidate) => candidate.resident_inc_unchecked(promotedAddress),
    "unchecked promoted-tag increment",
  );
  await invalid(
    (memory) => writeHeader(memory, checkedAddress, {
      refCount: 0xffffffff,
    }),
    (candidate) => candidate.resident_inc_checked(checkedAddress),
    "overflowing checked increment",
  );

  return "PASS zero-import resident nonrecursive increments";
}

export async function checkFetchedResidentIncrements(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentIncrements(await response.arrayBuffer());
}
