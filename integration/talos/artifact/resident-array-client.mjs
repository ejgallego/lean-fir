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

function arrayWords(memory, address) {
  const view = new DataView(memory.buffer);
  equal(view.getUint32(address, true), 8, "array object kind");
  equal(view.getUint32(address + 4, true), 3, "array flags");
  equal(view.getUint32(address + 16, true), 0x41525259, "array marker");
  const size = view.getUint32(address + 20, true);
  equal(view.getUint32(address + 24, true), size, "array capacity");
  equal(view.getUint32(address + 12, true), 32 + 8 * size,
    "array allocation size");
  return Array.from({ length: size }, (_, index) =>
    view.getUint32(address + 32 + 8 * index, true));
}

/** Check the zero-import resident Array.uget/uset/replicate frontier. */
export async function checkResidentArrays(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident array module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident array memory export is missing");
  const replicate = exports.fir_ext_Array_replicate;
  const uget = exports.fir_ext_Array_uget;
  const uset = exports.fir_ext_Array_uset;
  equal(typeof replicate, "function", "Array.replicate export");
  equal(typeof uget, "function", "Array.uget export");
  equal(typeof uset, "function", "Array.uset export");

  const value = immediateNatural(21);
  const replacement = immediateNatural(49);
  const original = replicate(0, immediateNatural(3), value);
  expect(original >= 1024 && original % 8 === 0,
    "Array.replicate returned an invalid address");
  expect(arrayWords(exports.memory, original).every((word) => word === value),
    "Array.replicate did not fill every element");
  equal(uget(0, original, 1n, 0), value, "Array.uget middle element");

  const updated = uset(0, original, 1n, replacement, 0);
  expect(updated !== original, "Array.uset did not preserve its input array");
  expect(arrayWords(exports.memory, original).every((word) => word === value),
    "Array.uset mutated the persistent input array");
  expect(arrayWords(exports.memory, updated).join(",") ===
    [value, replacement, value].join(","),
  "Array.uset copied or replaced the wrong element");
  equal(uget(0, updated, 1n, 0), replacement,
    "Array.uget updated element");

  const empty = replicate(0, immediateNatural(0), value);
  expect(arrayWords(exports.memory, empty).length === 0,
    "Array.replicate zero did not create an empty array");
  expectTrap(() => uget(0, original, 3n, 0), "Array.uget out of bounds");
  expectTrap(() => uset(0, original, 3n, replacement, 0),
    "Array.uset out of bounds");
  expectTrap(() => replicate(0, 0, value), "Array.replicate invalid Nat");

  return "PASS zero-import resident arrays";
}

export async function checkFetchedResidentArrays(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentArrays(await response.arrayBuffer());
}
