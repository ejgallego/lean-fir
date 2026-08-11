function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function writePromotedTag(memory, address, payload) {
  const view = new DataView(memory.buffer);
  for (const [index, value] of [5, 3, 0, 40, 1, 1, 0, 0].entries()) {
    view.setUint32(address + 4 * index, value, true);
  }
  view.setBigUint64(address + 32, payload, true);
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

/** Exercise Lean-compatible scalar boxing, unboxing, and fixed-width equality. */
export async function checkResidentScalarBox(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident scalar-box module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident scalar-box memory export is missing");
  for (const name of [
    "resident_scalar_box_uint8_roundtrip",
    "resident_scalar_unbox_uint32",
    "fir_box_uint8",
    "fir_unbox_uint8",
    "fir_unbox_uint32",
    "fir_ext_UInt32_decEq",
  ]) {
    equal(typeof exports[name], "function", `missing export ${name}`);
  }

  const view = new DataView(exports.memory.buffer);
  for (let value = 0; value <= 255; value += 1) {
    view.setUint32(0, 0xdecafbad, true);
    equal(exports.fir_box_uint8(value) >>> 0, 2 * value + 1,
      `UInt8 ${value} boxed incorrectly`);
    equal(exports.resident_scalar_box_uint8_roundtrip(value) >>> 0, value,
      `UInt8 ${value} round trip failed`);
    equal(view.getUint32(0, true), 0xdecafbad,
      `UInt8 ${value} did not restore scratch memory`);
  }

  for (const value of [0, 1, 255, 65535, 0x7fffffff]) {
    const word = (BigInt(value) * 2n + 1n) & 0xffffffffn;
    equal(exports.fir_unbox_uint32(Number(word)) >>> 0, value >>> 0,
      `immediate UInt32 ${value} unboxed incorrectly`);
  }
  equal(exports.fir_ext_UInt32_decEq(0xffffffff, 0xffffffff), 1,
    "UInt32.decEq equal");
  equal(exports.fir_ext_UInt32_decEq(0xffffffff, 0), 0,
    "UInt32.decEq unequal");

  writePromotedTag(exports.memory, 1024, 0x80000000n);
  writePromotedTag(exports.memory, 1064, 0xffffffffn);
  equal(exports.resident_scalar_unbox_uint32(1024) >>> 0, 0x80000000,
    "promoted UInt32 lower boundary unboxed incorrectly");
  equal(exports.resident_scalar_unbox_uint32(1064) >>> 0, 0xffffffff,
    "promoted UInt32 upper boundary unboxed incorrectly");

  expectTrap(() => exports.fir_unbox_uint8(513),
    "out-of-range UInt8 immediate did not trap");
  writePromotedTag(exports.memory, 1104, 0x100000000n);
  expectTrap(() => exports.fir_unbox_uint32(1104),
    "out-of-range promoted UInt32 did not trap");

  return "PASS zero-import resident scalar boxing";
}

export async function checkFetchedResidentScalarBox(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentScalarBox(await response.arrayBuffer());
}
