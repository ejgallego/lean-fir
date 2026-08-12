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

function checkPromotedTag(memory, address, payload) {
  const view = new DataView(memory.buffer);
  const expectedHeader = [5, 3, 0, 40, 1, 1, 0, 0];
  expectedHeader.forEach((value, index) =>
    equal(view.getUint32(address + 4 * index, true), value,
      `promoted UInt32 header word ${index}`));
  equal(view.getBigUint64(address + 32, true), payload,
    "promoted UInt32 payload");
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
    "resident_scalar_box_uint16_roundtrip",
    "resident_scalar_box_uint32_roundtrip",
    "resident_scalar_unbox_uint32",
    "fir_box_uint8",
    "fir_box_uint16",
    "fir_box_uint32",
    "fir_unbox_uint8",
    "fir_unbox_uint16",
    "fir_unbox_uint32",
    "fir_ext_UInt32_decEq",
  ]) {
    equal(typeof exports[name], "function", `missing export ${name}`);
  }

  for (let value = 0; value <= 0xffff; value += 1) {
    equal(exports.fir_box_uint16(value) >>> 0, 2 * value + 1,
      `UInt16 ${value} boxed incorrectly`);
    equal(exports.resident_scalar_box_uint16_roundtrip(value) >>> 0, value,
      `UInt16 ${value} round trip failed`);
  }

  const initialFrontier = exports.fir_heap_frontier() >>> 0;
  for (const value of [0, 1, 0xffff, 0x7fffffff]) {
    equal(exports.fir_box_uint32(value) >>> 0,
      Number((BigInt(value) * 2n + 1n) & 0xffffffffn),
      `immediate UInt32 ${value} boxed incorrectly`);
    equal(exports.resident_scalar_box_uint32_roundtrip(value) >>> 0,
      value >>> 0, `immediate UInt32 ${value} round trip failed`);
  }
  equal(exports.fir_heap_frontier() >>> 0, initialFrontier,
    "immediate UInt32 boxing grew the heap");

  for (const value of [0x80000000, 0xffffffff]) {
    const before = exports.fir_heap_frontier() >>> 0;
    const address = exports.fir_box_uint32(value) >>> 0;
    equal(address, before, `promoted UInt32 ${value} used the wrong address`);
    equal(exports.fir_heap_frontier() >>> 0, before + 40,
      `promoted UInt32 ${value} grew the frontier incorrectly`);
    checkPromotedTag(exports.memory, address, BigInt(value));
    equal(exports.fir_unbox_uint32(address) >>> 0, value >>> 0,
      `promoted UInt32 ${value} unboxed incorrectly`);
    equal(exports.resident_scalar_box_uint32_roundtrip(value) >>> 0,
      value >>> 0, `promoted UInt32 ${value} round trip failed`);
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
  expectTrap(() => exports.fir_unbox_uint16(0x20001),
    "out-of-range UInt16 immediate did not trap");
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
