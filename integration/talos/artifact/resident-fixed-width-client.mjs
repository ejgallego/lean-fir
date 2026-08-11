function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

/** Exercise the generic UInt16 extern family used by packed ByteArrays. */
export async function checkResidentFixedWidth(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident fixed-width module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  for (const name of [
    "fir_ext_UInt16_shiftRight",
    "fir_ext_UInt16_ofNat",
    "fir_ext_UInt16_toUInt8",
    "fir_ext_UInt16_land",
    "fir_ext_UInt16_xor",
  ]) {
    equal(typeof exports[name], "function", `missing export ${name}`);
  }

  const view = new DataView(exports.memory.buffer);
  const scratch = 0xdecafbad;
  for (const [value, count, expected] of [
    [0x8001, 0, 0x8001],
    [0x8001, 1, 0x4000],
    [0x8001, 8, 0x80],
    [0x8001, 15, 1],
    [0x8001, 16, 0x8001],
    [0x8001, 17, 0x4000],
  ]) {
    view.setUint32(0, scratch, true);
    equal(exports.fir_ext_UInt16_shiftRight(value, count) >>> 0, expected,
      `UInt16.shiftRight(${value}, ${count})`);
    equal(view.getUint32(0, true), scratch,
      "UInt16.shiftRight did not restore scratch memory");
  }

  for (const value of [0, 1, 255, 256, 0xffff, 0x10000, 0x12345]) {
    equal(exports.fir_ext_UInt16_ofNat(2 * value + 1) >>> 0,
      value & 0xffff, `UInt16.ofNat(${value})`);
  }
  equal(exports.fir_ext_UInt16_toUInt8(0xabcd) >>> 0, 0xcd,
    "UInt16.toUInt8");
  equal(exports.fir_ext_UInt16_land(0xa55a, 0x0ff0) >>> 0, 0x0550,
    "UInt16.land");
  equal(exports.fir_ext_UInt16_xor(0xa55a, 0x0ff0) >>> 0, 0xaaaa,
    "UInt16.xor");

  return "PASS zero-import resident fixed-width operations";
}

export async function checkFetchedResidentFixedWidth(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentFixedWidth(await response.arrayBuffer());
}
