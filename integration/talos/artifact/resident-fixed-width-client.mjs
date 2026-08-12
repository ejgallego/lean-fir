function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function naturalValue(memory, physical) {
  const word = physical >>> 0;
  if ((word & 1) === 1) return BigInt(word >>> 1);
  const view = new DataView(memory.buffer);
  equal(view.getUint32(word, true), 5, "natural object kind");
  equal(view.getUint32(word + 16, true), 1, "one-limb natural marker");
  return view.getBigUint64(word + 32, true);
}

/** Exercise the generic unsigned fixed-width extern families. */
export async function checkResidentFixedWidth(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident fixed-width module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  for (const name of [
    "fir_ext_UInt8_ofNat",
    "fir_ext_UInt8_toNat",
    "fir_ext_UInt8_toUInt32",
    "fir_ext_UInt8_toUInt64",
    "fir_ext_UInt8_toUSize",
    "fir_ext_UInt8_decEq",
    "fir_ext_UInt8_decLt",
    "fir_ext_UInt16_shiftRight",
    "fir_ext_UInt16_ofNat",
    "fir_ext_UInt16_toUInt8",
    "fir_ext_UInt16_toNat",
    "fir_ext_UInt16_toUInt32",
    "fir_ext_UInt16_toUInt64",
    "fir_ext_UInt16_land",
    "fir_ext_UInt16_xor",
    "fir_ext_UInt32_ofNat",
    "fir_ext_UInt32_toNat",
    "fir_ext_UInt32_toUInt8",
    "fir_ext_UInt32_toUInt16",
    "fir_ext_UInt32_toUInt64",
    "fir_ext_UInt32_toUSize",
    "fir_ext_UInt32_add",
    "fir_ext_UInt32_sub",
    "fir_ext_UInt32_land",
    "fir_ext_UInt32_xor",
    "fir_ext_UInt32_shiftRight",
    "fir_ext_UInt32_decLt",
    "fir_ext_UInt32_decLe",
    "fir_ext_UInt64_ofNat",
    "fir_ext_UInt64_toUInt8",
    "fir_ext_UInt64_toUInt16",
    "fir_ext_UInt64_toUSize",
    "fir_ext_UInt64_shiftLeft",
    "fir_ext_UInt64_shiftRight",
    "fir_ext_UInt64_decEq",
  ]) {
    equal(typeof exports[name], "function", `missing export ${name}`);
  }

  const view = new DataView(exports.memory.buffer);
  const scratch = 0xdecafbad01234567n;
  for (const [value, count, expected] of [
    [0x8001, 0, 0x8001],
    [0x8001, 1, 0x4000],
    [0x8001, 8, 0x80],
    [0x8001, 15, 1],
    [0x8001, 16, 0x8001],
    [0x8001, 17, 0x4000],
  ]) {
    view.setBigUint64(0, scratch, true);
    equal(exports.fir_ext_UInt16_shiftRight(value, count) >>> 0, expected,
      `UInt16.shiftRight(${value}, ${count})`);
    equal(view.getBigUint64(0, true), scratch,
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

  for (const value of [0, 1, 0x7f, 0xff]) {
    const natural = 2 * value + 1;
    equal(exports.fir_ext_UInt8_ofNat(natural) >>> 0, value,
      `UInt8.ofNat(${value})`);
    equal(naturalValue(exports.memory,
      exports.fir_ext_UInt8_toNat(value)), BigInt(value),
    `UInt8.toNat(${value})`);
    equal(exports.fir_ext_UInt8_toUInt32(value) >>> 0, value,
      `UInt8.toUInt32(${value})`);
    equal(exports.fir_ext_UInt8_toUInt64(value), BigInt(value),
      `UInt8.toUInt64(${value})`);
    equal(exports.fir_ext_UInt8_toUSize(value), BigInt(value),
      `UInt8.toUSize(${value})`);
  }
  equal(exports.fir_ext_UInt8_decEq(255, 255), 1, "UInt8.decEq equal");
  equal(exports.fir_ext_UInt8_decEq(255, 0), 0, "UInt8.decEq unequal");
  equal(exports.fir_ext_UInt8_decLt(1, 255), 1, "UInt8.decLt true");
  equal(exports.fir_ext_UInt8_decLt(255, 1), 0, "UInt8.decLt false");

  equal(naturalValue(exports.memory,
    exports.fir_ext_UInt16_toNat(0xffff)), 0xffffn, "UInt16.toNat");
  equal(exports.fir_ext_UInt16_toUInt32(0xffff) >>> 0, 0xffff,
    "UInt16.toUInt32");
  equal(exports.fir_ext_UInt16_toUInt64(0xffff), 0xffffn,
    "UInt16.toUInt64");

  const naturalMax32 = exports.fir_numeric_make_natural(0xffffffff, 0);
  equal(exports.fir_ext_UInt32_ofNat(naturalMax32) >>> 0, 0xffffffff,
    "UInt32.ofNat upper boundary");
  equal(naturalValue(exports.memory,
    exports.fir_ext_UInt32_toNat(0xffffffff)), 0xffffffffn,
  "UInt32.toNat upper boundary");
  equal(exports.fir_ext_UInt32_toUInt8(0x1234abcd) >>> 0, 0xcd,
    "UInt32.toUInt8");
  equal(exports.fir_ext_UInt32_toUInt16(0x1234abcd) >>> 0, 0xabcd,
    "UInt32.toUInt16");
  equal(exports.fir_ext_UInt32_toUInt64(0xffffffff), 0xffffffffn,
    "UInt32.toUInt64");
  equal(exports.fir_ext_UInt32_toUSize(0xffffffff), 0xffffffffn,
    "UInt32.toUSize");
  equal(exports.fir_ext_UInt32_add(0xffffffff, 2) >>> 0, 1,
    "UInt32.add wraps");
  equal(exports.fir_ext_UInt32_sub(0, 1) >>> 0, 0xffffffff,
    "UInt32.sub wraps");
  equal(exports.fir_ext_UInt32_land(0xa55aa55a, 0x0ff00ff0) >>> 0,
    0x05500550, "UInt32.land");
  equal(exports.fir_ext_UInt32_xor(0xf0f0f0f0, 0x0ff00ff0) >>> 0,
    0xff00ff00, "UInt32.xor");
  equal(exports.fir_ext_UInt32_shiftRight(0x80000001, 33) >>> 0,
    0x40000000, "UInt32.shiftRight masks count");
  equal(exports.fir_ext_UInt32_decLt(0xffffffff, 0), 0,
    "UInt32.decLt unsigned");
  equal(exports.fir_ext_UInt32_decLe(0xffffffff, 0xffffffff), 1,
    "UInt32.decLe equal");
  equal(exports.fir_ext_UInt32_decLe(0xffffffff, 0), 0,
    "UInt32.decLe false");

  const wideNatural = exports.fir_numeric_make_natural(0x89abcdef, 0x01234567);
  const wide = 0x0123456789abcdefn;
  equal(exports.fir_ext_UInt64_ofNat(wideNatural), wide, "UInt64.ofNat");
  equal(exports.fir_ext_UInt64_toUInt8(wide) >>> 0, 0xef,
    "UInt64.toUInt8");
  equal(exports.fir_ext_UInt64_toUInt16(wide) >>> 0, 0xcdef,
    "UInt64.toUInt16");
  equal(exports.fir_ext_UInt64_toUSize(wide), wide, "UInt64.toUSize");
  equal(exports.fir_ext_UInt64_shiftLeft(1n, 65n), 2n,
    "UInt64.shiftLeft masks count");
  equal(exports.fir_ext_UInt64_shiftRight(0x8000000000000001n, 65n),
    0x4000000000000000n, "UInt64.shiftRight masks count");
  equal(exports.fir_ext_UInt64_decEq(wide, wide), 1, "UInt64.decEq equal");
  equal(exports.fir_ext_UInt64_decEq(wide, wide + 1n), 0,
    "UInt64.decEq unequal");

  equal(view.getBigUint64(0, true), scratch,
    "fixed-width helpers did not restore eight-byte scratch memory");

  return "PASS zero-import resident fixed-width operations";
}

export async function checkFetchedResidentFixedWidth(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentFixedWidth(await response.arrayBuffer());
}
