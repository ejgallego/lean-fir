function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function u64(value) {
  return BigInt.asUintN(64, value);
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
    "fir_ext_UInt8_ofNatLT",
    "fir_ext_UInt8_toNat",
    "fir_ext_UInt8_toUInt32",
    "fir_ext_UInt8_toUInt64",
    "fir_ext_UInt8_toUSize",
    "fir_ext_UInt8_decEq",
    "fir_ext_UInt8_decLt",
    "fir_ext_UInt8_decLe",
    "fir_ext_UInt8_shiftRight",
    "fir_ext_UInt8_land",
    "fir_ext_UInt8_lor",
    "fir_ext_UInt16_shiftRight",
    "fir_ext_UInt16_ofNat",
    "fir_ext_UInt16_toUInt8",
    "fir_ext_UInt16_toNat",
    "fir_ext_UInt16_toUInt32",
    "fir_ext_UInt16_toUInt64",
    "fir_ext_UInt16_land",
    "fir_ext_UInt16_xor",
    "fir_ext_UInt16_shiftLeft",
    "fir_ext_UInt16_lor",
    "fir_ext_UInt32_ofNat",
    "fir_ext_UInt32_ofNatLT",
    "fir_ext_UInt32_log2Clz",
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
    "fir_ext_UInt32_shiftLeft",
    "fir_ext_UInt32_lor",
    "fir_ext_UInt32_mul",
    "fir_ext_UInt64_ofNat",
    "fir_ext_UInt64_toUInt8",
    "fir_ext_UInt64_toUInt16",
    "fir_ext_UInt64_toUSize",
    "fir_ext_UInt64_shiftLeft",
    "fir_ext_UInt64_shiftRight",
    "fir_ext_UInt64_decEq",
    "fir_ext_UInt64_add",
    "fir_ext_UInt64_sub",
    "fir_ext_UInt64_land",
    "fir_ext_UInt64_lor",
    "fir_ext_UInt64_xor",
    "fir_ext_UInt64_complement",
    "fir_ext_UInt64_decLt",
    "fir_ext_UInt64_mul",
    "fir_ext_UInt64_ctzFast",
    "fir_ext_UInt64_mod",
    "fir_ext_USize_decLt",
    "fir_ext_USize_add",
    "fir_ext_USize_sub",
    "fir_ext_USize_ofNat",
    "fir_ext_USize_toUInt32",
    "fir_ext_USize_toNat",
    "fir_ext_USize_land",
    "fir_ext_USize_shiftLeft",
    "fir_ext_USize_decLe",
    "fir_ext_USize_decEq",
    "fir_ext_USize_complement",
    "fir_ext_USize_shiftRight",
    "fir_ext_USize_mod",
    "fir_ext_USize_ofNatLT",
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
  equal(exports.fir_ext_UInt16_shiftLeft(0x8001, 17) >>> 0, 2,
    "UInt16.shiftLeft masks count");
  equal(exports.fir_ext_UInt16_lor(0xa500, 0x0a5a) >>> 0, 0xaf5a,
    "UInt16.lor");

  for (const value of [0, 1, 0x7f, 0xff]) {
    const natural = 2 * value + 1;
    equal(exports.fir_ext_UInt8_ofNat(natural) >>> 0, value,
      `UInt8.ofNat(${value})`);
    equal(exports.fir_ext_UInt8_ofNatLT(natural, 0) >>> 0, value,
      `UInt8.ofNatLT(${value})`);
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
  equal(exports.fir_ext_UInt8_decLe(255, 255), 1, "UInt8.decLe equal");
  equal(exports.fir_ext_UInt8_decLe(255, 1), 0, "UInt8.decLe false");
  equal(exports.fir_ext_UInt8_shiftRight(0x81, 9) >>> 0, 0x40,
    "UInt8.shiftRight masks count");
  equal(exports.fir_ext_UInt8_land(0xa5, 0x3c) >>> 0, 0x24,
    "UInt8.land");
  equal(exports.fir_ext_UInt8_lor(0xa5, 0x3c) >>> 0, 0xbd,
    "UInt8.lor");

  equal(naturalValue(exports.memory,
    exports.fir_ext_UInt16_toNat(0xffff)), 0xffffn, "UInt16.toNat");
  equal(exports.fir_ext_UInt16_toUInt32(0xffff) >>> 0, 0xffff,
    "UInt16.toUInt32");
  equal(exports.fir_ext_UInt16_toUInt64(0xffff), 0xffffn,
    "UInt16.toUInt64");

  const naturalMax32 = exports.fir_numeric_make_natural(0xffffffff, 0);
  equal(exports.fir_ext_UInt32_ofNat(naturalMax32) >>> 0, 0xffffffff,
    "UInt32.ofNat upper boundary");
  equal(exports.fir_ext_UInt32_ofNatLT(naturalMax32, 0) >>> 0, 0xffffffff,
    "UInt32.ofNatLT upper boundary");
  for (const [value, expected] of [
    [0, 0],
    [1, 0],
    [2, 1],
    [3, 1],
    [0x80000000, 31],
    [0xffffffff, 31],
  ]) {
    equal(exports.fir_ext_UInt32_log2Clz(value) >>> 0, expected,
      `UInt32.log2Clz(${value})`);
  }
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
  equal(exports.fir_ext_UInt32_shiftLeft(0x80000001, 33) >>> 0, 2,
    "UInt32.shiftLeft masks count");
  equal(exports.fir_ext_UInt32_lor(0xa500a500, 0x0a5a0a5a) >>> 0,
    0xaf5aaf5a, "UInt32.lor");
  for (const [left, right] of [
    [0, 0],
    [0xffffffff, 0],
    [0xffffffff, 2],
    [0x12345678, 0x9abcdef0],
  ]) {
    equal(exports.fir_ext_UInt32_mul(left, right) >>> 0,
      Math.imul(left, right) >>> 0, `UInt32.mul(${left}, ${right})`);
  }

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

  const mask64 = 0xffffffffffffffffn;
  equal(exports.fir_ext_UInt64_add(mask64, 2n), 1n,
    "UInt64.add wraps");
  equal(u64(exports.fir_ext_UInt64_sub(0n, 1n)), mask64,
    "UInt64.sub wraps");
  equal(u64(exports.fir_ext_UInt64_land(
    0xa55aa55aa55aa55an, 0x0ff00ff00ff00ff0n)),
    0x0550055005500550n, "UInt64.land");
  equal(u64(exports.fir_ext_UInt64_lor(
    0xa500a500a500a500n, 0x0a5a0a5a0a5a0a5an)),
    0xaf5aaf5aaf5aaf5an, "UInt64.lor");
  equal(u64(exports.fir_ext_UInt64_xor(
    0xf0f0f0f00f0f0f0fn, 0x0ff00ff0f00ff00fn)),
    0xff00ff00ff00ff00n, "UInt64.xor");
  equal(u64(exports.fir_ext_UInt64_complement(wide)),
    0xfedcba9876543210n, "UInt64.complement");
  equal(exports.fir_ext_UInt64_decLt(0n, mask64), 1,
    "UInt64.decLt true");
  equal(exports.fir_ext_UInt64_decLt(mask64, 0n), 0,
    "UInt64.decLt false");
  for (const [left, right] of [
    [0n, mask64],
    [mask64, 2n],
    [0x0123456789abcdefn, 0xfedcba9876543210n],
    [0x8000000000000000n, 3n],
  ]) {
    equal(u64(exports.fir_ext_UInt64_mul(left, right)),
      (left * right) & mask64, `UInt64.mul(${left}, ${right})`);
  }
  for (const [value, expected] of [
    [0n, 64n],
    [1n, 0n],
    [2n, 1n],
    [0x100000000n, 32n],
    [0x8000000000000000n, 63n],
    [0x0123456789abcdefn, 0n],
  ]) {
    equal(exports.fir_ext_UInt64_ctzFast(value), expected,
      `UInt64.ctzFast(${value})`);
  }
  for (const [left, right] of [
    [0n, 0n],
    [mask64, 0n],
    [mask64, 1n],
    [mask64, 0x100000001n],
    [0x0123456789abcdefn, 0x12345n],
    [0x8000000000000000n, 3n],
  ]) {
    const expected = right === 0n ? left : left % right;
    equal(u64(exports.fir_ext_UInt64_mod(left, right)), expected,
      `UInt64.mod(${left}, ${right})`);
  }
  let randomWord = 0x123456789abcdef0n;
  for (let index = 0; index < 1000; index += 1) {
    randomWord = (randomWord * 6364136223846793005n +
      1442695040888963407n) & mask64;
    const left = randomWord;
    randomWord = (randomWord * 6364136223846793005n +
      1442695040888963407n) & mask64;
    const right = randomWord;
    const expected = right === 0n ? left : left % right;
    equal(u64(exports.fir_ext_UInt64_mod(left, right)), expected,
      `UInt64.mod deterministic differential case ${index}`);
  }

  equal(exports.fir_ext_USize_decLt(1n, mask64), 1,
    "USize.decLt unsigned");
  equal(u64(exports.fir_ext_USize_add(mask64, 2n)), 1n,
    "USize.add wraps");
  equal(u64(exports.fir_ext_USize_sub(0n, 1n)), mask64,
    "USize.sub wraps");
  equal(u64(exports.fir_ext_USize_ofNat(wideNatural)), wide,
    "USize.ofNat");
  equal(u64(exports.fir_ext_USize_ofNatLT(wideNatural, 0)), wide,
    "USize.ofNatLT");
  equal(exports.fir_ext_USize_toUInt32(0x0123456789abcdefn) >>> 0,
    0x89abcdef, "USize.toUInt32");
  equal(naturalValue(exports.memory,
    exports.fir_ext_USize_toNat(wide)), wide, "USize.toNat");
  equal(u64(exports.fir_ext_USize_land(
    0xa55aa55aa55aa55an, 0x0ff00ff00ff00ff0n)),
    0x0550055005500550n, "USize.land");
  equal(u64(exports.fir_ext_USize_shiftLeft(1n, 65n)), 2n,
    "USize.shiftLeft masks count");
  equal(u64(exports.fir_ext_USize_shiftRight(
    0x8000000000000001n, 65n)), 0x4000000000000000n,
    "USize.shiftRight masks count");
  equal(exports.fir_ext_USize_decLe(mask64, mask64), 1,
    "USize.decLe equal");
  equal(exports.fir_ext_USize_decLe(mask64, 0n), 0,
    "USize.decLe false");
  equal(exports.fir_ext_USize_decEq(wide, wide), 1,
    "USize.decEq equal");
  equal(exports.fir_ext_USize_decEq(wide, wide + 1n), 0,
    "USize.decEq unequal");
  equal(u64(exports.fir_ext_USize_complement(0x0123456789abcdefn)),
    0xfedcba9876543210n, "USize.complement");
  for (const [left, right] of [
    [0n, 0n],
    [mask64, 0n],
    [mask64, 0x100000001n],
    [0x0123456789abcdefn, 0x12345n],
  ]) {
    const expected = right === 0n ? left : left % right;
    equal(u64(exports.fir_ext_USize_mod(left, right)), expected,
      `USize.mod(${left}, ${right})`);
  }

  equal(view.getBigUint64(0, true), scratch,
    "fixed-width helpers did not restore eight-byte scratch memory");

  return "PASS zero-import resident fixed-width operations";
}

export async function checkFetchedResidentFixedWidth(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentFixedWidth(await response.arrayBuffer());
}
