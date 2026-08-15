function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(Object.is(actual, expected),
    `${message}: expected ${String(expected)}, got ${String(actual)}`);
}

function naturalValue(memory, physical) {
  const word = physical >>> 0;
  if ((word & 1) === 1) return BigInt(word >>> 1);
  const view = new DataView(memory.buffer);
  equal(view.getUint32(word, true), 5, "natural object kind");
  equal(view.getUint32(word + 16, true), 1, "one-limb natural marker");
  return view.getBigUint64(word + 32, true);
}

/** Exercise the core-Wasm Float and conversion resident frontier. */
export async function checkResidentFloat(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident Float module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  for (const name of [
    "fir_ext_UInt64_toFloat",
    "fir_ext_Float_add",
    "fir_ext_Float_sub",
    "fir_ext_Float_div",
    "fir_ext_Float_mul",
    "fir_ext_Float_neg",
    "fir_ext_Float_beq",
    "fir_ext_Float_decLt",
    "fir_ext_Float_decLe",
    "fir_ext_Float_abs",
    "fir_ext_Float_sqrt",
    "fir_ext_Float_floor",
    "fir_ext_Float_round",
    "fir_ext_Float_toUInt64",
    "fir_ext_UInt64_toNat",
    "resident_Float_neg_bits",
    "resident_Float_abs_bits",
    "resident_Float_floor_bits",
    "resident_Float_round_bits",
  ]) {
    equal(typeof exports[name], "function", `missing export ${name}`);
  }
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident Float module does not own memory");

  equal(exports.fir_ext_UInt64_toFloat(0n), 0, "UInt64.toFloat zero");
  equal(exports.fir_ext_UInt64_toFloat(0xffffffffffffffffn), 2 ** 64,
    "UInt64.toFloat rounds maximum to binary64");
  equal(exports.fir_ext_Float_add(1.25, 2.5), 3.75, "Float.add");
  equal(exports.fir_ext_Float_sub(1.25, 2.5), -1.25, "Float.sub");
  equal(exports.fir_ext_Float_mul(-3, 2.5), -7.5, "Float.mul");
  equal(exports.fir_ext_Float_div(7.5, 2.5), 3, "Float.div");
  equal(exports.fir_ext_Float_neg(0), -0, "Float.neg preserves signed zero");
  equal(exports.fir_ext_Float_abs(-0), 0, "Float.abs clears the zero sign");
  equal(exports.fir_ext_Float_sqrt(81), 9, "Float.sqrt");
  expect(Number.isNaN(exports.fir_ext_Float_sqrt(-1)),
    "Float.sqrt negative input must return NaN");
  equal(exports.fir_ext_Float_floor(-1.25), -2, "Float.floor");

  const negativeNaN = 0xfff8123456789abcn;
  const positiveNaN = 0x7ff8123456789abcn;
  equal(BigInt.asUintN(64, exports.resident_Float_neg_bits(negativeNaN)),
    positiveNaN, "Float.neg toggles only the sign bit");
  equal(BigInt.asUintN(64, exports.resident_Float_abs_bits(negativeNaN)),
    positiveNaN, "Float.abs clears only the sign bit");
  equal(BigInt.asUintN(64, exports.resident_Float_floor_bits(0x8000000000000000n)),
    0x8000000000000000n, "Float.floor preserves negative zero bits");
  equal(BigInt.asUintN(64, exports.resident_Float_round_bits(0x8000000000000000n)),
    0x8000000000000000n, "Float.round preserves negative zero bits");

  const view = new DataView(exports.memory.buffer);
  const scratch = 0xdecafbad01234567n;
  view.setBigUint64(0, scratch, true);
  equal(exports.fir_ext_Float_beq(-0, 0), 1, "Float.beq signed zero");
  equal(exports.fir_ext_Float_beq(Number.NaN, Number.NaN), 0,
    "Float.beq NaN");
  equal(exports.fir_ext_Float_decLt(-1, 0), 1, "Float.decLt");
  equal(exports.fir_ext_Float_decLe(1, 1), 1, "Float.decLe");
  equal(view.getBigUint64(0, true), scratch,
    "Float decision helper did not restore scratch memory");

  for (const [value, expected] of [
    [0, 0], [-0, -0], [0.25, 0], [-0.25, -0],
    [0.5, 1], [-0.5, -1], [1.5, 2], [2.5, 3], [-2.5, -3],
    [Number.POSITIVE_INFINITY, Number.POSITIVE_INFINITY],
    [Number.NEGATIVE_INFINITY, Number.NEGATIVE_INFINITY],
  ]) {
    equal(exports.fir_ext_Float_round(value), expected,
      `Float.round(${String(value)})`);
  }
  expect(Number.isNaN(exports.fir_ext_Float_round(Number.NaN)),
    "Float.round NaN must remain NaN");

  const maxUInt64 = (1n << 64n) - 1n;
  for (const [value, expected] of [
    [Number.NaN, 0n], [Number.NEGATIVE_INFINITY, 0n], [-1, 0n],
    [-0, 0n], [0, 0n], [1.9, 1n], [42.75, 42n],
    [Number.POSITIVE_INFINITY, maxUInt64], [2 ** 64, maxUInt64],
  ]) {
    equal(BigInt.asUintN(64, exports.fir_ext_Float_toUInt64(value)), expected,
      `Float.toUInt64(${String(value)})`);
  }

  equal(naturalValue(exports.memory, exports.fir_ext_UInt64_toNat(7n)), 7n,
    "UInt64.toNat immediate");
  const large = 0x123456789abcdef0n;
  equal(naturalValue(exports.memory, exports.fir_ext_UInt64_toNat(large)), large,
    "UInt64.toNat heap value");
}
