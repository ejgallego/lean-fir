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

function expectTrap(action, message) {
  try {
    action();
  } catch (error) {
    expect(error instanceof WebAssembly.RuntimeError,
      `${message}: expected WebAssembly.RuntimeError, got ${String(error)}`);
    return;
  }
  throw new Error(`${message}: expected trap`);
}

const float32Buffer = new ArrayBuffer(4);
const float32View = new DataView(float32Buffer);

function float32Bits(value) {
  float32View.setFloat32(0, value, true);
  return float32View.getUint32(0, true);
}

const float64Buffer = new ArrayBuffer(8);
const float64View = new DataView(float64Buffer);

function float64Bits(value) {
  float64View.setFloat64(0, value, true);
  return float64View.getBigUint64(0, true);
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
    "fir_float32_box",
    "fir_float32_unbox",
    "fir_float_box",
    "fir_float_unbox",
    "resident_float32_box_bits_roundtrip",
    "resident_float_box_bits_roundtrip",
    "resident_Float_neg_bits",
    "resident_Float_abs_bits",
    "resident_Float_floor_bits",
    "resident_Float_round_bits",
  ]) {
    equal(typeof exports[name], "function", `missing export ${name}`);
  }
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident Float module does not own memory");

  const frontier = () => exports.fir_heap_frontier() >>> 0;
  const rewind = (address) => exports.fir_heap_rewind(address);
  const boxBytes = 40;

  for (const bits of [
    0x00000000, 0x80000000, 0x00000001, 0x007fffff,
    0x7f7fffff, 0x7f800000, 0xff800000, 0x7fc01234, 0x7fa12345,
  ]) {
    const before = frontier();
    equal(exports.resident_float32_box_bits_roundtrip(bits) >>> 0,
      bits >>> 0, `Float32 box roundtrip 0x${bits.toString(16)}`);
    equal(frontier(), before + boxBytes,
      "Float32 box frontier growth");
    rewind(before);
    equal(frontier(), before, "Float32 box rewind");
  }

  for (const bits of [
    0x0000000000000000n, 0x8000000000000000n, 0x0000000000000001n,
    0x000fffffffffffffn, 0x7fefffffffffffffn, 0x7ff0000000000000n,
    0xfff0000000000000n, 0x7ff8123456789abcn, 0x7ff0123456789abcn,
  ]) {
    const before = frontier();
    equal(BigInt.asUintN(64,
      exports.resident_float_box_bits_roundtrip(bits)), bits,
      `Float box roundtrip 0x${bits.toString(16)}`);
    equal(frontier(), before + boxBytes, "Float box frontier growth");
    rewind(before);
    equal(frontier(), before, "Float box rewind");
  }

  const view = new DataView(exports.memory.buffer);
  const checkHeader = (address, marker, payloadBytes, message) => {
    equal(view.getUint32(address, true), 3, `${message} object kind`);
    equal(view.getUint32(address + 4, true), 2, `${message} live flags`);
    equal(view.getUint32(address + 8, true), 1, `${message} refcount`);
    equal(view.getUint32(address + 12, true), boxBytes,
      `${message} allocation bytes`);
    equal(view.getUint32(address + 16, true), marker, `${message} marker`);
    equal(view.getUint32(address + 20, true), payloadBytes,
      `${message} payload bytes`);
    equal(view.getUint32(address + 24, true), 0, `${message} aux2`);
    equal(view.getUint32(address + 28, true), 0, `${message} aux3`);
  };

  let before = frontier();
  const float32Address = exports.fir_float32_box(Math.fround(-13.25)) >>> 0;
  equal(float32Address, before, "Float32 box allocation address");
  checkHeader(float32Address, 6, 4, "Float32 box");
  equal(view.getUint32(float32Address + 32, true),
    float32Bits(Math.fround(-13.25)), "Float32 box payload bits");
  equal(view.getUint32(float32Address + 36, true), 0,
    "Float32 box zero padding");
  view.setUint32(float32Address + 20, 8, true);
  expectTrap(() => exports.fir_float32_unbox(float32Address),
    "Float32 box malformed width");
  view.setUint32(float32Address + 20, 4, true);
  view.setUint32(float32Address + 36, 1, true);
  expectTrap(() => exports.fir_float32_unbox(float32Address),
    "Float32 box nonzero padding");
  rewind(before);

  before = frontier();
  const floatAddress = exports.fir_float_box(-13.25) >>> 0;
  equal(floatAddress, before, "Float box allocation address");
  checkHeader(floatAddress, 7, 8, "Float box");
  equal(view.getBigUint64(floatAddress + 32, true), float64Bits(-13.25),
    "Float box payload bits");
  view.setUint32(floatAddress + 16, 6, true);
  expectTrap(() => exports.fir_float_unbox(floatAddress),
    "Float box wrong scalar marker");
  rewind(before);

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
