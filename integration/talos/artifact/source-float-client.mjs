import assert from "node:assert/strict";

const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const NATURAL_KIND = 5;
const LIVE_FLAG = 2;
const BIG_NATURAL_MARKER = 2;
const MAX_IMMEDIATE = 0x7fffffffn;
const MAX_PROMOTED = 0x7fffffffffffffffn;

function encodeNatural(exports, value) {
  const natural = BigInt(value);
  assert.ok(natural >= 0n, "natural input must be nonnegative");
  if (natural <= MAX_IMMEDIATE) return Number(natural * 2n + 1n);
  if (natural <= MAX_PROMOTED) {
    const bytes = HEADER_BYTES + SLOT_BYTES;
    const address = exports.fir_heap_alloc(bytes) >>> 0;
    const view = new DataView(exports.memory.buffer);
    for (let offset = 0; offset < bytes; offset += 4) {
      view.setUint32(address + offset, 0, true);
    }
    view.setUint32(address, NATURAL_KIND, true);
    view.setUint32(address + 4, LIVE_FLAG + 1, true);
    view.setUint32(address + 12, bytes, true);
    view.setUint32(address + 16, 1, true);
    view.setUint32(address + 20, 1, true);
    view.setBigUint64(address + HEADER_BYTES, natural, true);
    return address;
  }
  const limbs = [];
  let remaining = natural;
  while (remaining !== 0n) {
    limbs.push(BigInt.asUintN(64, remaining));
    remaining >>= 64n;
  }
  const bytes = HEADER_BYTES + SLOT_BYTES * limbs.length;
  const address = exports.fir_heap_alloc(bytes) >>> 0;
  const view = new DataView(exports.memory.buffer);
  for (let offset = 0; offset < bytes; offset += 4) {
    view.setUint32(address + offset, 0, true);
  }
  view.setUint32(address, NATURAL_KIND, true);
  view.setUint32(address + 4, LIVE_FLAG, true);
  view.setUint32(address + 8, 1, true);
  view.setUint32(address + 12, bytes, true);
  view.setUint32(address + 16, BIG_NATURAL_MARKER, true);
  view.setUint32(address + 20, limbs.length, true);
  limbs.forEach((limb, index) => {
    view.setBigUint64(address + HEADER_BYTES + SLOT_BYTES * index, limb, true);
  });
  return address;
}

function expectTrap(action, label) {
  assert.throws(action, WebAssembly.RuntimeError, `${label} did not trap`);
}

export async function checkSourceFloatConversions(bytes, oracle) {
  const module = await WebAssembly.compile(bytes);
  assert.equal(WebAssembly.Module.imports(module).length, 0,
    "source Float conversion module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  assert.ok(exports.memory instanceof WebAssembly.Memory,
    "source Float conversion module does not own memory");
  const ofNat = exports["Float.ofNat._fir_bit_exact"];
  const ofScientific = exports["Float.ofScientific._fir_bit_exact"];
  assert.equal(typeof ofNat, "function", "missing bit-exact Float.ofNat facade");
  assert.equal(typeof ofScientific, "function",
    "missing bit-exact Float.ofScientific facade");

  for (const test of oracle.ofNat) {
    const input = encodeNatural(exports, BigInt(test.value));
    let actual;
    try {
      actual = ofNat(input);
    } catch (error) {
      throw new Error(`Float.ofNat(${test.value}) trapped`, { cause: error });
    }
    assert.equal(BigInt.asUintN(64, actual), BigInt(test.bits),
      `Float.ofNat(${test.value}) bits`);
  }
  for (const test of oracle.ofScientific) {
    const mantissa = encodeNatural(exports, BigInt(test.mantissa));
    const exponent = encodeNatural(exports, BigInt(test.exponent));
    let actual;
    try {
      actual = ofScientific(mantissa, test.hasDot ? 1 : 0, exponent);
    } catch (error) {
      throw new Error(
        `Float.ofScientific(${test.mantissa}, ${test.hasDot}, ${test.exponent}) trapped`,
        { cause: error });
    }
    assert.equal(BigInt.asUintN(64, actual), BigInt(test.bits),
      `Float.ofScientific(${test.mantissa}, ${test.hasDot}, ${test.exponent}) bits`);
  }

  expectTrap(() => ofNat(0), "Float.ofNat malformed Natural");
  expectTrap(() => ofScientific(0, 0, encodeNatural(exports, 0n)),
    "Float.ofScientific malformed mantissa");
  expectTrap(() => ofScientific(encodeNatural(exports, 1n), 0, 0),
    "Float.ofScientific malformed exponent");

  return "PASS upstream source-compiled Float construction is bit-exact";
}
