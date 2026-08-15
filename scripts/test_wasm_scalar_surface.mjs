import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const path = process.argv[2];
if (!path) throw new Error("usage: test_wasm_scalar_surface.mjs <module.wasm>");

const bytes = await readFile(path);
assert.equal(WebAssembly.validate(bytes), true, "scalar surface is not standard Wasm");
const { instance } = await WebAssembly.instantiate(bytes);
const wasm = instance.exports;
const called = new Set();

function call(name, ...args) {
  called.add(name);
  const fn = wasm[name];
  assert.equal(typeof fn, "function", `missing export ${name}`);
  return fn(...args);
}

const u32 = value => value >>> 0;
const u64 = value => BigInt.asUintN(64, value);
const s64 = value => BigInt.asIntN(64, value);
const f32 = Math.fround;
const mask64 = (1n << 64n) - 1n;

assert.equal(call("surfaceF32Const"), 1);
assert.equal(call("surfaceF64Const"), 1);

assert.equal(call("surfaceI32Eqz", 0), 1);
assert.equal(call("surfaceI32Clz", 1), 31);
assert.equal(call("surfaceI32Ctz", 8), 3);
assert.equal(call("surfaceI32Popcnt", 0xf0), 4);

const i32Comparisons = [
  ["surfaceI32Eq", 7, 7, 1], ["surfaceI32Ne", 7, 8, 1],
  ["surfaceI32LtS", -1, 0, 1], ["surfaceI32LtU", -1, 0, 0],
  ["surfaceI32GtS", 0, -1, 1], ["surfaceI32GtU", -1, 0, 1],
  ["surfaceI32LeS", -1, -1, 1], ["surfaceI32LeU", 1, 2, 1],
  ["surfaceI32GeS", 2, 1, 1], ["surfaceI32GeU", -1, 0, 1],
];
for (const [name, left, right, expected] of i32Comparisons)
  assert.equal(call(name, left, right), expected, name);

assert.equal(u32(call("surfaceI32Add", 0xffffffff, 2)), 1);
assert.equal(u32(call("surfaceI32Sub", 0, 1)), 0xffffffff);
assert.equal(u32(call("surfaceI32Mul", 0x80000000, 2)), 0);
assert.equal(call("surfaceI32DivS", -7, 3), -2);
assert.equal(u32(call("surfaceI32DivU", 0xffffffff, 3)), 1431655765);
assert.equal(call("surfaceI32RemS", -7, 3), -1);
assert.equal(u32(call("surfaceI32RemU", 0xffffffff, 16)), 15);
assert.equal(u32(call("surfaceI32And", 0xf0f0, 0x0ff0)), 0x00f0);
assert.equal(u32(call("surfaceI32Or", 0xf000, 0x0f00)), 0xff00);
assert.equal(u32(call("surfaceI32Xor", 0xffff, 0x0f0f)), 0xf0f0);
assert.equal(u32(call("surfaceI32Shl", 1, 4)), 16);
assert.equal(call("surfaceI32ShrS", -16, 2), -4);
assert.equal(u32(call("surfaceI32ShrU", -16, 2)), 0x3ffffffc);
assert.equal(u32(call("surfaceI32Rotl", 0x12345678, 8)), 0x34567812);
assert.equal(u32(call("surfaceI32Rotr", 0x12345678, 8)), 0x78123456);

assert.equal(call("surfaceI64Eqz", 0n), 1);
assert.equal(call("surfaceI64Clz", 1n), 63n);
assert.equal(call("surfaceI64Ctz", 8n), 3n);
assert.equal(call("surfaceI64Popcnt", 0xf0n), 4n);

const i64Comparisons = [
  ["surfaceI64Eq", 7n, 7n, 1], ["surfaceI64Ne", 7n, 8n, 1],
  ["surfaceI64LtS", -1n, 0n, 1], ["surfaceI64LtU", -1n, 0n, 0],
  ["surfaceI64GtS", 0n, -1n, 1], ["surfaceI64GtU", -1n, 0n, 1],
  ["surfaceI64LeS", -1n, -1n, 1], ["surfaceI64LeU", 1n, 2n, 1],
  ["surfaceI64GeS", 2n, 1n, 1], ["surfaceI64GeU", -1n, 0n, 1],
];
for (const [name, left, right, expected] of i64Comparisons)
  assert.equal(call(name, left, right), expected, name);

assert.equal(u64(call("surfaceI64Add", -1n, 2n)), 1n);
assert.equal(u64(call("surfaceI64Sub", 0n, 1n)), mask64);
assert.equal(u64(call("surfaceI64Mul", 1n << 63n, 2n)), 0n);
assert.equal(call("surfaceI64DivS", -7n, 3n), -2n);
assert.equal(u64(call("surfaceI64DivU", -1n, 3n)), 6148914691236517205n);
assert.equal(call("surfaceI64RemS", -7n, 3n), -1n);
assert.equal(u64(call("surfaceI64RemU", -1n, 16n)), 15n);
assert.equal(u64(call("surfaceI64And", 0xf0f0n, 0x0ff0n)), 0x00f0n);
assert.equal(u64(call("surfaceI64Or", 0xf000n, 0x0f00n)), 0xff00n);
assert.equal(u64(call("surfaceI64Xor", 0xffffn, 0x0f0fn)), 0xf0f0n);
assert.equal(u64(call("surfaceI64Shl", 1n, 4n)), 16n);
assert.equal(call("surfaceI64ShrS", -16n, 2n), -4n);
assert.equal(u64(call("surfaceI64ShrU", -16n, 2n)), 0x3ffffffffffffffcn);
assert.equal(u64(call("surfaceI64Rotl", 0x0123456789abcdefn, 8n)), 0x23456789abcdef01n);
assert.equal(u64(call("surfaceI64Rotr", 0x0123456789abcdefn, 8n)), 0xef0123456789abcdn);

const floatUnary = [
  ["Abs", -3.5, 3.5], ["Neg", 3.5, -3.5], ["Ceil", 1.25, 2],
  ["Floor", 1.75, 1], ["Trunc", -1.75, -1], ["Nearest", 2.5, 2],
  ["Sqrt", 9, 3],
];
for (const [suffix, value, expected] of floatUnary) {
  assert.equal(call(`surfaceF32${suffix}`, f32(value)), f32(expected));
  assert.equal(call(`surfaceF64${suffix}`, value), expected);
}

const floatComparisons = [
  ["Eq", 2, 2, 1], ["Ne", 2, 3, 1], ["Lt", 2, 3, 1],
  ["Gt", 3, 2, 1], ["Le", 2, 2, 1], ["Ge", 2, 2, 1],
];
for (const [suffix, left, right, expected] of floatComparisons) {
  assert.equal(call(`surfaceF32${suffix}`, f32(left), f32(right)), expected);
  assert.equal(call(`surfaceF64${suffix}`, left, right), expected);
}

const floatBinary = [
  ["Add", 1.5, 2.25, 3.75], ["Sub", 5.5, 2.25, 3.25],
  ["Mul", 1.5, 2, 3], ["Div", 7.5, 2.5, 3],
  ["Min", 3, 2, 2], ["Max", 3, 2, 3], ["Copysign", 3, -2, -3],
];
for (const [suffix, left, right, expected] of floatBinary) {
  assert.equal(call(`surfaceF32${suffix}`, f32(left), f32(right)), f32(expected));
  assert.equal(call(`surfaceF64${suffix}`, left, right), expected);
}

assert.equal(u32(call("surfaceI32WrapI64", 0x100000001n)), 1);
assert.equal(call("surfaceI64ExtendI32S", -1), -1n);
assert.equal(u64(call("surfaceI64ExtendI32U", -1)), 0xffffffffn);
assert.equal(call("surfaceI32Extend8S", 0xff), -1);
assert.equal(call("surfaceI32Extend16S", 0xffff), -1);
assert.equal(call("surfaceI64Extend8S", 0xffn), -1n);
assert.equal(call("surfaceI64Extend16S", 0xffffn), -1n);
assert.equal(call("surfaceI64Extend32S", 0xffffffffn), -1n);

assert.equal(call("surfaceF32ConvertI32S", -17), -17);
assert.equal(call("surfaceF32ConvertI32U", -1), f32(0xffffffff));
assert.equal(call("surfaceF32ConvertI64S", -17n), -17);
assert.equal(call("surfaceF32ConvertI64U", 17n), 17);
assert.equal(call("surfaceF64ConvertI32S", -17), -17);
assert.equal(call("surfaceF64ConvertI32U", -1), 0xffffffff);
assert.equal(call("surfaceF64ConvertI64S", -17n), -17);
assert.equal(call("surfaceF64ConvertI64U", 17n), 17);

assert.equal(call("surfaceI32TruncF32S", f32(-17.75)), -17);
assert.equal(u32(call("surfaceI32TruncF32U", f32(17.75))), 17);
assert.equal(call("surfaceI32TruncF64S", -17.75), -17);
assert.equal(u32(call("surfaceI32TruncF64U", 17.75)), 17);
assert.equal(call("surfaceI64TruncF32S", f32(-17.75)), -17n);
assert.equal(u64(call("surfaceI64TruncF32U", f32(17.75))), 17n);
assert.equal(call("surfaceI64TruncF64S", -17.75), -17n);
assert.equal(u64(call("surfaceI64TruncF64U", 17.75)), 17n);

assert.equal(call("surfaceI32TruncSatF32S", Infinity), 0x7fffffff);
assert.equal(u32(call("surfaceI32TruncSatF32U", Infinity)), 0xffffffff);
assert.equal(call("surfaceI32TruncSatF64S", -Infinity), -0x80000000);
assert.equal(u32(call("surfaceI32TruncSatF64U", -Infinity)), 0);
assert.equal(call("surfaceI64TruncSatF32S", Infinity), 0x7fffffffffffffffn);
assert.equal(u64(call("surfaceI64TruncSatF32U", Infinity)), mask64);
assert.equal(call("surfaceI64TruncSatF64S", -Infinity), -0x8000000000000000n);
assert.equal(u64(call("surfaceI64TruncSatF64U", -Infinity)), 0n);

assert.equal(call("surfaceF32DemoteF64", 1.337), f32(1.337));
assert.equal(call("surfaceF64PromoteF32", f32(1.337)), f32(1.337));
assert.equal(u32(call("surfaceI32ReinterpretF32", 1)), 0x3f800000);
assert.equal(u64(call("surfaceI64ReinterpretF64", 1)), 0x3ff0000000000000n);
assert.equal(call("surfaceF32ReinterpretI32", 0x3f800000), 1);
assert.equal(call("surfaceF64ReinterpretI64", 0x3ff0000000000000n), 1);

call("surfaceI32Store", 0, 0x89abcdef);
assert.equal(u32(call("surfaceI32Load", 0)), 0x89abcdef);
call("surfaceI32Store8", 8, 0xff);
assert.equal(call("surfaceI32Load8S", 8), -1);
assert.equal(u32(call("surfaceI32Load8U", 8)), 0xff);
call("surfaceI32Store16", 16, 0xffff);
assert.equal(call("surfaceI32Load16S", 16), -1);
assert.equal(u32(call("surfaceI32Load16U", 16)), 0xffff);

call("surfaceI64Store", 24, -1n);
assert.equal(u64(call("surfaceI64Load", 24)), mask64);
call("surfaceI64Store8", 40, 0xffn);
assert.equal(call("surfaceI64Load8S", 40), -1n);
assert.equal(u64(call("surfaceI64Load8U", 40)), 0xffn);
call("surfaceI64Store16", 48, 0xffffn);
assert.equal(call("surfaceI64Load16S", 48), -1n);
assert.equal(u64(call("surfaceI64Load16U", 48)), 0xffffn);
call("surfaceI64Store32", 56, 0xffffffffn);
assert.equal(call("surfaceI64Load32S", 56), -1n);
assert.equal(u64(call("surfaceI64Load32U", 56)), 0xffffffffn);

call("surfaceF32Store", 64, f32(1.337));
assert.equal(call("surfaceF32Load", 64), f32(1.337));
call("surfaceF64Store", 72, 1.337);
assert.equal(call("surfaceF64Load", 72), 1.337);

const pages = call("surfaceMemorySize");
assert.equal(pages, 1);
assert.equal(call("surfaceMemoryGrow", 1), pages);
assert.equal(wasm.memory.buffer.byteLength, 2 * 65536);

const functionExports = Object.entries(wasm)
  .filter(([, value]) => typeof value === "function")
  .map(([name]) => name);
assert.equal(functionExports.length, 163);
assert.deepEqual(functionExports.filter(name => !called.has(name)), [],
  "every scalar export must be executed by this regression");

console.log(`scalar Wasm surface: ${called.size} functions, ${bytes.length} bytes, all passed`);
