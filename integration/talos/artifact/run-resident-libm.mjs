import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import {
  STANDARD_LIBM_RUNTIME_DECLARATIONS,
  STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES,
  standardLibmRuntimeCapability,
} from "../../wasm-runtime/contract.mjs";

const [frontierPath, completePath] = process.argv.slice(2);
if (completePath === undefined) {
  throw new Error("usage: node run-resident-libm.mjs FRONTIER COMPLETE");
}

const unary = new Map([
  ["Float.sin", Math.sin],
  ["Float.cos", Math.cos],
  ["Float.acos", Math.acos],
  ["Float.cbrt", Math.cbrt],
  ["Float.log2", Math.log2],
]);
const binary = new Map([["Float.atan2", Math.atan2]]);
const probeName = (name) => `resident_${name.replaceAll(".", "_")}_bits`;
const buffer = new ArrayBuffer(8);
const view = new DataView(buffer);
const bitsOf = (value) => {
  view.setFloat64(0, value, true);
  return view.getBigUint64(0, true);
};
const valueOf = (bits) => {
  view.setBigUint64(0, BigInt.asUintN(64, bits), true);
  return view.getFloat64(0, true);
};
const resultBits = (fn, ...values) => BigInt.asUintN(64,
  fn(...values.map(bitsOf)));
const orderedBits = (bits) => (bits >> 63n) === 0n
  ? bits | (1n << 63n)
  : BigInt.asUintN(64, ~bits);
const ulpDistance = (left, right) => {
  const a = orderedBits(bitsOf(left));
  const b = orderedBits(bitsOf(right));
  return a >= b ? a - b : b - a;
};

const frontierBytes = await readFile(frontierPath);
const completeBytes = await readFile(completePath);
const frontier = await WebAssembly.compile(frontierBytes);
const complete = await WebAssembly.compile(completeBytes);
const expectedImports = STANDARD_LIBM_RUNTIME_DECLARATIONS.map((name) => ({
  module: "lean.extern", name, kind: "function",
}));
assert.deepEqual(WebAssembly.Module.imports(frontier), expectedImports);
assert.deepEqual(WebAssembly.Module.imports(complete), []);
assert.deepEqual(WebAssembly.Module.exports(complete),
  WebAssembly.Module.exports(frontier));
assert.deepEqual(standardLibmRuntimeCapability(
  STANDARD_LIBM_RUNTIME_DECLARATIONS), {
  version: "fir.standard-libm/v2",
  declarations: [...STANDARD_LIBM_RUNTIME_DECLARATIONS],
  reservedMemoryBytes: STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES,
  numericContract: "platform-libm-special-values-and-bounded-error",
});

const imports = Object.fromEntries([...unary, ...binary]);
const frontierInstance = await WebAssembly.instantiate(frontier, {
  "lean.extern": imports,
});
const completeInstance = await WebAssembly.instantiate(complete, {});
const expectedExportNames = [
  ...STANDARD_LIBM_RUNTIME_DECLARATIONS.map(probeName),
  "memory",
];
assert.deepEqual(WebAssembly.Module.exports(complete).map(({ name }) => name),
  expectedExportNames);
assert(frontierInstance.exports.memory instanceof WebAssembly.Memory);
assert(completeInstance.exports.memory instanceof WebAssembly.Memory);

for (const declaration of STANDARD_LIBM_RUNTIME_DECLARATIONS) {
  const name = probeName(declaration);
  const host = frontierInstance.exports[name];
  const wasm = completeInstance.exports[name];
  const samples = declaration === "Float.atan2"
    ? [[0, 1], [-0, 1], [1, -1], [-1, -1], [0.5, 2], [-3, 7]]
    : declaration === "Float.acos"
      ? [[-1], [-0.75], [-0], [0], [0.25], [0.75], [1]]
      : [[-10], [-2], [-1], [-0.5], [-0], [0], [0.5], [1], [2], [10]];
  for (const values of samples) {
    const hostValue = valueOf(resultBits(host, ...values));
    const wasmValue = valueOf(resultBits(wasm, ...values));
    if (Number.isNaN(hostValue)) {
      assert(Number.isNaN(wasmValue), `${declaration} must preserve NaN class`);
    } else if (!Number.isFinite(hostValue) || Object.is(hostValue, 0)) {
      assert(Object.is(wasmValue, hostValue),
        `${declaration} special result mismatch for ${values}`);
    } else {
      assert(ulpDistance(hostValue, wasmValue) <= 8n,
        `${declaration} differs by more than 8 ULP for ${values}`);
    }
  }
}

const wasm = completeInstance.exports;
assert.equal(resultBits(wasm[probeName("Float.sin")], -0),
  0x8000000000000000n);
assert.equal(resultBits(wasm[probeName("Float.cos")], -0),
  0x3ff0000000000000n);
assert.equal(resultBits(wasm[probeName("Float.acos")], 1), 0n);
assert.equal(resultBits(wasm[probeName("Float.atan2")], -0, 1),
  0x8000000000000000n);
assert.equal(resultBits(wasm[probeName("Float.cbrt")], -0),
  0x8000000000000000n);
assert.equal(resultBits(wasm[probeName("Float.log2")], 1), 0n);
assert.equal(valueOf(resultBits(wasm[probeName("Float.log2")], 0)),
  Number.NEGATIVE_INFINITY);
assert(Number.isNaN(valueOf(resultBits(wasm[probeName("Float.acos")], 2))));

console.log("resident libm frontier checks passed");
