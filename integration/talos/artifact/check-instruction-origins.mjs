import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

const [wasmPath, originsPath] = process.argv.slice(2);
assert(wasmPath !== undefined && originsPath !== undefined,
  "usage: node check-instruction-origins.mjs MODULE.wasm ORIGINS.json");

const bytes = readFileSync(wasmPath);
const table = JSON.parse(readFileSync(originsPath, "utf8"));
const module = new WebAssembly.Module(bytes);
const functionImports = WebAssembly.Module.imports(module)
  .filter(({ kind }) => kind === "function").length;
const functionExports = new Set(WebAssembly.Module.exports(module)
  .filter(({ kind }) => kind === "function").map(({ name }) => name));

assert.equal(table.schema, "fir.wasm.instruction-origins/v1");
assert.equal(table.artifact.byteLength, bytes.length);
assert.equal(table.artifact.functionImports, functionImports);
assert.equal(table.artifact.definedFunctions, table.functions.length);
assert.deepEqual(table.encoding, {
  functionOrder: "defined-function-order",
  originOrder: "symbolic-preorder",
  originRow: ["absoluteOpcodeOffset", "encodedSize", "opcodeBytes"],
});

let originCount = 0;
let previousOffset = -1;
const names = new Set();
const sources = new Set();
for (const [ordinal, function_] of table.functions.entries()) {
  assert.equal(function_.index, functionImports + ordinal,
    "function index is not in emitter order");
  assert.equal(typeof function_.name, "string");
  assert(function_.name.length > 0, "function name is empty");
  assert(!names.has(function_.name), `duplicate function ${function_.name}`);
  names.add(function_.name);
  assert(["lean-source", "resident-helper", "unclassified-definition"]
    .includes(function_.kind), `invalid function kind ${function_.kind}`);
  assert.equal(function_.public, functionExports.has(function_.name),
    `public classification drift for ${function_.name}`);
  assert.equal(function_.source,
    `fir-wasm-origin/${function_.index}/${function_.name}`);
  assert(!sources.has(function_.source),
    `duplicate synthetic source ${function_.source}`);
  sources.add(function_.source);
  assert(Array.isArray(function_.origins));
  for (const [preorder, row] of function_.origins.entries()) {
    assert(Array.isArray(row) && row.length === 3,
      `invalid origin row ${function_.name}:${preorder + 1}`);
    const [offset, encodedSize, opcode] = row;
    assert(Number.isSafeInteger(offset) && offset >= 0);
    assert(Number.isSafeInteger(encodedSize) && encodedSize > 0);
    assert(Array.isArray(opcode) && opcode.length > 0);
    assert(opcode.every(byte => Number.isSafeInteger(byte) &&
      byte >= 0 && byte <= 255));
    assert(offset > previousOffset,
      `origin offsets are not strictly increasing at ${function_.name}:${preorder + 1}`);
    previousOffset = offset;
    assert(offset + opcode.length <= bytes.length,
      `origin opcode exceeds module at ${function_.name}:${preorder + 1}`);
    assert.deepEqual([...bytes.subarray(offset, offset + opcode.length)], opcode,
      `origin opcode drift at ${function_.name}:${preorder + 1}`);
    originCount += 1;
  }
}
assert.equal(originCount, table.artifact.originCount);

console.log(`instruction origins: ${table.functions.length} functions, ` +
  `${originCount} origins, ${bytes.length} Wasm bytes`);
