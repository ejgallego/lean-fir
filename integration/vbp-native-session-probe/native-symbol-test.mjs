import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const bytes = readFileSync(process.argv[2]);
assert.ok(WebAssembly.validate(bytes));
const module = new WebAssembly.Module(bytes);
assert.deepEqual(WebAssembly.Module.imports(module), []);
const instance = new WebAssembly.Instance(module, {});
const entry = instance.exports['NativeSymbolTests.externalDifference'];
assert.equal(typeof entry, 'function');
for (const [a, b] of [[7, 2], [2, 7], [0, 0], [0xffffffff, 1], [0, 0xffffffff]]) {
  assert.equal(entry(a, b) >>> 0, (a - b) >>> 0);
}
console.log('PASS native-symbol typed forwarding in Wasm (argument order and uint32 wraparound)');
