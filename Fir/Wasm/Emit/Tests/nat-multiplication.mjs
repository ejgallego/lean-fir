import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { ConcreteHost } from '../../../../integration/talos/artifact/concrete-host.mjs';
import { instantiateModuleArtifact } from '../../../../integration/talos/artifact/module-client.mjs';
import { checkResidentNatArithmetic } from '../../../../integration/talos/artifact/resident-nat-arithmetic-client.mjs';

const path = process.argv[2];
const bytes = await fs.readFile(path);
const manifest = JSON.parse(await fs.readFile(`${path}.json`, 'utf8'));
await checkResidentNatArithmetic({ bytes, manifest });
const host = new ConcreteHost([]);
const { instance } = await instantiateModuleArtifact({ bytes, manifest, host });
const e = instance.exports;
assert.deepEqual(WebAssembly.Module.imports(new WebAssembly.Module(bytes)), []);
const sync = () => host.synchronizeResidentFrontierBeforeImport();
const input = n => { sync(); const p = host.allocateNatural(n); sync(); return p; };
const read = p => { sync(); return p & 1 ? BigInt(p >>> 1) : host.readNatural(p >>> 0); };
const release = p => e.fir_dec_once(p, 1);
const snapshot = p => p & 1 ? null : (() => {
  const h = host.readHeader(p);
  return Buffer.from(new Uint8Array(e.memory.buffer, p, h.bytes));
})();
const digest = createHash('sha256');
let cases = 0;
function check(a, b, alias = false, refs = 1) {
  const x = input(a), y = alias ? x : input(b);
  if (refs !== 1) {
    assert.equal(host.readHeader(x).persistent, false);
    host.writeU32(x + 8, refs);
  }
  const beforeX = snapshot(x), beforeY = snapshot(y);
  for (const mul of [e.fir_nat_mul_generic, e.fir_ext_Nat_mul]) {
    const p = mul(x, y) >>> 0;
    e.fir_big_numeric_validate_natural(p);
    assert.equal(read(p), a * b, `product ${a} * ${b}`);
    if (!(p & 1)) {
      const h = host.readHeader(p);
      assert.equal(h.bytes, 32 + 8 * h.aux1);
      assert.equal(h.aux1, Math.ceil((a * b).toString(2).length / 64));
      assert.equal(h.aux2, 0);
      assert.equal(h.aux3, 0);
      assert.equal(h.persistent, a * b < (1n << 63n));
    }
    digest.update(`${a}:${b}:${read(p)}\n`);
    release(p);
    assert.deepEqual(snapshot(x), beforeX, 'borrowed left changed');
    assert.deepEqual(snapshot(y), beforeY, 'borrowed right changed');
    ++cases;
  }
  release(x);
  for (let n = 1; n < refs; ++n) release(x);
  if (!alias) release(y);
}
const edges = [0n, 1n, 2n, 3n];
for (const bit of [31n, 32n, 63n, 64n, 65n, 127n, 128n, 257n]) {
  edges.push((1n << bit) - 1n, 1n << bit, (1n << bit) + 1n);
}
for (const a of edges) for (const b of edges) check(a, b);
for (const a of edges) check(a, a, true);
check((1n << 130n) + 17n, (1n << 130n) + 17n, true, 3);
let seed = 0x12345678;
const random32 = () => {
  seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5;
  return BigInt(seed >>> 0);
};
const random = n => {
  let r = 0n;
  for (let i = 0; i < n; ++i) r = (r << 32n) | random32();
  return r;
};
for (let i = 1; i <= 96; ++i) check(random(i), random(1 + i % 31));
for (const limbs of [2n, 3n, 8n, 32n, 64n]) {
  const a = (1n << (64n * limbs)) - 1n;
  check(a, a, true); // full carry chain, shared address
}

// Reuse both exact and trimmed construction extents. Poison dead payload bytes
// except the recycler link word, so fresh zero-filled Wasm memory cannot mask
// missing initialization. All input allocation happens before the warm loop.
for (const a of [(1n << 128n) - 1n, 1n << 64n]) {
  const x = input(a), y = input(a + 2n);
  const run = () => {
    const p = e.fir_nat_mul_generic(x, y) >>> 0;
    assert.equal(read(p), a * (a + 2n));
    const h = host.readHeader(p);
    release(p);
    new Uint8Array(e.memory.buffer, p + 36, h.bytes - 36).fill(0xa5);
  };
  for (let i = 0; i < 8; ++i) run();
  const start = e.fir_heap_frontier() >>> 0;
  const capacity = e.memory.buffer.byteLength;
  for (let i = 0; i < 1000; ++i) run();
  assert.equal(e.fir_heap_frontier() >>> 0, start, 'warm frontier must plateau');
  assert.equal(e.memory.buffer.byteLength, capacity, 'warm memory capacity grew');
  release(x); release(y);
}
// Invalid boxed inputs must still be validated even when multiplied by zero.
assert.throws(() => e.fir_nat_mul_generic(8, 1), WebAssembly.RuntimeError);
assert.throws(() => e.fir_nat_mul_generic(1, 8), WebAssembly.RuntimeError);
const malformed = input(1n << 128n);
host.writeU64(malformed + 48, 0n); // noncanonical leading zero
assert.throws(() => e.fir_nat_mul_generic(malformed, 3), WebAssembly.RuntimeError);
release(malformed);
console.log(JSON.stringify({ cases, resultSHA256: digest.digest('hex'),
  wasmBytes: bytes.length, wasmSHA256: createHash('sha256').update(bytes).digest('hex'),
  frontier: e.fir_heap_frontier() >>> 0, memoryCapacity: e.memory.buffer.byteLength,
  reuseRounds: 2000 }));
