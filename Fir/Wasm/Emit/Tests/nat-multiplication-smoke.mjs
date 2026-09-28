import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { createHash } from 'node:crypto';

const root = new URL('./', import.meta.url);
for (const line of (await fs.readFile(new URL('SHA256SUMS', root), 'utf8')).trim().split('\n')) {
  const [hash, name] = line.split('  ');
  assert.equal(createHash('sha256').update(await fs.readFile(new URL(name, root))).digest('hex'), hash);
}
for (const name of ['nat-multiplication.wasm', 'nat-multiplication-opt.wasm']) {
  const bytes = await fs.readFile(new URL(name, root));
  const module = new WebAssembly.Module(bytes);
  assert.deepEqual(WebAssembly.Module.imports(module), []);
  const e = new WebAssembly.Instance(module).exports;
  const encode = n => {
    if (n < (1n << 64n)) return e.fir_numeric_make_natural(
      Number(n & 0xffffffffn), Number(n >> 32n)) >>> 0;
    const count = Math.ceil(n.toString(2).length / 64);
    const p = e.fir_big_numeric_allocate(5, 2, 0, count) >>> 0;
    const view = new DataView(e.memory.buffer);
    for (let i = 0; i < count; ++i, n >>= 64n) {
      view.setBigUint64(p + 32 + 8 * i, n & ((1n << 64n) - 1n), true);
    }
    return p;
  };
  const decode = p => {
    e.fir_big_numeric_validate_natural(p);
    if (p & 1) return BigInt(p >>> 1);
    const view = new DataView(e.memory.buffer);
    let n = 0n;
    for (let i = view.getUint32(p + 20, true) - 1; i >= 0; --i) {
      n = (n << 64n) | view.getBigUint64(p + 32 + 8 * i, true);
    }
    return n;
  };
  let cases = 0;
  for (const a of [0n, 1n, 2n, (1n << 31n)-1n, 1n << 63n,
    (1n << 64n)-1n, (1n << 257n)+13n, (1n << 4096n)-1n]) {
    for (const b of [0n, 1n, 3n, (1n << 65n)-1n, a]) {
      const x = encode(a), y = encode(b);
      for (const mul of [e.fir_nat_mul_generic, e.fir_ext_Nat_mul]) {
        const p = mul(x, y) >>> 0;
        assert.equal(decode(p), a * b);
        e.fir_dec_once(p, 1);
        ++cases;
      }
      e.fir_dec_once(x, 1); e.fir_dec_once(y, 1);
    }
  }
  console.log(`PASS ${name}: ${cases} independent products; zero imports`);
}
