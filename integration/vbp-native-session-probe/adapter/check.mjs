import assert from 'node:assert/strict';
import { cpSync, mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { checksumManifest, sha256 } from '../../package-tools/immutable-package.mjs';
import { produce, verifyBaseline } from './package.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../../..');
assert.equal(process.argv.length, 3, 'usage: node check.mjs FROZEN_BASELINE');
const baseline = resolve(process.argv[2]);
const state = join(root, '.deps/utf8-adapter');
mkdirSync(state, { recursive: true });
const packagesDirectory = join(state, 'packages');
const first = produce({ baseline, packagesDirectory });
const second = produce({ baseline, packagesDirectory });
assert.deepEqual(second, first, 'publication must be deterministic');
const bytes = readFileSync(join(first.directory, 'component.wasm'));
const module = new WebAssembly.Module(bytes);
const imports = WebAssembly.Module.imports(module);
assert.equal(imports.filter(x => x.kind === 'function').length, 38);
assert.equal(imports.filter(x => x.kind === 'memory').length, 0);
assert.equal(WebAssembly.Module.exports(module).length, 105);
execFileSync(process.execPath, [join(first.directory, 'smoke.mjs')], { stdio: 'inherit' });

const temporary = mkdtempSync(join(state, 'negative-'));
try {
  const bad = join(temporary, 'baseline');
  cpSync(baseline, bad, { recursive: true });
  writeFileSync(join(bad, 'component.wasm'), Buffer.from('wrong frozen Wasm'));
  assert.throws(() => verifyBaseline(bad), /checksum mismatch/);
  const names = readFileSync(join(bad, 'SHA256SUMS'), 'utf8').trim().split('\n').map(row => row.slice(66));
  writeFileSync(join(bad, 'SHA256SUMS'), checksumManifest(bad, names));
  assert.throws(() => verifyBaseline(bad), /wrong frozen baseline/);

  const modified = join(temporary, 'modified');
  cpSync(first.directory, modified, { recursive: true });
  const host = join(modified, 'host-prototype.mjs');
  const original = readFileSync(host, 'utf8');
  const controls = [
    ['const scratchIndex = stringScratchDepth++', 'const scratchIndex = 0'],
    ['stringScratchDepth = scratchIndex;', 'stringScratchDepth = 0;'],
    ['stringScratch.length = 0;', '/* missing disposal clearing */'],
  ];
  for (const [from, to] of controls) {
    assert.ok(original.includes(from));
    writeFileSync(host, original.replace(from, to));
    const outputNames = readFileSync(join(first.directory, 'SHA256SUMS'), 'utf8').trim().split('\n').map(row => row.slice(66));
    writeFileSync(join(modified, 'SHA256SUMS'), checksumManifest(modified, outputNames));
    assert.throws(() => execFileSync(process.execPath, [join(modified, 'verify.mjs')], { stdio: 'pipe' }));
  }
} finally { rmSync(temporary, { recursive: true, force: true }); }
console.log(JSON.stringify({ pass: true, ...first, deterministic: true,
  negativeControls: 5, sumsSHA256: sha256(readFileSync(join(first.directory, 'SHA256SUMS'))) }));
