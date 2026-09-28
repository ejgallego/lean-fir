import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, copyFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { publishImmutablePackage, sha256 } from '../../../../integration/package-tools/immutable-package.mjs';

const [raw, optimized, directory] = process.argv.slice(2);
assert.ok(raw && optimized && directory, 'expected raw Wasm, optimized Wasm, local package directory');
const git = (...args) => execFileSync('git', args, { encoding: 'utf8' }).trim();
assert.equal(git('status', '--porcelain', '--untracked-files=normal'), '', 'package requires clean source');
const head = git('rev-parse', 'HEAD');
const files = ['nat-multiplication.wasm', 'nat-multiplication-opt.wasm',
  'nat-multiplication.wasm.json', 'BUILD.json', 'smoke.mjs'];
const info = path => {
  const bytes = readFileSync(path), module = new WebAssembly.Module(bytes);
  const imports = WebAssembly.Module.imports(module);
  assert.equal(imports.length, 0);
  return { bytes: bytes.length, sha256: sha256(bytes), imports,
    exports: WebAssembly.Module.exports(module) };
};
const build = {
  kind: 'local production-helper diagnostic; not a consumer release',
  source: { commit: head, dirty: false },
  leanToolchain: readFileSync('lean-toolchain', 'utf8').trim(),
  raw: info(raw), optimized: { ...info(optimized), optimizer: 'pinned Binaryen -O3' },
  entry: 'fir_nat_mul_generic', parameters: ['borrowed tobject', 'borrowed tobject'],
  result: 'owned canonical Nat tobject', limbBits: 64, multiplicationDigitBits: 32,
  memory: 'module-owned; exact-extent recycler; instance-lifetime arena',
  ownership: 'inputs remain borrowed; release result with fir_dec_once(result, 1); promoted values remain persistent',
  proofStatus: 'generation-only; no new W6 multiplication refinement claimed',
};
const result = publishImmutablePackage({
  packagesDirectory: resolve(directory), packageId: `nat-mul-${head}-${build.raw.sha256.slice(0, 12)}`,
  outputNames: files,
  populate(dir) {
    copyFileSync(raw, join(dir, files[0]));
    copyFileSync(optimized, join(dir, files[1]));
    copyFileSync(`${raw}.json`, join(dir, files[2]));
    writeFileSync(join(dir, 'BUILD.json'), JSON.stringify(build, null, 2) + '\n');
    copyFileSync(fileURLToPath(new URL('./nat-multiplication-smoke.mjs', import.meta.url)), join(dir, 'smoke.mjs'));
  },
  validate(dir) { execFileSync(process.execPath, [join(dir, 'smoke.mjs')], { stdio: 'inherit' }); },
});
console.log(result.directory);
