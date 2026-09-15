import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync, mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { sha, unique } from './installed-module-inputs.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const state = resolve(here, '../../.deps/native-session-probe');
const out = join(state, 'module-product');
mkdirSync(out, { recursive: true });
const resolver = join(here, 'module-product-inputs.mjs');
execFileSync('node', [resolver, '--prepare'], { stdio: 'inherit' });
const catalog = JSON.parse(readFileSync(join(out, 'catalog.json'), 'utf8'));
const rootModule = 'VersoBlueprintVir.Preview.Renderer';
const setup = unique(catalog.setups[rootModule], rootModule);
const source = join(state, 'sources/vbp/src/VersoBlueprintVir/Preview/Renderer.lean');
for (const round of ['first', 'repeat']) {
  execFileSync('lake', ['--keep-toolchain', '-KpostponeCompile=false', 'env', 'lean', '--run',
    'ModuleProduct.lean', source, setup.path, resolver, join(out, round)],
  { cwd: here, stdio: 'inherit' });
}
const hashes = {};
for (const file of ['root.lcnf', 'product.lcnf', 'product.json']) {
  const hash = sha(readFileSync(join(out, 'first', file)));
  assert.equal(hash, sha(readFileSync(join(out, 'repeat', file))), `${file}: nondeterministic`);
  hashes[file] = hash;
}
assert.equal(hashes['root.lcnf'], '819fed859b7d21f3988072f7be53969705614de8d047f41b6c8b8bc488704073');
const result = JSON.parse(readFileSync(join(out, 'first/product.json'), 'utf8'));
assert.equal(new Set(result.modules.map(m => m.name)).size, result.modules.length, 'owner captured twice');
assert.equal(new Set(result.bodies.map(b => b.name)).size, result.bodies.length, 'duplicate body');
assert.equal(new Set(result.frontier.map(b => b.name)).size, result.frontier.length, 'duplicate signature');
assert.equal(result.lowered, false);
assert.equal(result.hostProfileAdmitted, false);
assert.equal(result.negativeControls, true);
assert.equal(result.modules[0].name, rootModule);
assert.ok(result.bodies.some(b => b.name === result.entry));
assert.ok(result.bodies.every(b => result.modules.some(m => m.name === b.owner)));
assert.ok(result.selections.every(s => result.bodies.some(b => b.name === s.name && b.owner === s.module)));
assert.ok(result.frontier.every(e => !result.bodies.some(b => b.name === e.name)));
assert.equal(result.complete, result.failure === null);
if (result.complete) assert.ok(result.frontier.every(r => r.category !== 'source pending'));
const counts = {};
for (const e of result.frontier) counts[e.category] = (counts[e.category] ?? 0) + 1;
// This checkpoint accepts the recorded stop, not an arbitrary repeatable error.
// A later diagnostic repair must review and deliberately advance this boundary.
assert.equal(result.complete, false);
assert.equal(result.failure, 'compiler diagnostic in VersoManual.Basic');
assert.equal(result.modules.length, 26);
assert.equal(result.selections.length, 74);
assert.equal(result.bodies.length, 1201);
assert.deepEqual(counts, {
  'runtime/primitive boundary': 74, 'VIR boundary': 12, 'source pending': 25,
});
assert.equal(hashes['product.lcnf'], 'fdb34c2cb7a5366c6d60258d17a46e15413416ba91e43a9e38e66a1dd1a7d1f3');
writeFileSync(join(out, 'summary.json'), JSON.stringify({ complete: result.complete, failure: result.failure,
  modules: result.modules.length, bodies: result.bodies.length, frontier: result.frontier.length,
  selections: result.selections.length, counts, hashes }, null, 2) + '\n');
console.log(JSON.stringify({ complete: result.complete, failure: result.failure, modules: result.modules.length,
  bodies: result.bodies.length, frontier: result.frontier.length, counts }, null, 2));
console.log('PASS deterministic fail-closed module-product experiment (not a Wasm acceptance)');
