import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdirSync, realpathSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { sha, unique } from './installed-module-inputs.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const state = resolve(here, '../../.deps/native-session-probe');
const out = join(state, 'lifecycle');
mkdirSync(out, { recursive: true });
const rootSource = join(state, 'sources/vbp/src/VersoBlueprintVir/Preview/Renderer.lean');
const rootSetup = join(here, '.lake/build/ir/VersoBlueprintVir/Preview/Renderer.setup.json');
const basicSource = join(state, 'sources/verso/src/verso-manual/VersoManual/Basic.lean');
const basicSetup = join(state, 'sources/verso/.lake/build/ir/VersoManual/Basic.setup.json');
const read = p => JSON.parse(readFileSync(p, 'utf8'));
const file = path => ({ path: realpathSync(path), sha256: sha(readFileSync(path)) });
const identities = [rootSource, rootSetup, basicSource, basicSetup,
  join(state, 'sources/verso/src/verso-manual/VersoManual/Ext.lean'),
  join(state, 'sources/verso/.lake/build/ir/VersoManual/Ext.c')].map(file);
for (const setupPath of [rootSetup, basicSetup]) {
  const setup = read(setupPath);
  assert.deepEqual(setup.dynlibs, []);
  for (const p of setup.plugins) identities.push({ ...file(p.path), initFn: p.initFn ?? null });
}
const ext = unique(read(basicSetup).plugins.filter(p => p.path.endsWith('/verso_VersoManual_Ext.so')), 'actual Ext plugin');
const aggregate = unique(read(rootSetup).plugins.filter(p => p.path.endsWith('/libverso_VersoManual.so')), 'aggregate manual plugin');
const symbols = [aggregate, ext].map(p => ({ path: p.path,
  names: execFileSync('nm', ['-D', '--defined-only', p.path], { encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 })
    .trim().split('\n').map(line => line.trim().split(/\s+/).at(-1))
    .filter(name => name === 'initialize_verso_VersoManual_Ext' ||
      name.endsWith('_Manual_inlineExtensionExt') || name.endsWith('_Manual_blockExtensionExt')).sort(),
}));
for (const s of symbols) assert.deepEqual(s.names, [
  'initialize_verso_VersoManual_Ext', 'lp_verso_Verso_Genre_Manual_blockExtensionExt',
  'lp_verso_Verso_Genre_Manual_inlineExtensionExt',
]);
const cases = ['fresh-basic', 'root-basic', 'basic-basic', 'plugins-root-repeat', 'plugins-root-ext'];
const duplicate = "invalid environment extension, 'Verso.Genre.Manual.inlineExtensionExt' has already been used";
const results = [];
for (const round of ['first', 'repeat']) {
mkdirSync(join(out, round), { recursive: true });
for (const mode of cases) {
  const path = join(out, round, mode + '.json');
  execFileSync('lake', ['--keep-toolchain', '-KpostponeCompile=false', 'env', 'lean', '--run',
    'ExtensionLifecycle.lean', mode, rootSource, rootSetup, basicSource, basicSetup, path],
  { cwd: here, stdio: 'inherit' });
  const result = read(path);
  assert.equal(result.mode, mode);
  assert.equal(result.worklistResumed, false);
  assert.equal(result.registryReset, false);
  assert.equal(result.initial.inlineCount, 0);
  assert.equal(result.initial.blockCount, 0);
  assert.deepEqual(result.initial.manualLibraries, []);
  const failing = mode === 'root-basic' || mode === 'plugins-root-ext';
  assert.equal(result.failure === null, !failing);
  if (failing) assert.ok(result.failure.includes(duplicate));
  assert.equal(result.retainedCaptures, ({
    'fresh-basic': 1, 'root-basic': 1, 'basic-basic': 2,
    'plugins-root-repeat': 0, 'plugins-root-ext': 0,
  })[mode]);
  assert.equal(result.steps.filter(s => !s.ok).length, failing ? 1 : 0);
  const last = result.steps.at(-1);
  assert.equal(last.after.inlineCount, 1);
  assert.equal(last.after.blockCount, 1);
  if (mode === 'plugins-root-ext') {
    assert.equal(last.step, 'plugin:' + ext.path);
    assert.equal(last.before.inlineCount, 1);
    assert.deepEqual(last.before.manualLibraries, [aggregate.path]);
    assert.deepEqual(last.after.manualLibraries, [aggregate.path, ext.path].sort());
  }
  if (mode === 'root-basic') {
    assert.equal(result.steps[0].step, 'capture:VersoBlueprintVir.Preview.Renderer');
    assert.equal(result.steps[0].after.inlineCount, 1);
    assert.deepEqual(result.steps[0].after.manualLibraries, [aggregate.path]);
    assert.equal(last.step, 'capture:VersoManual.Basic');
  }
  if (mode === 'plugins-root-repeat') assert.equal(result.steps.length, 2 * read(rootSetup).plugins.length);
  if (round === 'first') results.push(result);
  else assert.deepEqual(result, results.find(r => r.mode === mode), `${mode}: repeat differs`);
}
}
for (const row of identities) assert.equal(file(row.path).sha256, row.sha256, 'input changed during experiment');
writeFileSync(join(out, 'inputs.json'), JSON.stringify({
  source: read(join(state, 'SOURCE.json')), identities, extPlugin: ext, symbols,
}, null, 2) + '\n');
writeFileSync(join(out, 'summary.json'), JSON.stringify(results.map(r => ({
  mode: r.mode, failure: r.failure, retainedCaptures: r.retainedCaptures,
  steps: r.steps.map(s => ({ step: s.step, ok: s.ok, before: s.before, after: s.after })),
})), null, 2) + '\n');
console.log('PASS five repeated lifecycle controls: aggregate/module plugin collision, not fresh or same-plugin repetition');
