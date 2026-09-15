import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { deriveInputs, validateInputs, sha, owners, unique } from './installed-module-inputs.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const state = resolve(here, '../../.deps/native-session-probe');
const out = join(state, 'installed-inputs');
mkdirSync(out, { recursive: true });
const prior = JSON.parse(readFileSync(join(state, 'assembly/feasibility.json'), 'utf8'));
const inputs = deriveInputs(prior.frontier);
validateInputs(inputs);
assert.deepEqual(inputs, deriveInputs(prior.frontier), 'nondeterministic input derivation');
const put = (path, data) => writeFileSync(path, JSON.stringify(data, null, 2) + '\n');
const inputFile = join(out, 'derived-inputs.json');
put(inputFile, inputs);
function negative(mutate, pattern) {
  const bad = structuredClone(inputs);
  mutate(bad);
  assert.throws(() => validateInputs(bad), pattern);
}
negative(x => x.revision = 'stale', /stale revision/);
negative(x => x.options['interpreter.prefer_native'] = true, /deep-equal/);
negative(x => x.modules[0].sourceSha256 = 'stale', /stale source/);
negative(x => x.modules[0].artifacts[0].sha256 = 'stale', /stale artifact/);
negative(x => x.modules[0].source = join(out, 'missing.lean'), /missing source/);
negative(x => x.modules[1] = x.modules[0], /ambiguous module/);
negative(x => x.dependencies[0].artifacts[0].sha256 = 'stale', /stale dependency artifact/);
assert.throws(() => unique([], 'setup'), /missing or ambiguous/);
assert.throws(() => unique(['a', 'b'], 'setup'), /missing or ambiguous/);
const lean = (file, name, target) => execFileSync('lake', ['--keep-toolchain', '-KpostponeCompile=false',
  'env', 'lean', '--run', 'InstalledModuleCapture.lean', file, name, target],
{ cwd: here, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 });
// All input checks happen before the first actual capture frontend.
for (const name of owners.keys()) process.stdout.write(lean(inputFile, name, '--verify'));
const bad = structuredClone(inputs);
bad.modules[0].imports = [];
const badFile = join(out, 'bad-imports.json');
put(badFile, bad);
assert.throws(() => lean(badFile, 'Init.Data.Repr', '--verify'), /recorded import provenance mismatch/);
const results = [];
for (const name of owners.keys()) {
  for (const round of ['first', 'repeat']) {
    validateInputs(inputs);
    const target = join(out, round, name);
    // Stop immediately on the first new compiler diagnostic. Do not try the
    // remaining owners or admit them as capture-resolvable after a failure.
    try { process.stdout.write(lean(inputFile, name, target)); }
    catch (error) {
      writeFileSync(join(out, 'first-diagnostic.txt'), `${error.stdout ?? ''}\n${error.stderr ?? ''}`);
      put(join(out, 'status.json'), { complete: false, stoppedAt: name, completed: results });
      throw error;
    }
  }
  const first = join(out, 'first', name), repeat = join(out, 'repeat', name);
  const hashes = {};
  for (const file of readdirSync(first).sort()) {
    const hash = sha(readFileSync(join(first, file)));
    assert.equal(hash, sha(readFileSync(join(repeat, file))), `${name}/${file}: nondeterministic capture`);
    hashes[file] = hash;
  }
  results.push({ name, hashes, ...JSON.parse(readFileSync(join(first, 'capture.json'), 'utf8')) });
  put(join(out, 'status.json'), { complete: false, completed: results });
}
const frontier = prior.frontier.map(row => owners.has(row.module) && row.category === 'unavailable/ambiguous input'
  ? { ...row, category: 'capture-resolvable owning module', provider: inputs.kind } : row);
const counts = {};
for (const row of frontier) counts[row.category] = (counts[row.category] ?? 0) + 1;
assert.deepEqual(counts, { 'capture-resolvable owning module': 31, 'runtime/primitive boundary': 6, 'VIR boundary': 4 });
put(join(out, 'status.json'), { complete: true, counts, completed: results, frontier,
  derivedInputSha256: sha(readFileSync(inputFile)), noRecursiveAssembly: true, noLowering: true });
console.log('PASS five derived module inputs, seven captured entries, deterministic repeats and negative provenance controls');
