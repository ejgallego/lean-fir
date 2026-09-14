import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync, mkdirSync, copyFileSync } from 'node:fs';
import { dirname, resolve, join } from 'node:path';
import { fileURLToPath } from 'node:url';

// Caller supplies the same 4.34-scoped cache and TMPDIR as check.sh.
const here = dirname(fileURLToPath(import.meta.url));
const evidence = resolve(here, '../../.deps/native-session-probe/control');
const setupPath = join(here, '.lake/build/ir/VersoBlueprint/Html.setup.json');
const hash = path => createHash('sha256').update(readFileSync(path)).digest('hex');
const sourcePath = resolve(here, '../../.deps/native-session-probe/sources/vbp/src/VersoBlueprint/Html.lean');
const sourceHash = hash(sourcePath);
assert.ok(process.env.LAKE_CACHE_DIR?.endsWith('/leanprover--lean4---v4.34.0-rc2'));
assert.equal(process.env.LAKE_ARTIFACT_CACHE, 'true');
assert.equal(process.env.LAKE_RESTORE_ARTIFACTS, 'true');
assert.equal(process.env.TMPDIR, resolve(here, '../../.deps/native-session-probe/tmp'));
mkdirSync(evidence, { recursive: true });
const rows = [];
for (const mode of [true, false]) {
  const label = mode ? 'postponed-control' : 'ordinary-control';
  const args = ['--keep-toolchain', '--reconfigure', `-KpostponeCompile=${mode}`,
    'build', 'VersoBlueprint.Html'];
  const run = spawnSync('lake', args, { cwd: here, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 });
  if (run.error) throw run.error;
  const log = `${run.stdout ?? ''}${run.stderr ?? ''}`;
  writeFileSync(join(evidence, `${label}.log`), log);
  assert.equal(run.signal, null);
  const setup = JSON.parse(readFileSync(setupPath, 'utf8'));
  assert.equal(setup.name, 'VersoBlueprint.Html');
  assert.equal(setup.options['compiler.postponeCompile'], mode,
    'invocation override did not reach the actual module setup');
  assert.equal(hash(sourcePath), sourceHash, 'control changed the source');
  copyFileSync(setupPath, join(evidence, `${label}.setup.json`));
  const row = { mode, command: ['lake', ...args], exitCode: run.status,
    sourceSha256: sourceHash, options: setup.options, setupSha256: hash(setupPath),
    firstError: log.split('\n').find(line => /Unknown constant|error:/.test(line)) ?? null };
  rows.push(row);
  writeFileSync(join(evidence, 'controls.json'), JSON.stringify(rows, null, 2) + '\n');
  console.log(JSON.stringify(row));
  if (mode) {
    assert.equal(run.status, 1);
    assert.ok(log.includes('Unknown constant `String.Slice.posGE._redArg`'));
  }
}
const [postponed, ordinary] = rows;
const withoutMode = row => {
  const options = { ...row.options };
  delete options['compiler.postponeCompile'];
  return options;
};
assert.deepEqual(withoutMode(postponed), withoutMode(ordinary));
if (ordinary.exitCode !== 0) process.exitCode = 1;
