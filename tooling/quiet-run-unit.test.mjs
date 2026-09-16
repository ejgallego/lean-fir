import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync } from 'node:fs';
import { resolve } from 'node:path';
import test from 'node:test';

const root = resolve(import.meta.dirname, '..');
const scratch = resolve(root, '.deps/tooling-tmp');

function run(command, verbose = false) {
  mkdirSync(scratch, { recursive: true });
  const dir = mkdtempSync(resolve(scratch, 'quiet-run-'));
  const result = spawnSync('bash', [resolve(root, 'scripts/quiet-run.sh'),
    'negative-probe', '--', ...command], {
    cwd: root, encoding: 'utf8',
    env: { ...process.env, TMPDIR: dir, FIR_TOOL_LOG_DIR: dir,
      FIR_VERBOSE: verbose ? '1' : '0' },
  });
  return { ...result, dir, cleanup: () => rmSync(dir, { recursive: true, force: true }) };
}

test('quiet success prints one line and removes its log', () => {
  const r = run(['bash', '-c', 'echo child-output; echo child-stderr >&2']);
  try {
    assert.equal(r.status, 0);
    assert.equal(r.stdout, 'PASS negative-probe\n');
    assert.equal(r.stderr, '');
    assert.deepEqual(readdirSync(r.dir), []);
  } finally { r.cleanup(); }
});

for (const status of [1, 2, 7, 127]) {
  test(`direct quiet wrapper preserves child exit ${status} and full failure log`, () => {
    const r = run(['bash', '-c', `echo child-output; echo child-stderr >&2; exit ${status}`]);
    try {
      assert.equal(r.status, status);
      assert.equal(r.stdout, '');
      const files = readdirSync(r.dir);
      assert.equal(files.length, 1);
      assert.match(r.stderr, /FAIL negative-probe \(full log:/);
      assert.match(r.stderr, /child-output\nchild-stderr\n/);
      assert.equal(readFileSync(resolve(r.dir, files[0]), 'utf8'),
        'child-output\nchild-stderr\n');
    } finally { r.cleanup(); }
  });
}

test('failed command lookup returns 127 and retains diagnostics', () => {
  const r = run([resolve(scratch, 'nonexistent-quiet-command')]);
  try {
    assert.equal(r.status, 127);
    assert.match(r.stderr, /FAIL negative-probe/);
    const files = readdirSync(r.dir);
    assert.equal(files.length, 1);
    assert.match(readFileSync(resolve(r.dir, files[0]), 'utf8'), /No such file or directory/);
  } finally { r.cleanup(); }
});

test('quiet failure tails output but keeps the complete log', () => {
  const r = run(['bash', '-c', 'for ((i=1;i<=150;i++)); do echo line-$i; done; exit 7']);
  try {
    assert.equal(r.status, 7);
    assert.doesNotMatch(r.stderr, /\nline-1\n/);
    assert.match(r.stderr, /\nline-31\n/);
    const log = readFileSync(resolve(r.dir, readdirSync(r.dir)[0]), 'utf8');
    assert.equal(log.split('\n').filter(Boolean).length, 150);
    assert.ok(log.startsWith('line-1\n'));
  } finally { r.cleanup(); }
});

for (const status of [0, 7]) {
  test(`verbose passthrough preserves streams and exit ${status} without logs`, () => {
    const r = run(['bash', '-c', `echo child-output; echo child-stderr >&2; exit ${status}`], true);
    try {
      assert.equal(r.status, status);
      assert.equal(r.stdout, 'child-output\n');
      assert.equal(r.stderr, 'child-stderr\n');
      assert.deepEqual(readdirSync(r.dir), []);
    } finally { r.cleanup(); }
  });
}
