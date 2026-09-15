import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, readdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const state = resolve(here, '../../.deps/native-session-probe');
const out = join(state, 'assembly');
mkdirSync(out, { recursive: true });
const sha = path => createHash('sha256').update(readFileSync(path)).digest('hex');
const setups = new Map();
function scan(dir) {
  for (const ent of readdirSync(dir, { withFileTypes: true })) {
    const path = join(dir, ent.name);
    if (ent.isDirectory()) scan(path);
    else if (ent.isFile() && ent.name.endsWith('.setup.json')) {
      const setup = JSON.parse(readFileSync(path, 'utf8'));
      if (typeof setup.name !== 'string') continue;
      const row = { path: realpathSync(path), sha256: sha(path), package: setup.package ?? null };
      const rows = setups.get(setup.name) ?? [];
      if (!rows.some(x => x.path === row.path)) rows.push(row);
      setups.set(setup.name, rows);
    }
  }
}
// Inspect actual Lake-produced setups, not old packages or guessed file paths.
scan(join(state, 'sources'));
scan(join(here, '.lake/build'));
function unique(rows, label) {
  if (rows.length !== 1) throw new Error(`${label}: expected one input, found ${rows.length}`);
  return rows[0];
}
assert.throws(() => unique([], 'missing setup'), /found 0/);
assert.throws(() => unique(['a', 'b'], 'ambiguous setup'), /found 2/);
const rootModule = 'VersoBlueprintVir.Preview.Renderer';
const owner = 'VersoReact.Renderer';
const rootSetup = unique(setups.get(rootModule) ?? [], rootModule);
const depSetup = unique(setups.get(owner) ?? [], owner);
const rootSource = join(state, 'sources/vbp/src/VersoBlueprintVir/Preview/Renderer.lean');
for (const round of ['first', 'repeat']) {
  const result = execFileSync('lake', ['--keep-toolchain', '-KpostponeCompile=false',
    'env', 'lean', '--run', 'ModuleAssembly.lean', rootSource, rootSetup.path,
    depSetup.path, join(out, round)], { cwd: here, encoding: 'utf8', stdio: ['ignore', 'pipe', 'inherit'] });
  if (result) process.stdout.write(result);
}
for (const file of ['assembly.json', 'root.lcnf', 'root-groups.lcnf', 'dependency.lcnf', 'assembled.lcnf']) {
  assert.equal(sha(join(out, 'first', file)), sha(join(out, 'repeat', file)), `${file}: nondeterministic`);
}
const result = JSON.parse(readFileSync(join(out, 'first/assembly.json'), 'utf8'));
assert.equal(result.owner, owner);
assert.equal(result.rootGroups.length, 28);
assert.equal(result.rootGroups.flat().length, 164);
assert.equal(result.dependencyGroups.length, 141);
assert.equal(result.dependencyGroups.flat().length, 565);
assert.equal(result.localDeclarations.length, 512);
assert.equal(new Set(result.localDeclarations).size, 512);
assert.equal(result.imports.length, 103);
assert.equal(new Set(result.imports.map(x => x.name)).size, 103);
assert.ok(result.localDeclarations.includes(result.selected));
assert.ok(!result.imports.some(x => x.name === result.selected));
assert.equal(result.rootUnchanged, true);
assert.equal(result.signatureMismatchRejected, true);
assert.equal(result.recursiveCapture, false);
assert.equal(result.lowered, false);
for (const row of result.imports) assert.equal(typeof row.module, 'string', row.name);
assert.equal(result.rootFrontier.length, 41);
const frontier = result.rootFrontier.map(row => {
  const candidates = setups.get(row.module) ?? [];
  let category;
  if (row.virTargets.length > 0) category = 'VIR boundary';
  else if (row.externSymbols.length > 0) category = 'runtime/primitive boundary';
  else if (row.sources.length === 1 && candidates.length === 1) category = 'capture-resolvable owning module';
  else category = 'unavailable/ambiguous input';
  return { ...row, category, sources: row.sources.map(path => ({ path, sha256: sha(path) })), setups: candidates };
});
const counts = {};
for (const row of frontier) counts[row.category] = (counts[row.category] ?? 0) + 1;
assert.deepEqual(counts, {
  'unavailable/ambiguous input': 7,
  'capture-resolvable owning module': 24,
  'runtime/primitive boundary': 6,
  'VIR boundary': 4,
});
const report = {
  scope: 'one owning dependency only; source taxonomy, not host-profile admission',
  rootSetup, dependencySetup: depSetup,
  source: { path: result.source, sha256: sha(result.source) },
  localDeclarations: result.localDeclarations.length, remainingSignatures: result.imports.length,
  hashes: Object.fromEntries(['root.lcnf', 'root-groups.lcnf', 'dependency.lcnf', 'assembled.lcnf']
    .map(file => [file, sha(join(out, 'first', file))])),
  controls: { deterministic: true, missingSetupRejected: true, ambiguousSetupRejected: true,
    signatureMismatchRejected: true, rootUnchanged: true },
  counts, frontier,
};
writeFileSync(join(out, 'feasibility.json'), JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify({ counts, locals: 512, remainingSignatures: 103, controls: report.controls }, null, 2));
console.log('PASS one-module assembly, exact source/setup provenance, unchanged groups, signature sensitivity and deterministic repeats');
