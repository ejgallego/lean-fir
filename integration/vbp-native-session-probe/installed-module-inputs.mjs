// Bounded, pinned-bootstrap-derived capture inputs. These are NOT recovered
// release setup metadata, and this provider never writes Lake setup JSON.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, readFileSync, realpathSync } from 'node:fs';
import { join, resolve } from 'node:path';

export const revision = '6a10ac8c22beadecabdbb0919c2b50214762f91d';
export const toolchain = 'leanprover/lean4:v4.34.0-rc2';
export const owners = new Map([
  ['Init.Data.Repr', ['Nat.reprFast']],
  ['Init.Data.Array.Basic', ['Array.append._redArg']],
  ['Init.Prelude', ['Lean.Name.mkStr3', 'Lean.Name.mkStr4']],
  ['Init.Data.ToString.Name', ['Lean.Name.toString', 'Lean.Name.toStringWithToken._at_.Lean.Name.toString.spec_0']],
  ['Lean.DocString.Types', ['Lean.Doc.instBEqMathMode.beq']],
]);
export const sha = bytes => createHash('sha256').update(bytes).digest('hex');
const run = (cmd, args) => execFileSync(cmd, args, { encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 }).trim();
export function unique(xs, label) {
  assert.equal(xs.length, 1, `${label}: missing or ambiguous input`);
  return xs[0];
}

export function deriveInputs(frontier, repo = process.env.LEAN_SOURCE_REPO ?? '/home/egallego/lean/lean4', selectedOwners = owners) {
  assert.equal(run('elan', ['run', toolchain, 'lean', '--githash']), revision, 'Lean revision mismatch');
  assert.equal(process.platform, 'linux', 'only the reviewed Linux bootstrap derivation is supported');
  const prefix = realpathSync(run('elan', ['run', toolchain, 'lean', '--print-prefix']));
  const git = path => execFileSync('git', ['-C', repo, 'show', `${revision}:${path}`]);
  const templates = ['src/lakefile.toml.in', 'src/CMakeLists.txt'].map(path => {
    const bytes = git(path);
    return { path, sha256: sha(bytes), text: bytes.toString('utf8') };
  });
  const template = templates[0].text, cmake = templates[1].text;
  unique([...template.matchAll(/^bootstrap = true$/gm)], 'bootstrap package identity');
  unique([...template.matchAll(/^moreLeanArgs = \[\$\{LEAN_EXTRA_OPTS_TOML\}\]$/gm)], 'stage argument source');
  unique([...cmake.matchAll(/^set\(LEAN_EXTRA_OPTS "" CACHE STRING .*\)$/gm)], 'initial stage arguments');
  const args = [...cmake.matchAll(/^string\(APPEND LEAN_EXTRA_OPTS " (-D[^"\n]+)"\)$/gm)].map(m => m[1]);
  assert.deepEqual(args, ['-Dinterpreter.prefer_native=false', '-Dpp.rawOnError=true']);
  const option = unique([...template.matchAll(/^leanOptions\.(\S+) = (true|false)$/gm)], 'bootstrap Lean option');
  const options = Object.fromEntries(args.map(arg => {
    const [key, value] = arg.slice(2).split('=');
    return [key, value === 'true'];
  }));
  options[option[1]] = option[2] === 'true';
  assert.deepEqual(options, { 'interpreter.prefer_native': false, 'pp.rawOnError': true, 'linter.coreInternal': true });
  const modules = [...selectedOwners].map(([name, entries]) => {
    const relative = name.replaceAll('.', '/');
    const source = realpathSync(join(prefix, 'src/lean', relative + '.lean'));
    for (const entry of entries) {
      const row = unique(frontier.filter(row => row.name === entry), entry);
      assert.equal(row.module, name, `${entry}: owner mismatch`);
      assert.equal(realpathSync(unique(row.sources, entry + ' source').path), source, 'ambiguous/source-path mismatch');
    }
    const bytes = readFileSync(source);
    assert.deepEqual(bytes, git(`src/${relative}.lean`), `${name}: installed source differs from pinned revision`);
    const artifacts = ['olean', 'olean.server', 'olean.private', 'ir.sig', 'ir', 'ilean'].map(extension => {
      const path = realpathSync(join(prefix, 'lib/lean', relative + '.' + extension));
      return { extension, path, sha256: sha(readFileSync(path)) };
    });
    const ilean = JSON.parse(readFileSync(artifacts.find(a => a.extension === 'ilean').path, 'utf8'));
    assert.equal(ilean.module, name, 'artifact module identity mismatch');
    return { name, entries, source, sourceSha256: sha(bytes), artifacts, directImports: ilean.directImports,
      imports: ilean.directImports.map(([module, isPrivate, importAll, isMeta]) =>
        ({ module, isExported: !isPrivate, importAll, isMeta })) };
  });
  // Inventory the installed import DAG, without compiling any dependency.
  // Hash all parts that ordinary import resolution may consume, not just the
  // selected owner's artifact. Lean checks these paths against its search path.
  const dependencies = new Map();
  const visit = name => {
    if (dependencies.has(name)) return;
    const relative = name.replaceAll('.', '/');
    const artifacts = ['olean', 'olean.server', 'olean.private', 'ir.sig', 'ir', 'ilean'].map(extension => {
      const path = realpathSync(join(prefix, 'lib/lean', relative + '.' + extension));
      return { extension, path, sha256: sha(readFileSync(path)) };
    });
    const ilean = JSON.parse(readFileSync(artifacts.find(a => a.extension === 'ilean').path, 'utf8'));
    assert.equal(ilean.module, name, 'dependency module identity mismatch');
    dependencies.set(name, { name, artifacts });
    for (const [module] of ilean.directImports) visit(module);
  };
  for (const m of modules) for (const [name] of m.directImports) visit(name);
  return {
    kind: 'pinned-bootstrap-derived-capture-inputs/v1', recoveredReleaseSetup: false,
    revision, toolchain, prefix, options, package: null,
    configuration: { platform: 'Linux', initialExtraLeanOpts: '', additionalOverrides: [],
      captureOverrides: { 'compiler.postponeCompile': false, 'Elab.async': false },
      importer: 'unchanged ModuleSource.compile; original source imports and installed search path' },
    upstream: templates.map(({ text, ...row }) => row), modules,
    dependencies: [...dependencies.values()].sort((a, b) => a.name.localeCompare(b.name, 'en')),
  };
}

// Recheck immediately before every frontend invocation, including repeats.
export function validateInputs(inputs, selectedOwners = owners) {
  assert.equal(inputs.kind, 'pinned-bootstrap-derived-capture-inputs/v1');
  assert.equal(inputs.recoveredReleaseSetup, false);
  assert.equal(inputs.revision, revision, 'stale revision');
  assert.equal(inputs.modules.length, selectedOwners.size);
  assert.equal(new Set(inputs.modules.map(m => m.name)).size, selectedOwners.size, 'ambiguous module');
  assert.deepEqual(inputs.options, { 'interpreter.prefer_native': false, 'pp.rawOnError': true, 'linter.coreInternal': true });
  for (const m of inputs.modules) {
    assert.deepEqual(m.entries, selectedOwners.get(m.name), 'wrong module/entry mapping');
    assert.ok(existsSync(m.source), 'missing source');
    assert.equal(sha(readFileSync(m.source)), m.sourceSha256, 'stale source');
    assert.equal(realpathSync(m.source), resolve(inputs.prefix, 'src/lean', m.name.replaceAll('.', '/') + '.lean'));
    assert.equal(m.artifacts.length, 6);
    assert.equal(new Set(m.artifacts.map(a => a.extension)).size, 6, 'ambiguous artifact');
    for (const a of m.artifacts) {
      assert.equal(realpathSync(a.path), resolve(inputs.prefix, 'lib/lean', m.name.replaceAll('.', '/') + '.' + a.extension));
      assert.equal(sha(readFileSync(a.path)), a.sha256, 'stale artifact');
    }
  }
  assert.equal(new Set(inputs.dependencies.map(d => d.name)).size, inputs.dependencies.length, 'ambiguous dependency');
  for (const d of inputs.dependencies) for (const a of d.artifacts) {
    assert.equal(realpathSync(a.path), resolve(inputs.prefix, 'lib/lean', d.name.replaceAll('.', '/') + '.' + a.extension));
    assert.equal(sha(readFileSync(a.path)), a.sha256, 'stale dependency artifact');
  }
}
