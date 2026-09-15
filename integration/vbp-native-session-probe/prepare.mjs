import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdirSync, existsSync, copyFileSync } from 'node:fs';
import { dirname, join, resolve, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const fir = resolve(here, '../..');
const state = join(fir, '.deps/native-session-probe');
const source = join(state, 'sources');
const consumer = process.env.VBP_ROOT ??
  '/home/egallego/lean/verso-blueprint/.worktrees/fir-preview-baseline';
const matched = process.env.VBP_MATCHED_ROOT ??
  '/home/egallego/lean/verso-blueprint/.worktrees/native-preview-vir-refresh';
const vir = process.env.VIR_ROOT ?? '/home/egallego/lean/vir';
const base = 'fdef2c1e44355367d449f26ecd87c0fd55a4319b';
const vbpCommit = 'c4430bfe2c898c0312903ae46c45b410d253ebf4';
const rpcPath = 'src/VersoBlueprintVir/Preview/Rpc.lean';
const rpcHash = 'b11a19b76283fec7137c2ea623b94b178dbae29095ec41a775c2045781d30ea6';
const run = (cmd, args, cwd = here) => execFileSync(cmd, args,
  { cwd, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 }).trim();
const sha = bytes => createHash('sha256').update(bytes).digest('hex');
const json = path => JSON.parse(readFileSync(path, 'utf8'));
const put = (path, value) => writeFileSync(path, JSON.stringify(value, null, 2) + '\n');

assert.equal(run('git', ['rev-parse', 'HEAD'], consumer), vbpCommit);
assert.equal(sha(readFileSync(join(consumer, rpcPath))), rpcHash);
assert.equal(run('git', ['diff', '--name-only', 'HEAD'], consumer), rpcPath,
  'the frozen consumer has an unexpected tracked delta');
assert.equal(readFileSync(join(consumer, 'lean-toolchain'), 'utf8').trim(),
  'leanprover/lean4:v4.34.0-rc2');
run('git', ['merge-base', '--is-ancestor', base, 'HEAD'], fir);
mkdirSync(source, { recursive: true });
mkdirSync(join(state, 'tmp'), { recursive: true });
const identities = [];
function archive(name, repo, commit) {
  const dest = join(source, name);
  const tar = join(state, `${name}-${commit}.tar`);
  if (!existsSync(tar)) run('git', ['archive', '--format=tar', '--output', tar, commit], repo);
  const hash = sha(readFileSync(tar));
  if (!existsSync(dest)) {
    mkdirSync(dest);
    run('tar', ['-xf', tar, '-C', dest]);
  }
  identities.push({ name, commit, archiveSha256: hash });
  return dest;
}
archive('fir', fir, base);
// Narrow reviewed compiler overlay; all consumer/dependency source pins stay fixed.
const compilerOverlayPath = 'Fir/Wasm/Emit/CompilerPrivate.lean';
const compilerOverlaySha256 = '3136b2a037ffa18ca83505f93ed9b08fac67e5f37d8d5a32a5927f9d78c1d916';
const compilerOverlay = readFileSync(join(fir, compilerOverlayPath));
assert.equal(sha(compilerOverlay), compilerOverlaySha256,
  'review the constructor-metadata compiler overlay before changing it');
copyFileSync(join(fir, compilerOverlayPath), join(source, 'fir', compilerOverlayPath));
const sourceOverlayPath = 'Fir/Wasm/Emit/Source.lean';
const sourceOverlaySha256 = '26667687f22cc9092b5194121ac9a8ab27b713bd196107ea2c78711a80e07486';
assert.equal(sha(readFileSync(join(fir, sourceOverlayPath))), sourceOverlaySha256,
  'review the executable-body source-discovery overlay before changing it');
copyFileSync(join(fir, sourceOverlayPath), join(source, 'fir', sourceOverlayPath));
const moduleOverlayPath = 'Fir/Wasm/Emit/ModuleSource.lean';
const moduleOverlaySha256 = '6f4c8e4c6935f6ff26a981e9c348797acdfc1f601c9f4b92c13f9d7591fda99c';
assert.equal(sha(readFileSync(join(fir, moduleOverlayPath))), moduleOverlaySha256,
  'review the ordinary module capture adapter before changing it');
copyFileSync(join(fir, moduleOverlayPath), join(source, 'fir', moduleOverlayPath));
const vbp = archive('vbp', consumer, vbpCommit);
copyFileSync(join(consumer, rpcPath), join(vbp, rpcPath));
const manifest = json(join(consumer, 'lake-manifest.json'));
const packages = [];
for (const pkg of manifest.packages) {
  const name = pkg.name.replaceAll('«', '').replaceAll('»', '');
  let dest;
  if (pkg.type === 'path') {
    assert.equal(name, 'verso-react');
    dest = join(vbp, pkg.dir);
  } else {
    if (name === 'lean_vir') assert.equal(pkg.rev, '9fafe9cfd594213ee39dc8205b08084c31101816');
    if (name === 'verso') assert.equal(pkg.rev, '52c8c9557bcb5cc8c0edc0ee37e74311a3d53ee9');
    const candidates = name === 'lean_vir' ? [vir] :
      [join(consumer, '.lake/packages', name), join(matched, '.lake/packages', name)];
    const repo = candidates.find(path => {
      try {
        execFileSync('git', ['cat-file', '-e', `${pkg.rev}^{commit}`],
          { cwd: path, stdio: 'ignore' });
        return true;
      }
      catch { return false; }
    });
    assert.ok(repo, `missing local source object for ${name}@${pkg.rev}`);
    dest = archive(name, repo, pkg.rev);
  }
  packages.push({ type: 'path', scope: '', name: pkg.name,
    manifestFile: 'lake-manifest.json', inherited: !['verso', 'lean_vir', 'verso-react'].includes(name),
    dir: relative(here, dest), configFile: pkg.configFile });
}
packages.push({ type: 'path', scope: '', name: 'Fir', manifestFile: 'lake-manifest.json',
  inherited: false, dir: relative(here, join(source, 'fir')), configFile: 'lakefile.toml' });
put(join(here, 'lake-manifest.json'), { version: '1.2.0', packagesDir: '.lake/packages',
  packages, name: 'FirVbpNativeSessionProbe', lakeDir: '.lake', fixedToolchain: true });
put(join(state, 'SOURCE.json'), {
  firBase: base, fixtureHead: run('git', ['rev-parse', 'HEAD'], fir),
  compilerOverlay: { path: compilerOverlayPath, sha256: compilerOverlaySha256 },
  sourceOverlay: { path: sourceOverlayPath, sha256: sourceOverlaySha256 },
  moduleOverlay: { path: moduleOverlayPath, sha256: moduleOverlaySha256 },
  fixtureDirty: run('git', ['status', '--porcelain'], fir) !== '',
  leanToolchain: 'leanprover/lean4:v4.34.0-rc2',
  leanVersion: run('elan', ['run', 'leanprover/lean4:v4.34.0-rc2', 'lean', '--version']),
  leanCommit: run('elan', ['run', 'leanprover/lean4:v4.34.0-rc2', 'lean', '--githash']),
  contractBase: 'dc94cd4f0aa716aad5e79a7f77bafa752e9994a9',
  entry: 'VersoBlueprint.Experimental.VirPreview.Renderer.render',
  bindingProfile: 'fir.wasm-host-binding/render-core/v0',
  vbp: { commit: vbpCommit, dirty: true, rpcPath, rpcHash,
    nativeSessionSha256: sha(readFileSync(join(vbp, 'tests/VersoBlueprintVirTests/NativeSession.lean'))),
    rendererSha256: sha(readFileSync(join(vbp, 'src/VersoBlueprintVir/Preview/Renderer.lean'))),
    manifestSha256: sha(readFileSync(join(consumer, 'lake-manifest.json'))) },
  archives: identities,
});
console.log(`Pinned ${identities.length} source archives under ${state}; no consumer build products used.`);
