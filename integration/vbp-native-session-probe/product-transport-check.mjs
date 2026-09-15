import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdirSync, realpathSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { sha } from './installed-module-inputs.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const state = resolve(here, '../../.deps/native-session-probe');
assert.ok(process.argv.length === 2 || (process.argv.length === 3 && process.argv[2] === '--assemble'));
const assemble = process.argv[2] === '--assemble';
const out = join(state, assemble ? 'two-module-worker' : 'transport');
mkdirSync(out, { recursive: true });
const rootSource = join(state, 'sources/vbp/src/VersoBlueprintVir/Preview/Renderer.lean');
const rootSetup = join(here, '.lake/build/ir/VersoBlueprintVir/Preview/Renderer.setup.json');
const basicSource = join(state, 'sources/verso/src/verso-manual/VersoManual/Basic.lean');
const basicSetup = join(state, 'sources/verso/.lake/build/ir/VersoManual/Basic.setup.json');
const schema = join(here, 'ProductTransport.lean');
const read = p => JSON.parse(readFileSync(p, 'utf8'));
const file = path => ({ path: realpathSync(path), sha256: sha(readFileSync(path)) });
const inputs = [rootSource, rootSetup, basicSource, basicSetup, schema,
  join(state, 'sources/fir/Fir/Wasm/Emit/ModuleSource.lean')].map(file);
for (const path of [rootSetup, basicSetup]) {
  const setup = read(path);
  assert.deepEqual(setup.dynlibs, []);
  for (const p of setup.plugins) inputs.push({ ...file(p.path), initFn: p.initFn ?? null });
}
const revision = execFileSync('lake', ['--keep-toolchain', 'env', 'lean', '--githash'],
  { cwd: here, encoding: 'utf8' }).trim();
assert.equal(revision, '6a10ac8c22beadecabdbb0919c2b50214762f91d');
const identity = { kind: 'local-compacted-region-feasibility-only', leanRevision: revision,
  type: 'ProductTransport.Product', schemaSha256: file(schema).sha256, allowClosures: false,
  source: read(join(state, 'SOURCE.json')), inputs };
const identityPath = join(out, 'identity.json');
writeFileSync(identityPath, JSON.stringify(identity, null, 2) + '\n');
function verifyIdentity(value) {
  assert.equal(value.leanRevision, revision);
  assert.equal(value.type, identity.type);
  assert.equal(value.schemaSha256, file(schema).sha256);
  assert.equal(value.allowClosures, false);
  assert.deepEqual(value, identity);
  for (const row of value.inputs) assert.equal(file(row.path).sha256, row.sha256, 'input identity changed');
}
function run(args) {
  execFileSync('lake', ['--keep-toolchain', '-KpostponeCompile=false', 'env', 'lean', '--run',
    'ProductTransport.lean', ...args], { cwd: here, stdio: 'inherit' });
}
const products = [];
for (const round of ['first', 'repeat']) {
  verifyIdentity(read(identityPath));
  const path = join(out, round + '.region');
  run(['export', basicSource, basicSetup, identityPath, path]);
  const report = read(path + '.json');
  assert.equal(report.roundTripEqual, true);
  assert.equal(report.allowClosures, false);
  assert.ok(report.manualImages.some(p => p.endsWith('/verso_VersoManual_Ext.so')));
  assert.ok(!report.manualImages.some(p => p.endsWith('/libverso_VersoManual.so')));
  products.push({ ...file(path), bytes: readFileSync(path).length, report });
}
assert.equal(products[0].sha256, products[1].sha256, 'compacted payload nondeterministic');
assert.deepEqual(products[0].report, products[1].report, 'producer inventory differs');
function verifyProducts(rows) {
  assert.equal(rows.length, 2);
  for (let i = 0; i < rows.length; i++) {
    assert.equal(rows[i].path, products[i].path);
    assert.equal(file(rows[i].path).sha256, rows[i].sha256, 'blob integrity failure');
    assert.equal(readFileSync(rows[i].path).length, rows[i].bytes);
  }
}
assert.throws(() => verifyIdentity({ ...identity, leanRevision: 'wrong' }));
assert.throws(() => verifyIdentity({ ...identity, schemaSha256: 'wrong' }));
assert.throws(() => verifyProducts(products.map((p, i) => i ? p : { ...p, sha256: 'wrong' })));
const assembled = [];
for (const round of ['first', 'repeat']) {
  verifyIdentity(read(identityPath));
  verifyProducts(products); // Reject before invoking type-erased CompactedRegion.read.
  const path = join(out, round + '-assembly.json');
  run([assemble ? 'assemble' : 'import', rootSource, rootSetup, identityPath,
    products[0].path, products[1].path, path]);
  const result = read(path);
  assert.equal(result.accepted, true);
  assert.equal(result.structuralEquality, true);
  assert.equal(result.signatureOwnerChecks, true);
  assert.equal(result.negativeControls, true);
  assert.equal(result.worklistResumed, false);
  assert.deepEqual(result.imagesBefore, result.imagesAfter);
  assert.equal(result.imagesAfter.length, 1);
  assert.ok(result.imagesAfter[0].endsWith('/libverso_VersoManual.so'));
  if (assemble) {
    assert.equal(result.rendererUnchanged, true);
    assert.equal(result.rendererBodies, 151);
    assert.equal(result.rendererSignatures.length, 41);
    assert.deepEqual(result.assembly.modules, ['VersoBlueprintVir.Preview.Renderer', 'VersoManual.Basic']);
    assert.equal(result.assembly.complete, false);
    assert.equal(result.assembly.lowered, false);
    const bodies = result.assembly.declarations.filter(d => !d.external);
    assert.equal(bodies.length, 158);
    for (const entry of result.assembly.entries) assert.ok(bodies.some(d => d.name === entry));
    assert.equal(new Set(result.assembly.declarations.map(d => d.name)).size,
      result.assembly.declarations.length);
    const expected = [...new Set([...result.rendererSignatures, ...products[0].report.externals])]
      .filter(n => !bodies.some(d => d.name === n));
    assert.deepEqual(result.assembly.remainingSignatures, expected);
    assert.equal(expected.length, 45);
    result.rootText = file(path + '.root.lcnf').sha256;
    result.productText = file(path + '.product.lcnf').sha256;
    assert.equal(result.rootText, '819fed859b7d21f3988072f7be53969705614de8d047f41b6c8b8bc488704073');
    assert.equal(result.productText, '8753415f035416839614b9596472b0a13dcd5c939a4f9300d7b6908a1446953d');
  }
  assembled.push(result);
}
assert.deepEqual(assembled[0], assembled[1]);
verifyIdentity(read(identityPath));
verifyProducts(products);
writeFileSync(join(out, 'summary.json'), JSON.stringify({ products, assembled,
  integrityNegativeControls: true, trustedLocalOnly: true, durableFormat: false }, null, 2) + '\n');
console.log('PASS exact one-product compacted-region transport; no standalone Ext plugin in assembler');
if (assemble) console.log('PASS deterministic two-module assembly; unchanged renderer; exact remaining signatures');
