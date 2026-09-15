// Trusted-local process boundary around the real owning frontend. No product
// cache: the assembler calls once per owner in one traversal and retains data.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdirSync, realpathSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { sha, revision, validateInputs } from './installed-module-inputs.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const read = p => JSON.parse(readFileSync(p, 'utf8'));
const put = (p, v) => writeFileSync(p, JSON.stringify(v, null, 2) + '\n');
const file = p => ({ path: realpathSync(p), sha256: sha(readFileSync(p)) });
const requestPath = process.argv[2];
const request = read(requestPath);
const resolved = JSON.parse(execFileSync('node', [join(here, 'module-product-inputs.mjs'), requestPath],
  { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 }));
const out = join(dirname(requestPath), 'workers', request.module);
mkdirSync(out, { recursive: true });
const inputs = [file(join(here, 'ModuleProduct.lean'))];
if (resolved.route === 'lake') {
  inputs.push(file(resolved.source), file(resolved.setup));
  assert.equal(inputs[1].sha256, resolved.sourceSha256);
  assert.equal(inputs[2].sha256, resolved.setupSha256);
  const setup = read(resolved.setup);
  assert.equal(setup.name, request.module);
  for (const p of setup.plugins ?? []) inputs.push({ ...file(p.path), initFn: p.initFn ?? null });
  for (const p of setup.dynlibs ?? []) inputs.push(file(p));
} else {
  assert.equal(resolved.route, 'installed');
  validateInputs(resolved.inputs, new Map([[request.module, [request.name]]]));
}
inputs.push(file(join(here, '../../Fir/Wasm/Emit/NativeSymbol.lean')));
function verify() {
  const actual = execFileSync('lake', ['--keep-toolchain', 'env', 'lean', '--githash'],
    { cwd: here, encoding: 'utf8' }).trim();
  assert.equal(actual, revision);
  for (const row of inputs) assert.equal(file(row.path).sha256, row.sha256);
  if (resolved.route === 'installed')
    validateInputs(resolved.inputs, new Map([[request.module, [request.name]]]));
}
const identity = join(out, 'identity.json');
const product = join(out, 'module.region');
const identityData = { kind: 'trusted-local-module-worker', module: request.module,
  revision, schema: 'RendererModuleProduct.WorkerProduct', inputs, resolved };
put(identity, identityData);
verify();
// Capture diagnostics belong to the per-owner log, not the JSON control pipe.
try {
  const stdout = execFileSync('lake', ['--keep-toolchain', '-KpostponeCompile=false', 'env',
    'lean', '--run', 'ModuleProduct.lean', '--worker', identity, product],
  { cwd: here, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 });
  writeFileSync(join(out, 'capture.log'), stdout);
} catch (e) {
  writeFileSync(join(out, 'capture.log'), String(e.stdout ?? '') + String(e.stderr ?? ''));
  throw e;
}
verify();
assert.deepEqual(read(identity), identityData);
const report = read(product + '.json');
assert.equal(report.module, request.module);
assert.ok(!(report.images.some(p => p.endsWith('/libverso_VersoManual.so')) &&
  report.images.some(p => p.endsWith('/verso_VersoManual_Ext.so'))), 'overlapping Manual images');
const digest = file(product).sha256;
const result = { identity, product, sha256: digest, bytes: readFileSync(product).length, report };
put(join(out, 'result.json'), result);
// Complete identity/integrity validation immediately before the parent reads.
assert.equal(file(product).sha256, digest);
process.stdout.write(JSON.stringify(result));
