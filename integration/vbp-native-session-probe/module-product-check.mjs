import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync, mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { sha, unique } from './installed-module-inputs.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const state = resolve(here, '../../.deps/native-session-probe');
const isolated = process.argv.includes('--isolated');
const once = process.argv.includes('--once');
const lower = process.argv.includes('--lower');
// Validation-only mode never claims a new capture or execution. It checks
// products from explicitly run phases, including their current input hashes.
const checkOnly = process.argv.includes('--check-only');
assert.ok(!lower || isolated);
assert.ok(!checkOnly || isolated);
assert.ok(process.argv.slice(2).every(a => ['--isolated', '--once', '--lower', '--check-only'].includes(a)));
const out = join(state, isolated ? 'native-provider-product' : 'module-product');
mkdirSync(out, { recursive: true });
const resolver = join(here, 'module-product-inputs.mjs');
execFileSync('node', [resolver, '--prepare'], { stdio: 'inherit' });
const catalog = JSON.parse(readFileSync(join(state, 'module-product/catalog.json'), 'utf8'));
const rootModule = 'VersoBlueprintVir.Preview.Renderer';
const setup = unique(catalog.setups[rootModule], rootModule);
const source = join(state, 'sources/vbp/src/VersoBlueprintVir/Preview/Renderer.lean');
if (!checkOnly) for (const round of once ? ['first'] : ['first', 'repeat']) {
  execFileSync('lake', ['--keep-toolchain', '-KpostponeCompile=false', 'env', 'lean', '--run',
    'ModuleProduct.lean', ...(isolated ? ['--isolated'] : []), source, setup.path,
    isolated ? join(here, 'module-product-worker.mjs') : resolver, join(out, round)],
  { cwd: here, stdio: 'inherit' });
}
const hashes = {};
for (const file of ['root.lcnf', 'product.lcnf', 'product.json']) {
  const hash = sha(readFileSync(join(out, 'first', file)));
  if (!once) assert.equal(hash, sha(readFileSync(join(out, 'repeat', file))), `${file}: nondeterministic`);
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
if (!isolated) {
assert.equal(result.complete, false);
assert.equal(result.failure, 'compiler diagnostic in VersoManual.Basic');
assert.equal(result.modules.length, 26);
assert.equal(result.selections.length, 74);
assert.equal(result.bodies.length, 1201);
assert.deepEqual(counts, {
  'runtime/primitive boundary': 74, 'VIR boundary': 12, 'source pending': 25,
});
assert.equal(hashes['product.lcnf'], 'fdb34c2cb7a5366c6d60258d17a46e15413416ba91e43a9e38e66a1dd1a7d1f3');
}
if (isolated) {
  assert.equal(result.complete, true, `isolated source closure regressed: ${result.failure}`);
  for (const round of once ? ['first'] : ['first', 'repeat']) {
    const maps = JSON.parse(readFileSync(join(out, round, 'isolation.json')));
    assert.deepEqual(maps.imagesBefore, maps.imagesAfter);
    assert.ok(!maps.imagesAfter.some(p => p.endsWith('/verso_VersoManual_Ext.so')));
    assert.equal(maps.regions + 1, result.modules.length);
    for (const module of result.modules.slice(1)) {
      const identity = JSON.parse(readFileSync(join(out, round, 'workers', module.name, 'identity.json')));
      for (const input of identity.inputs) assert.equal(sha(readFileSync(input.path)), input.sha256,
        `captured input changed: ${input.path}`);
      assert.ok(identity.inputs.some(i => i.path.endsWith('/Fir/Wasm/Emit/NativeSymbol.lean')));
    }
  }
  if (result.complete) {
    assert.equal(result.modules.length, 52);
    assert.equal(result.bodies.length, 1535);
    assert.deepEqual(counts, { 'runtime/primitive boundary': 116, 'VIR boundary': 12 });
    assert.equal(hashes['product.lcnf'], '678c0471328fc0f6a0b11f844b6499b68c7bf06a2ae7df75d7340449342e1376');
    assert.equal(result.nativeLinks.length, 16);
    assert.equal(new Set(result.nativeLinks.map(p => p.declaration)).size, 16);
    for (const p of result.nativeLinks) {
      assert.ok(result.frontier.some(e => e.name === p.declaration && e.externSymbols.includes(p.symbol)));
      assert.ok(result.bodies.some(b => b.name === p.provider && b.owner === p.owner));
    }
    const localNative = result.frontier.find(e => e.name === 'USize.repr');
    assert.equal(localNative?.category, 'runtime/primitive boundary');
    assert.deepEqual(localNative?.externSymbols, ['lean_string_of_usize']);
    const regionHash = sha(readFileSync(join(out, 'first/product.region')));
    if (!once) assert.equal(regionHash, sha(readFileSync(join(out, 'repeat/product.region'))));
    hashes['product.region'] = regionHash;
    if (lower) {
      const reports = [];
      for (const round of once ? ['first'] : ['first', 'repeat']) {
        const dir = join(out, round);
        // Both products were produced by this invocation and checked above.
        assert.equal(sha(readFileSync(join(dir, 'product.region'))), regionHash);
        if (!checkOnly) execFileSync('lake', ['--keep-toolchain', '-KpostponeCompile=false', 'env', 'lean', '--run',
          'LowerModuleProduct.lean', source, setup.path, join(dir, 'product.region'),
          join(dir, 'product.json'), join(dir, 'lower')], { cwd: here, stdio: 'inherit' });
        reports.push(JSON.parse(readFileSync(join(dir, 'lower/result.json'))));
      }
      if (!once) assert.deepEqual(reports[0], reports[1]);
      for (const round of once ? ['first'] : ['first', 'repeat']) {
        const binary = readFileSync(join(out, round, 'lower/renderer-base.wasm'));
        assert.equal(binary.length, 839735);
        assert.equal(sha(binary), 'b154b7169d63c3aa02098b0f5936f0dee4d2fa5cc40a234ffcfaa8d602a0af9b');
        assert.ok(WebAssembly.validate(binary), 'base Wasm must validate independently');
        if (round === 'repeat') assert.deepEqual(binary,
          readFileSync(join(out, 'first/lower/renderer-base.wasm')));
      }
      // This is a precise diagnostic boundary, not acceptance of any failure.
      const linked = reports[0];
      assert.equal(linked.success, false);
      assert.equal(linked.stage, 'resident-link');
      assert.equal(linked.error,
        'Fir.Wasm.Emit.Source.CompileError.manifest "resident linker retained unsupported external String.Internal.atEnd"');
      const frontier = linked.diagnosticFrontier.imports;
      assert.equal(frontier.length, 15);
      assert.ok(frontier.every(i => !i.manifestError));
      assert.deepEqual(frontier.filter(i => i.operation.kind !== 'external'), []);
      assert.equal(frontier.filter(i => i.operation.declaration?.startsWith('Lean.Vir.')).length, 12);
      assert.deepEqual(frontier.filter(i => i.operation.kind === 'external' &&
        !i.operation.declaration.startsWith('Lean.Vir.')).map(i => i.operation.declaration), [
        'String.Internal.atEnd', 'String.Internal.get', 'String.Pos.Raw.atEnd',
      ]);
      const providers = linked.diagnosticFrontier.leanExportProviders;
      assert.deepEqual(providers, []);
      const host = JSON.parse(readFileSync(join(out, 'first/lower/host-boundary.json')));
      assert.equal(host.schema, 'fir.vir-host-boundary-audit/v1');
      assert.equal(host.admitted, false);
      assert.equal(host.executed, false);
      assert.equal(host.imports.length, 12);
      for (const row of host.imports) {
        const source = result.frontier.find(e => e.name === row.declaration);
        assert.deepEqual(source.virTargets, [row.target]);
        assert.equal(row.borrowedParameters.length, row.physicalImport.operation.params.length);
      }
      for (const [name, kind, target] of [
        ['ofBool', 'uint8', 'js.bool'], ['ofFloat', 'float', 'js.float'],
        ['ofString', 'object', 'js.string'],
      ]) {
        const row = host.imports.find(r => r.declaration === `Lean.Vir.JsValue.${name}`);
        assert.equal(row.marker, 'vir_js_explicit_conversion');
        assert.equal(row.target, target);
        assert.deepEqual(row.physicalImport.operation.params, [kind, 'erased']);
      }
      const callback = host.imports.find(r => r.declaration === 'Lean.Vir.React.Callback.ofUnary');
      assert.equal(callback.target, 'js.value.react.callback');
      assert.equal(callback.marker, 'vir_js_explicit_conversion');
      assert.deepEqual(callback.physicalImport.operation.params, ['erased', 'object', 'erased']);
      assert.equal(callback.borrowedParameters[1], false, 'callback is transferred, not borrowed');
      if (!once) assert.deepEqual(host, JSON.parse(readFileSync(join(out, 'repeat/lower/host-boundary.json'))));
      console.log(JSON.stringify(reports[0], null, 2));
    }
  }
}
writeFileSync(join(out, 'summary.json'), JSON.stringify({ complete: result.complete, failure: result.failure,
  modules: result.modules.length, bodies: result.bodies.length, frontier: result.frontier.length,
  selections: result.selections.length, counts, hashes }, null, 2) + '\n');
console.log(JSON.stringify({ complete: result.complete, failure: result.failure, modules: result.modules.length,
  bodies: result.bodies.length, frontier: result.frontier.length, counts }, null, 2));
console.log(checkOnly ? 'PASS validation of existing products (no new capture or execution)' : once ? 'DIAGNOSTIC single worklist attempt' :
  'PASS deterministic fail-closed module-product experiment (not a Wasm acceptance)');
