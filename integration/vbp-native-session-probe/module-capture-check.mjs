import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';

const root = process.argv[2];
const read = (round, module, file) => readFileSync(join(root, round, module, file), 'utf8');
for (const module of ['verso-doc', 'renderer']) {
  for (const file of ['module-capture.json', 'entry.lcnf']) {
    assert.equal(read('first', module, file), read('repeat', module, file),
      `${module}/${file} must be deterministic`);
  }
  const result = JSON.parse(read('first', module, 'module-capture.json'));
  assert.equal(result.capturePhase, 'final-impure');
  assert.equal(result.targetImported, false);
  assert.equal(result.postponeCompile, false);
  assert.equal(result.asyncElaboration, false);
  assert.equal(result.missingEntryRejected, true);
  assert.equal(result.nonModuleSetupRejected, true);
  assert.equal(result.groups.flat().length, result.declarationCount);
  assert.equal(new Set(result.groups.flat()).size, result.declarationCount);
  assert.ok(result.groups.flat().includes(result.entry));
  for (const edge of result.imports) assert.equal(typeof edge.module, 'string', edge.name);
}
const doc = JSON.parse(read('first', 'verso-doc', 'module-capture.json'));
assert.equal(doc.declarationCount, 621);
assert.equal(doc.groups.length, 317);
assert.equal(doc.entryDeclarations.length - doc.imports.length, 7);
assert.equal(doc.imports.length, 6);
const helper = '_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map._at_.' +
  '_private.Verso.Doc.0.Verso.Doc.ListItem.toJson.spec_0._redArg';
assert.ok(doc.entryDeclarations.includes(helper));
assert.ok(!doc.imports.some(({ name }) => name === helper));
const body = read('first', 'verso-doc', 'entry.lcnf');
assert.ok(body.includes(`:= ${helper} inlineToJson`));
assert.ok(body.includes(`:= ${helper} blockToJson`));
assert.ok(body.includes(`def ${helper} `));
const renderer = JSON.parse(read('first', 'renderer', 'module-capture.json'));
assert.equal(renderer.entry, 'VersoBlueprint.Experimental.VirPreview.Renderer.render');
assert.equal(renderer.declarationCount, 164);
assert.equal(renderer.groups.length, 28);
assert.equal(renderer.entryDeclarations.length - renderer.imports.length, 151);
// This is the reviewed source-signature frontier, not the historical viewer's
// Wasm host-import count. Several of these imports still need Lean compilation.
assert.equal(renderer.imports.length, 41);
assert.ok(renderer.imports.some(({ name }) => name === 'VersoReact.Renderer.render'));
assert.ok(renderer.imports.some(({ name }) => name === 'Lean.Vir.React.Node.text'));
console.log('PASS ordinary-module capture: real shared-helper coherence, renderer entry, fail-closed controls, deterministic final LCNF');
