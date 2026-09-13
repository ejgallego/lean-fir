import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
const out = new URL('../../.deps/native-session-probe/output/', import.meta.url);
const wasm = readFileSync(new URL('native-session.wasm', out));
assert.equal(WebAssembly.validate(wasm), true);
const module = new WebAssembly.Module(wasm);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
const linked = JSON.parse(readFileSync(new URL('linked.json', out)));
assert.equal(linked.runtimeOperations, 0);
assert.equal(imports.filter(x => x.kind === 'memory').length, 0);
assert.ok(exports.some(x => x.kind === 'memory' && x.name === 'memory'));
assert.ok(exports.some(x => x.kind === 'function' &&
  x.name === 'VersoBlueprint.Experimental.VirPreview.Renderer.render'));
assert.deepEqual(imports.map(x => x.name).sort(), linked.imports.map(x => x.name).sort());
const result = { wasm: fileURLToPath(new URL('native-session.wasm', out)),
  bytes: wasm.length, sha256: createHash('sha256').update(wasm).digest('hex'),
  validated: true, instantiated: false, browserExecuted: false, imports, exports };
writeFileSync(new URL('validation.json', out), JSON.stringify(result, null, 2) + '\n');
console.log(JSON.stringify(result, null, 2));
// The probe stopped at dependency compilation. Do not turn a future structural
// success into profile acceptance before inspecting the actual VIR frontier.
throw new Error('render-core/v0 frontier classification and conformance are not yet performed');
