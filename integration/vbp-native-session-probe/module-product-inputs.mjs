import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync, realpathSync, mkdirSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { deriveInputs, validateInputs, sha, unique } from './installed-module-inputs.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const state = resolve(here, '../../.deps/native-session-probe');
const out = join(state, 'module-product');
const catalogPath = join(out, 'catalog.json');
const read = path => JSON.parse(readFileSync(path, 'utf8'));
const put = (path, value) => writeFileSync(path, JSON.stringify(value, null, 2) + '\n');

if (process.argv[2] === '--prepare') {
  mkdirSync(out, { recursive: true });
  const setups = {};
  function scan(dir) {
    for (const ent of readdirSync(dir, { withFileTypes: true })) {
      const path = join(dir, ent.name);
      if (ent.isDirectory()) scan(path);
      else if (ent.isFile() && ent.name.endsWith('.setup.json')) {
        const s = read(path);
        if (typeof s.name !== 'string') continue;
        const rows = setups[s.name] ??= [];
        const real = realpathSync(path);
        if (!rows.some(r => r.path === real)) rows.push({ path: real, sha256: sha(readFileSync(real)) });
      }
    }
  }
  scan(join(state, 'sources'));
  scan(join(here, '.lake/build'));
  put(catalogPath, { setups });
} else {
  const requestPath = process.argv[2];
  assert.ok(requestPath, 'expected a provenance request');
  const request = read(requestPath);
  assert.equal(typeof request.module, 'string');
  assert.equal(typeof request.name, 'string');
  const source = realpathSync(unique(request.sources, request.module + ' source'));
  const candidates = read(catalogPath).setups[request.module] ?? [];
  let result;
  if (candidates.length) {
    const selected = unique(candidates, request.module + ' Lake setup');
    assert.equal(sha(readFileSync(selected.path)), selected.sha256, 'stale Lake setup');
    assert.equal(read(selected.path).name, request.module, 'setup owner mismatch');
    result = { route: 'lake', source, sourceSha256: sha(readFileSync(source)), setup: selected.path,
      setupSha256: selected.sha256 };
  } else {
    // The identical pinned-bootstrap derivation/validation policy now selects
    // the actual next worklist owner, not an independently guessed declaration.
    const selectedOwners = new Map([[request.module, [request.name]]]);
    const inputs = deriveInputs([{ ...request, sources: [{ path: source }] }], undefined, selectedOwners);
    validateInputs(inputs, selectedOwners);
    result = { route: 'installed', inputs };
  }
  const provenanceDir = join(dirname(requestPath), 'inputs');
  mkdirSync(provenanceDir, { recursive: true });
  put(join(provenanceDir, request.module + '.json'), { request, result });
  process.stdout.write(JSON.stringify(result));
}
