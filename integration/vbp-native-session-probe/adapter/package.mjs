import assert from 'node:assert/strict';
import { copyFileSync, readFileSync, writeFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { publishImmutablePackage, sha256, verifyChecksumManifest }
  from '../../package-tools/immutable-package.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, '../../..');
const contract = JSON.parse(readFileSync(join(here, 'inputs.json')));
const read = (dir, name) => readFileSync(join(dir, name));
const digest = (dir, name) => sha256(read(dir, name));
const sourceNames = ['host-prototype.mjs', 'smoke.mjs', 'verify.mjs', 'package.mjs',
  'inputs.json', 'package.json', 'package-lock.json', 'check.mjs', 'README.md'];

export function verifyBaseline(baseline) {
  assert.equal(digest(baseline, 'SHA256SUMS'), contract.baselineSumsSHA256,
    'wrong frozen baseline checksum inventory');
  const rows = read(baseline, 'SHA256SUMS').toString().trim().split('\n').map(line => {
    const match = /^([0-9a-f]{64})  ([^/\\]+)$/.exec(line);
    assert.ok(match, 'malformed frozen checksum row');
    return [match[2], match[1]];
  });
  verifyChecksumManifest(baseline, rows.map(([name]) => name));
  assert.equal(digest(baseline, 'BUILD.json'), contract.baselineBuildSHA256);
  assert.equal(digest(baseline, 'component.wasm'), contract.wasmSHA256);
  return Object.fromEntries(rows);
}

export function produce({ baseline, packagesDirectory }) {
  const rows = verifyBaseline(baseline);
  assert.equal(digest(here, 'host-prototype.mjs'), contract.acceptedHostSHA256);
  assert.equal(digest(here, 'smoke.mjs'), contract.acceptedSmokeSHA256);
  const original = JSON.parse(read(baseline, 'BUILD.json'));
  const git = (...args) => execFileSync('git', ['-C', root, ...args], { encoding: 'utf8' }).trim();
  const sourceFiles = Object.fromEntries(sourceNames.map(name => [name, digest(here, name)]));
  const replaced = new Set(['BUILD.json', 'README.md', 'host-prototype.mjs', 'smoke.mjs']);
  const unchanged = Object.fromEntries(Object.entries(rows).filter(([name]) => !replaced.has(name)));
  const identity = {
    ...original, packageId: undefined,
    producer: {
      schema: 'fir.frozen-utf8-adapter-producer/v1',
      commit: git('rev-parse', 'HEAD'), dirty: git('status', '--porcelain') !== '',
      toolchain: read(root, 'lean-toolchain').toString().trim(), sourceFiles,
      boundary: 'adapter-only packaging; original fir/lean/frozenInputs describe unchanged compiled Wasm',
    },
    baselinePackage: { id: contract.baselinePackage, buildSha256: contract.baselineBuildSHA256,
      sumsSha256: contract.baselineSumsSHA256, wasmSha256: contract.wasmSHA256 },
    adapterCandidate: {
      version: 'fir.adapter.utf8-depth-scratch/v1',
      acceptedPackage: contract.acceptedPackage,
      encoder: 'TextEncoder.encodeInto',
      ownership: 'JavaScript-owned per-session depth-indexed scratch leased through allocation',
      growth: 'Wasm destination/header/view acquired after fir_heap_alloc returns',
      failure: 'finally restores depth; existing fail-closed conversion behavior retained',
      disposal: 'scratch cleared with retained session resources',
      abiChanged: false, runtimeChanged: false, wasmChanged: false,
      hostPrototypeSha256: contract.acceptedHostSHA256, smokeSha256: contract.acceptedSmokeSHA256,
    },
    baselineUnchanged: unchanged,
    acceptance: 'accepted adapter behavior promoted to tracked producer; client owns browser qualification',
  };
  const readme = read(baseline, 'README.md').toString() +
    '\n## Tracked UTF-8 adapter producer\n\nThis local package preserves the frozen Wasm and typed ABI. Only the accepted depth-indexed UTF-8 host adapter, focused controls and package metadata are replaced. BUILD.producer identifies packaging sources separately from the original compiled-Wasm provenance. Not a public FIR runtime API; no live pin or publication is implied.\n';
  const packageId = sha256(Buffer.from(JSON.stringify(identity) + readme)).slice(0, 24);
  identity.packageId = packageId;
  const generated = {
    'BUILD.json': JSON.stringify(identity, null, 2) + '\n', 'README.md': readme,
    'host-prototype.mjs': read(here, 'host-prototype.mjs'),
    'smoke.mjs': read(here, 'smoke.mjs'), 'verify.mjs': read(here, 'verify.mjs'),
  };
  const outputNames = [...new Set([...Object.keys(rows), ...Object.keys(generated)])].sort();
  const result = publishImmutablePackage({ packagesDirectory, packageId, outputNames,
    populate(dir) {
      for (const name of outputNames) {
        if (Object.hasOwn(generated, name)) writeFileSync(join(dir, name), generated[name]);
        else copyFileSync(join(baseline, name), join(dir, name));
      }
    },
    validate(dir) {
      for (const [name, expected] of Object.entries(unchanged)) assert.equal(digest(dir, name), expected);
      assert.equal(digest(dir, 'component.wasm'), contract.wasmSHA256);
      execFileSync(process.execPath, [join(dir, 'verify.mjs')], { stdio: 'pipe' });
    },
  });
  return { ...result, packageId, wasmSHA256: contract.wasmSHA256 };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  assert.equal(process.argv.length, 4, 'usage: node package.mjs FROZEN_BASELINE OUTPUT_PACKAGES');
  console.log(JSON.stringify(produce({ baseline: resolve(process.argv[2]), packagesDirectory: resolve(process.argv[3]) })));
}
