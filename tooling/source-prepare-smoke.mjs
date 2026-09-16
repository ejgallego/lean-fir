// Explicit installed-toolchain replay; never downloads or changes FIR's pin.
import assert from "node:assert/strict";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { prepareSource, fileIdentity, setupIdentities } from "./source-prepare.mjs";
import { makeToolingTemporaryDirectory } from "./worktree-temp.mjs";

const [toolchainDirectory, leanCommit, frozenWorkspace] = process.argv.slice(2);
assert(toolchainDirectory && leanCommit, "usage: node tooling/source-prepare-smoke.mjs TOOLCHAIN_DIRECTORY LEAN_COMMIT [FROZEN_WORKSPACE]");
const root = makeToolingTemporaryDirectory("source-prepare-smoke-");
const source = join(root, "source");
const dep = join(root, "dep");
for (const path of [source, dep]) mkdirSync(path);
writeFileSync(join(source, "lakefile.toml"), 'name = "prepareFixture"\n[[require]]\nname = "prepareDep"\ngit = "https://unavailable.invalid/prepareDep"\nrev = "never-fetch"\n[[lean_lib]]\nname = "Main"\n');
writeFileSync(join(source, "lake-manifest.json"), JSON.stringify({ version: "1.2.0", name: "prepareFixture", lakeDir: ".lake", packagesDir: ".lake/packages", packages: [{ type: "git", name: "prepareDep", scope: "", url: "https://unavailable.invalid/prepareDep", rev: "a".repeat(40), inputRev: "never-fetch", inherited: false, manifestFile: "lake-manifest.json", configFile: "lakefile.toml", subDir: null }] }));
writeFileSync(join(source, "Main.lean"), "import PrepareDep\ndef selectedEntry := PrepareDep.value + 1\n");
writeFileSync(join(dep, "lakefile.toml"), 'name = "prepareDep"\n[[lean_lib]]\nname = "PrepareDep"\n');
writeFileSync(join(dep, "PrepareDep.lean"), "def PrepareDep.value : Nat := 7\n");
writeFileSync(join(dep, "lake-manifest.json"), JSON.stringify({ version: "1.2.0", name: "prepareDep", lakeDir: ".lake", packagesDir: ".lake/packages", packages: [] }));
const packages = join(root, "paths.json");
writeFileSync(packages, JSON.stringify({ prepareDep: dep }));
const result = prepareSource({ source, packages, toolchainDirectory, leanCommit, modules: ["Main"], entries: ["selectedEntry"] });
assert(result.setups[0].artifacts.length > 0);
console.log(`PASS source-prepare installed Lake supplied-Git-dependency replay ${result.workspace}`);

if (frozenWorkspace) {
  // Read-only replay of accepted setup evidence, not a reuse of build state.
  const gate = JSON.parse(readFileSync(join(frozenWorkspace, "SETUP-GATE.json")));
  assert.equal(gate.sourceIdentitySha256, "2c1ef0f6c7d78636af5f50384aafe6407282d1c4b06bece068d7ec49b1e4475b");
  assert.equal(gate.setupAuthoritySha256, "6bbd2b327cce7ca035f934296cd806a664d6856840c7c80932ff53d087489ce7");
  const sourceIdentityPath = join(frozenWorkspace, "snapshot", "identity.json");
  assert.equal(fileIdentity(sourceIdentityPath).sha256, gate.sourceIdentitySha256);
  const suppliedSource = JSON.parse(readFileSync(sourceIdentityPath));
  for (const expected of suppliedSource.files) {
    assert.equal(expected.kind, "file", "frozen source has unsupported file kind");
    const actual = fileIdentity(join(frozenWorkspace, "snapshot", expected.path));
    assert.equal(actual.sha256, expected.sha256, `frozen source changed: ${expected.path}`);
    assert.equal(actual.byteLength, expected.bytes);
    assert.equal(actual.mode, expected.mode);
  }
  const setupPath = join(frozenWorkspace, "private-setup.stdout");
  assert.equal(fileIdentity(setupPath).sha256, gate.setupSha256);
  const setup = JSON.parse(readFileSync(setupPath));
  const identity = setupIdentities(setup, join(frozenWorkspace, "snapshot", "source"), [frozenWorkspace, toolchainDirectory]);
  assert.equal(Object.keys(setup.importArts).length, gate.importRows);
  assert.equal(identity.plugins.length, gate.plugins.length);
  const consumed = new Map([...identity.artifacts, ...identity.plugins].map((item) => [item.path, item]));
  assert.equal(consumed.size, gate.referencedArtifacts.length);
  for (const expected of gate.referencedArtifacts) {
    const actual = consumed.get(expected.path);
    assert(actual, `missing accepted setup artifact: ${expected.path}`);
    assert.equal(actual.sha256, expected.sha256, `accepted artifact bytes changed: ${expected.path}`);
    assert.equal(actual.byteLength, expected.bytes);
    assert.equal(actual.mode, expected.mode);
  }
  writeFileSync(join(root, "FROZEN-SETUP-REPLAY.json"), `${JSON.stringify({ setup: fileIdentity(setupPath), ...identity }, null, 2)}\n`);
  console.log(`PASS source-prepare frozen setup identity replay ${suppliedSource.files.length} sources, ${identity.artifacts.length} artifacts, ${identity.plugins.length} plugins; evidence ${root}`);
}
