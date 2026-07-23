import assert from "../../../scripts/wasm_assert.mjs";

import {
  ConcreteFault,
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";
import {
  CONCRETE_FIXTURES,
  CONCRETE_SOURCE_PROBES,
  DEFAULT_EXTERNAL_FAULTS,
  EXPECTED_CONCRETE_FAULTS,
  REJECTED_FRAGMENT_FIXTURES,
} from "./concrete-corpus.mjs";
import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import {
  checkConcreteSourceInventory,
} from "./check-concrete-source-probes.mjs";

const corpusPath = new URLSearchParams(globalThis.location.search)
  .get("corpus") ?? "_build/concrete-corpus";
assert.ok(/^_build\/[A-Za-z0-9._/-]+$/.test(corpusPath) &&
  !corpusPath.split("/").includes(".."),
"browser concrete corpus path must be repository-local artifact _build data");
const corpusBase = new URL(`./${corpusPath}/`, import.meta.url);

async function fetchBytes(name, context, base = corpusBase) {
  const response = await fetch(new URL(name, base));
  assert.ok(response.ok, `${context} fetch failed with HTTP ${response.status}`);
  return new Uint8Array(await response.arrayBuffer());
}

async function fetchJson(name, context, base = corpusBase) {
  const response = await fetch(new URL(name, base));
  assert.ok(response.ok, `${context} fetch failed with HTTP ${response.status}`);
  return response.json();
}

async function runConcreteArtifact(fixture) {
  const manifest = await fetchJson(`${fixture}.wasm.json`, `${fixture} manifest`);
  const expected = await fetchJson(`${fixture}.expected.json`, `${fixture} oracle`);
  const bytes = await fetchBytes(`${fixture}.wasm`, `${fixture} module`);
  assert.ok(WebAssembly.validate(bytes), `${fixture}.wasm failed WebAssembly validation`);

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime,
    concreteArtifactExternalRegistry);
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const entry = instance.exports[manifest.entry];
  assert.equal(typeof entry, "function", `missing exported entry ${manifest.entry}`);
  assert.equal(manifest.params.length, manifest.arguments.length,
    `${fixture} manifest argument arity mismatch`);
  const physicalArgs = manifest.params.map((kind, index) =>
    host.encode(kind, concreteManifestValue(manifest.arguments[index])));
  let actual;
  try {
    actual = host.observation(manifest.result, entry(...physicalArgs));
  } catch (error) {
    if (!(error instanceof ConcreteFault)) throw error;
    actual = host.faultObservation(error.fault);
  }
  assert.deepStrictEqual(actual, expected, `${fixture} concrete observation mismatch`);
}

async function checkFragmentGate(fixture) {
  const manifest = await fetchJson(`${fixture}.wasm.json`, `${fixture} manifest`);
  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime,
    concreteArtifactExternalRegistry);
  let rejected = false;
  try {
    host.imports(manifest.imports);
  } catch (error) {
    rejected = /unsupported concrete artifact operation/.test(String(error));
  }
  assert.ok(rejected, `${fixture} unexpectedly crossed its concrete fragment gate`);
}

async function checkExpectedFault(fixture, expectedFault) {
  const manifest = await fetchJson(`${fixture}.wasm.json`, `${fixture} manifest`);
  const bytes = await fetchBytes(`${fixture}.wasm`, `${fixture} module`);
  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime,
    concreteArtifactExternalRegistry);
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  let actual;
  try {
    instance.exports[manifest.entry]();
    actual = undefined;
  } catch (error) {
    if (!(error instanceof ConcreteFault)) throw error;
    actual = error.fault;
  }
  assert.deepStrictEqual(actual, expectedFault,
    `${fixture} did not retain its exact concrete expected failure`);
}

async function checkDefaultExternalFault(fixture, expectedFault) {
  const manifest = await fetchJson(`${fixture}.wasm.json`, `${fixture} manifest`);
  const bytes = await fetchBytes(`${fixture}.wasm`, `${fixture} module`);
  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime);
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  let actual;
  try {
    instance.exports[manifest.entry]();
    actual = undefined;
  } catch (error) {
    if (!(error instanceof ConcreteFault)) throw error;
    actual = error.fault;
  }
  assert.deepStrictEqual(actual, expectedFault,
    `${fixture} did not reject its missing concrete external implementation`);
}

async function runConcreteSourceInventory() {
  const sourceBase = new URL("./_build/", import.meta.url);
  return checkConcreteSourceInventory(async (id) => ({
    manifest: await fetchJson(`${id}.wasm.json`, `${id} manifest`, sourceBase),
    bytes: await fetchBytes(`${id}.wasm`, `${id} module`, sourceBase),
  }));
}

async function runConcreteBrowserCorpus() {
  for (const fixture of CONCRETE_FIXTURES) {
    await runConcreteArtifact(fixture);
  }
  for (const fixture of REJECTED_FRAGMENT_FIXTURES) {
    await checkFragmentGate(fixture);
  }
  for (const [fixture, expectedFault] of DEFAULT_EXTERNAL_FAULTS) {
    await checkDefaultExternalFault(fixture, expectedFault);
  }
  for (const [fixture, expectedFault] of EXPECTED_CONCRETE_FAULTS) {
    await checkExpectedFault(fixture, expectedFault);
  }
  const sourceInventory = await runConcreteSourceInventory();
  assert.equal(sourceInventory.results.length, CONCRETE_SOURCE_PROBES.length);
  const fragmentCount = REJECTED_FRAGMENT_FIXTURES.length;
  return `PASS browser Worker concrete Wasm corpus ` +
    `(${CONCRETE_FIXTURES.length} artifacts, ` +
    `${fragmentCount} fragment gate${fragmentCount === 1 ? "" : "s"}, ` +
    `${DEFAULT_EXTERNAL_FAULTS.length} default external fault, ` +
    `${EXPECTED_CONCRETE_FAULTS.length} expected failure, ` +
    `${sourceInventory.results.length} compiler source probes)`;
}

try {
  globalThis.postMessage({ ok: true, result: await runConcreteBrowserCorpus() });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
