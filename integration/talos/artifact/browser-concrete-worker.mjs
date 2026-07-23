import assert from "../../../scripts/wasm_assert.mjs";

import {
  ConcreteFault,
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";
import {
  CONCRETE_FIXTURES,
  DEFAULT_EXTERNAL_FAULTS,
  EXPECTED_CONCRETE_FAULTS,
  REJECTED_FRAGMENT_FIXTURES,
} from "./concrete-corpus.mjs";
import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import {
  checkConcretePrettyFormatInvocation,
} from "./check-concrete-pretty-format-invocation.mjs";
import { checkConcretePrettyFormatModule } from "./check-concrete-pretty-format-module.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

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

async function runInitialRuntimeSource() {
  const sourceBase = new URL("./_build/", import.meta.url);
  const name = "source-nat-list-case.wasm";
  const manifest = await fetchJson(`${name}.json`, "nat-list source manifest", sourceBase);
  const bytes = await fetchBytes(name, "nat-list source module", sourceBase);
  assert.equal(manifest.fixture, "Fir.Wasm.Emit.SourceFixture.classifyNatList");
  assert.deepStrictEqual(manifest.params, ["tobject"]);
  assert.equal(manifest.result, "uint64");
  assert.ok(WebAssembly.validate(bytes), "nat-list source failed WebAssembly validation");

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime,
    concreteArtifactExternalRegistry);
  for (const cell of manifest.initialRuntime.heap) {
    const address = host.locationAddresses.get(cell.location);
    assert.notEqual(address, undefined, `initial location ${cell.location} was not loaded`);
    const header = host.readHeader(address);
    assert.equal(header.rc, cell.rc, `initial location ${cell.location} rc mismatch`);
    assert.equal(header.persistent, cell.persistent,
      `initial location ${cell.location} persistence mismatch`);
    assert.equal(header.live, cell.live, `initial location ${cell.location} liveness mismatch`);
    assert.deepStrictEqual(host.objectJson(address, header), cell.object,
      `initial location ${cell.location} object mismatch`);
  }
  const semanticArgument = concreteManifestValue(manifest.arguments[0]);
  const physicalArgument = host.encode(manifest.params[0], semanticArgument);
  assert.deepStrictEqual(host.decode(manifest.params[0], physicalArgument), semanticArgument,
    "initial heap argument did not round-trip through its concrete address");
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const result = host.decode(manifest.result,
    instance.exports[manifest.entry](physicalArgument));
  assert.deepStrictEqual(result,
    { kind: "scalar", scalarKind: "uint64", value: 1n });
}

async function runInitialRuntimeStringSource() {
  const sourceBase = new URL("./_build/", import.meta.url);
  const name = "source-string-input.wasm";
  const manifest = await fetchJson("source-string-input.wasm.json",
    "string source manifest", sourceBase);
  const bytes = await fetchBytes(name, "string source module", sourceBase);
  assert.equal(manifest.fixture, "Fir.Wasm.Emit.SourceFixture.acceptString");
  assert.deepStrictEqual(manifest.params, ["object"]);
  assert.equal(manifest.result, "uint64");
  assert.ok(WebAssembly.validate(bytes), "string source failed WebAssembly validation");

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime,
    concreteArtifactExternalRegistry);
  for (const cell of manifest.initialRuntime.heap) {
    const address = host.locationAddresses.get(cell.location);
    assert.notEqual(address, undefined, `initial location ${cell.location} was not loaded`);
    const header = host.readHeader(address);
    assert.equal(header.rc, cell.rc, `initial location ${cell.location} rc mismatch`);
    assert.equal(header.persistent, cell.persistent,
      `initial location ${cell.location} persistence mismatch`);
    assert.equal(header.live, cell.live, `initial location ${cell.location} liveness mismatch`);
    assert.deepStrictEqual(host.objectJson(address, header), cell.object,
      `initial location ${cell.location} object mismatch`);
  }
  const semanticArgument = concreteManifestValue(manifest.arguments[0]);
  const physicalArgument = host.encode(manifest.params[0], semanticArgument);
  assert.deepStrictEqual(host.decode(manifest.params[0], physicalArgument), semanticArgument,
    "initial string argument did not round-trip through its concrete address");
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const result = host.decode(manifest.result,
    instance.exports[manifest.entry](physicalArgument));
  assert.deepStrictEqual(result,
    { kind: "scalar", scalarKind: "uint64", value: 18446744073709551615n });
}

async function runConcretePrettyFormatModule() {
  const sourceBase = new URL("./_build/", import.meta.url);
  const name = "source-pretty-format-module.wasm";
  const manifest = await fetchJson(`${name}.json`, "prettyM module manifest", sourceBase);
  const bytes = await fetchBytes(name, "prettyM module", sourceBase);
  const host = new ConcreteHost(manifest.imports, undefined,
    concreteArtifactExternalRegistry);
  const artifact = await instantiateModuleArtifact({ bytes, manifest, host });
  return checkConcretePrettyFormatModule(artifact);
}

async function runConcretePrettyFormatInvocation() {
  const sourceBase = new URL("./_build/", import.meta.url);
  const name = "source-pretty-format-coverage.wasm";
  const manifest = await fetchJson(`${name}.json`,
    "prettyM coverage invocation manifest", sourceBase);
  const bytes = await fetchBytes(name, "prettyM coverage invocation", sourceBase);
  return checkConcretePrettyFormatInvocation({ bytes, manifest });
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
  await runInitialRuntimeSource();
  await runInitialRuntimeStringSource();
  await runConcretePrettyFormatInvocation();
  await runConcretePrettyFormatModule();
  const fragmentCount = REJECTED_FRAGMENT_FIXTURES.length;
  return `PASS browser Worker concrete Wasm corpus ` +
    `(${CONCRETE_FIXTURES.length} artifacts, ` +
    `${fragmentCount} fragment gate${fragmentCount === 1 ? "" : "s"}, ` +
    `${DEFAULT_EXTERNAL_FAULTS.length} default external fault, ` +
    `${EXPECTED_CONCRETE_FAULTS.length} expected failure, ` +
    `3 initial-runtime sources, 1 raw-layout prettyM module)`;
}

try {
  globalThis.postMessage({ ok: true, result: await runConcreteBrowserCorpus() });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
