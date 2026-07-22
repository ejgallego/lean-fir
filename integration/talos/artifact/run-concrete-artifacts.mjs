import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { basename, dirname, join } from "node:path";
import { pathToFileURL } from "node:url";

import {
  ConcreteFault,
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";
import {
  CONCRETE_FIXTURES,
  EXPECTED_CONCRETE_FAULTS,
  REJECTED_FRAGMENT_FIXTURES,
} from "./concrete-corpus.mjs";

export async function runConcreteArtifact(manifestPath) {
  const manifest = JSON.parse(await readFile(manifestPath, "utf8"));
  const expectedPath = join(dirname(manifestPath), `${manifest.fixture}.expected.json`);
  const expected = JSON.parse(await readFile(expectedPath, "utf8"));
  const wasmPath = manifestPath.slice(0, -".json".length);
  const bytes = await readFile(wasmPath);
  assert.ok(WebAssembly.validate(bytes), `${basename(wasmPath)} failed WebAssembly validation`);

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime);
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const entry = instance.exports[manifest.entry];
  assert.equal(typeof entry, "function", `missing exported entry ${manifest.entry}`);
  assert.equal(manifest.params.length, manifest.arguments.length,
    `${manifest.fixture} manifest argument arity mismatch`);
  const physicalArgs = manifest.params.map((kind, index) =>
    host.encode(kind, concreteManifestValue(manifest.arguments[index])));
  let actual;
  try {
    actual = host.observation(manifest.result, entry(...physicalArgs));
  } catch (error) {
    if (!(error instanceof ConcreteFault)) throw error;
    actual = host.faultObservation(error.fault);
  }
  assert.deepStrictEqual(actual, expected, `${manifest.fixture} concrete observation mismatch`);
  console.log(`PASS concrete ${manifest.fixture}`);
}

export async function runConcreteArtifactDirectory(artifactDirectory) {
  for (const fixture of CONCRETE_FIXTURES) {
    await runConcreteArtifact(join(artifactDirectory, `${fixture}.wasm.json`));
  }
  for (const fixture of REJECTED_FRAGMENT_FIXTURES) {
    const manifest = JSON.parse(await readFile(
      join(artifactDirectory, `${fixture}.wasm.json`), "utf8"));
    const host = new ConcreteHost(manifest.imports, manifest.initialRuntime);
    assert.throws(() => host.imports(manifest.imports),
      /unsupported concrete artifact operation/,
      `${fixture} unexpectedly crossed its concrete fragment gate`);
    console.log(`PASS concrete fragment gate ${fixture}`);
  }
  for (const [fixture, expectedFault] of EXPECTED_CONCRETE_FAULTS) {
    const manifestPath = join(artifactDirectory, `${fixture}.wasm.json`);
    const manifest = JSON.parse(await readFile(manifestPath, "utf8"));
    const bytes = await readFile(manifestPath.slice(0, -".json".length));
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
      `${fixture} did not retain its exact concrete expected failure`);
    console.log(`PASS concrete expected failure ${fixture}`);
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const artifactDirectory = process.argv[2];
  if (!artifactDirectory) {
    console.error("usage: node run-concrete-artifacts.mjs <artifact-directory>");
    process.exit(2);
  }
  await runConcreteArtifactDirectory(artifactDirectory);
}
