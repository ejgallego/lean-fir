import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { basename, dirname, join } from "node:path";
import { pathToFileURL } from "node:url";

import {
  SemanticFault,
  SemanticHost,
  manifestValue,
} from "../../../scripts/wasm_semantic_host.mjs";
import { artifactExternalRegistry } from "./artifact-external-registry.mjs";

export async function runArtifact(manifestPath) {
  const manifest = JSON.parse(await readFile(manifestPath, "utf8"));
  const expectedPath = join(dirname(manifestPath), `${manifest.fixture}.expected.json`);
  const expected = JSON.parse(await readFile(expectedPath, "utf8"));
  const wasmPath = manifestPath.slice(0, -".json".length);
  const bytes = await readFile(wasmPath);
  assert.ok(WebAssembly.validate(bytes), `${basename(wasmPath)} failed standard WebAssembly validation`);

  const host = new SemanticHost(manifest.initialRuntime, artifactExternalRegistry);
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const entry = instance.exports[manifest.entry];
  assert.equal(typeof entry, "function", `missing exported entry ${manifest.entry}`);
  assert.ok(Array.isArray(manifest.params), `${manifest.fixture} manifest params must be an array`);
  assert.ok(Array.isArray(manifest.arguments),
    `${manifest.fixture} manifest arguments must be an array`);
  assert.equal(manifest.params.length, manifest.arguments.length,
    `${manifest.fixture} manifest argument arity mismatch`);
  const physicalArgs = manifest.params.map((kind, index) =>
    host.encode(kind, manifestValue(manifest.arguments[index])));
  let actual;
  try {
    const physicalResult = entry(...physicalArgs);
    actual = host.observation(manifest.result, physicalResult);
  } catch (error) {
    if (!(error instanceof SemanticFault)) {
      throw error;
    }
    actual = host.faultObservation(error.fault);
  }
  assert.deepStrictEqual(actual, expected, `${manifest.fixture} observation mismatch`);
  console.log(`PASS ${manifest.fixture}`);
}

export async function runArtifactDirectory(artifactDirectory) {
  const manifests = (await readdir(artifactDirectory))
    .filter((name) => name.endsWith(".wasm.json"))
    .sort();
  assert.ok(manifests.length > 0, `no .wasm.json manifests found in ${artifactDirectory}`);
  for (const manifest of manifests) {
    await runArtifact(join(artifactDirectory, manifest));
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const artifactDirectory = process.argv[2];
  if (!artifactDirectory) {
    console.error("usage: node run-artifacts.mjs <artifact-directory>");
    process.exit(2);
  }
  await runArtifactDirectory(artifactDirectory);
}
