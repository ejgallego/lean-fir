import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { basename, dirname, join } from "node:path";
import { pathToFileURL } from "node:url";

import {
  ConcreteFault,
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";

const CONCRETE_FIXTURES = [
  "arg-erased",
  "arg-tagged-first",
  "arg-uint16-max",
  "arg-uint32-max",
  "arg-uint64-max",
  "arg-uint8-max",
  "arg-usize-max",
  "case",
  "closure-call",
  "closure-underapply",
  "ctor-projection",
  "default-case",
  "direct-call",
  "erased",
  "literal",
  "natural-heap",
  "projection-fault",
  "recursive-call",
  "uint16-max",
  "uint32-max",
  "uint64-max",
  "uint8-max",
  "usize-max",
];

const REJECTED_FRAGMENT_FIXTURES = [
  "external-echo",
  "mutation",
  "string-heap",
];

export async function runConcreteArtifact(manifestPath) {
  const manifest = JSON.parse(await readFile(manifestPath, "utf8"));
  const expectedPath = join(dirname(manifestPath), `${manifest.fixture}.expected.json`);
  const expected = JSON.parse(await readFile(expectedPath, "utf8"));
  const wasmPath = manifestPath.slice(0, -".json".length);
  const bytes = await readFile(wasmPath);
  assert.ok(WebAssembly.validate(bytes), `${basename(wasmPath)} failed WebAssembly validation`);

  const host = new ConcreteHost(manifest.imports);
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
    const host = new ConcreteHost(manifest.imports);
    assert.throws(() => host.imports(manifest.imports),
      /unsupported concrete artifact operation/,
      `${fixture} unexpectedly crossed its concrete fragment gate`);
    console.log(`PASS concrete fragment gate ${fixture}`);
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
