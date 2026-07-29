import assert from "../../../scripts/wasm_assert.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteHost } from "./concrete-host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

const HELPERS = [
  ["fir_ext_panicCore", [0, 0, 0]],
  ["fir_ext_instInhabitedOfMonad__redArg", [0, 0]],
];

function expectTrap(action, label) {
  let trapped = false;
  try {
    action();
  } catch (error) {
    assert.ok(error instanceof WebAssembly.RuntimeError,
      `${label}: expected WebAssembly.RuntimeError, got ${error}`);
    trapped = true;
  }
  assert.ok(trapped, `${label}: fail-closed helper returned`);
}

export async function checkResidentFallbacks({ bytes, manifest }) {
  const module = new WebAssembly.Module(bytes);
  assert.equal(WebAssembly.Module.imports(module).length, 0,
    "closed fallback artifact retained a Wasm import");
  assert.equal(manifest.imports.length, 0,
    "closed fallback descriptor retained an import");

  const host = new ConcreteHost(
    manifest.imports,
    undefined,
    concreteArtifactExternalRegistry,
    manifest.closureDispatch,
    manifest.closureDescriptors,
  );
  const { instance } = await instantiateModuleArtifact({
    bytes,
    manifest,
    host,
  });
  for (const [name, args] of HELPERS) {
    const helper = instance.exports[name];
    assert.equal(typeof helper, "function",
      `missing resident fallback export ${name}`);
    expectTrap(() => helper(...args), name);
  }
  return "PASS zero-import Wasm-resident fail-closed prettyM fallbacks";
}

export async function checkFetchedResidentFallbacks(artifactUrl) {
  const [moduleResponse, descriptorResponse] = await Promise.all([
    fetch(artifactUrl),
    fetch(`${artifactUrl}.json`),
  ]);
  assert.ok(moduleResponse.ok,
    `failed to fetch resident fallbacks: HTTP ${moduleResponse.status}`);
  assert.ok(descriptorResponse.ok,
    `failed to fetch resident fallback descriptor: HTTP ${descriptorResponse.status}`);
  return checkResidentFallbacks({
    bytes: await moduleResponse.arrayBuffer(),
    manifest: await descriptorResponse.json(),
  });
}
