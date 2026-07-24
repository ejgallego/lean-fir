import assert from "node:assert/strict";
import fs from "node:fs";

import {
  checkConcretePrettyFormatModule,
} from "./runtime/integration/talos/artifact/check-concrete-pretty-format-module.mjs";
import {
  concreteArtifactExternalRegistry,
} from "./runtime/integration/talos/artifact/concrete-artifact-external-registry.mjs";
import {
  ConcreteHost,
} from "./runtime/integration/talos/artifact/concrete-host.mjs";
import {
  instantiateModuleArtifact,
} from "./runtime/integration/talos/artifact/module-client.mjs";

const bytes = fs.readFileSync(new URL("./prettyM.wasm", import.meta.url));
const manifest = JSON.parse(
  fs.readFileSync(new URL("./prettyM.wasm.json", import.meta.url), "utf8"));
const module = new WebAssembly.Module(bytes);

assert.equal(
  WebAssembly.Module.imports(module).length,
  manifest.imports.length,
  "binary/descriptor import count mismatch",
);
assert.deepStrictEqual(
  WebAssembly.Module.exports(module),
  [{ name: manifest.entry, kind: "function" }],
  "current package must export exactly the raw prettyM entry",
);

const host = new ConcreteHost(
  manifest.imports,
  undefined,
  concreteArtifactExternalRegistry,
  manifest.closureDispatch,
);
const artifact = await instantiateModuleArtifact({ bytes, manifest, host });
console.log(checkConcretePrettyFormatModule(artifact));
