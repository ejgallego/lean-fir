import assert from "node:assert/strict";
import fs from "node:fs";

import {
  checkConcretePrettyFormatTraceModule,
} from "./runtime/integration/talos/artifact/check-concrete-pretty-format-trace-module.mjs";
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
const build = JSON.parse(
  fs.readFileSync(new URL("./BUILD.json", import.meta.url), "utf8"));
const module = new WebAssembly.Module(bytes);
const imports = WebAssembly.Module.imports(module);

assert.equal(
  imports.length,
  manifest.imports.length,
  "binary/descriptor import count mismatch",
);
const functionImportCount =
  imports.filter((entry) => entry.kind === "function").length;
assert.equal(build.compatibility.status, "experimental-unversioned");
assert.equal(build.compatibility.abiVersion, null);
assert.equal(build.capabilities.memoryOwner, "module");
assert.equal(build.capabilities.functionImportCount, functionImportCount);
assert.equal(build.functionImports, functionImportCount);
assert.equal(build.memoryImports, 0);
assert.equal(build.memoryExports, 1);
assert.deepStrictEqual(build.capabilities.output, {
  semantic: "PrettyTrace",
  physical: manifest.result,
  textProjection: "String",
  styling: "MonadPrettyFormat event stream",
  taggedSegments: true,
});
const exports = WebAssembly.Module.exports(module);
const requiredExports = [
  [manifest.entry, "function"],
  ["memory", "memory"],
  ["fir_heap_frontier", "function"],
  ["fir_heap_set_frontier", "function"],
  ["fir_heap_alloc", "function"],
  ["fir_heap_store8", "function"],
  ["fir_heap_store16", "function"],
  ["fir_heap_store32", "function"],
  ["fir_heap_store64", "function"],
];
for (const name of [
  build.capabilities.frontierProtocol.read,
  build.capabilities.frontierProtocol.advance,
  build.capabilities.frontierProtocol.allocate,
]) {
  assert.ok(requiredExports.some(([required]) => required === name),
    `capability metadata names unknown frontier export ${name}`);
}
for (const [name, kind] of requiredExports) {
  assert.ok(exports.some((entry) => entry.name === name && entry.kind === kind),
    `current package is missing ${kind} export ${name}`);
}

const host = new ConcreteHost(
  manifest.imports,
  undefined,
  concreteArtifactExternalRegistry,
  manifest.closureDispatch,
);
const artifact = await instantiateModuleArtifact({ bytes, manifest, host });
console.log(checkConcretePrettyFormatTraceModule(artifact));
