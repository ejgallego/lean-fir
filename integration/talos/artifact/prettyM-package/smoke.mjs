import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import fs from "node:fs";

import {
  checkConcretePrettyFormatTraceModule,
} from "./runtime/integration/talos/artifact/check-concrete-pretty-format-trace-module.mjs";
import {
  ConcreteHost,
} from "./runtime/integration/talos/artifact/concrete-host.mjs";
import {
  instantiateModuleArtifact,
} from "./runtime/integration/talos/artifact/module-client.mjs";
import {
  checkPrettyMBrowserAdapter,
} from "./check-prettyM-browser-adapter.mjs";

const bytes = fs.readFileSync(new URL("./prettyM.wasm", import.meta.url));
const manifest = JSON.parse(
  fs.readFileSync(new URL("./prettyM.wasm.json", import.meta.url), "utf8"));
const build = JSON.parse(
  fs.readFileSync(new URL("./BUILD.json", import.meta.url), "utf8"));
const functionSidecarBytes = fs.readFileSync(
  new URL("./prettyM.wasm.functions.json", import.meta.url));
const functionSidecar = JSON.parse(functionSidecarBytes);
const module = new WebAssembly.Module(bytes);
const imports = WebAssembly.Module.imports(module);

assert.equal(
  imports.length,
  manifest.imports.length,
  "binary/descriptor import count mismatch",
);
const functionImportCount =
  imports.filter((entry) => entry.kind === "function").length;
assert.equal(imports.length, 0);
assert.equal(functionImportCount, 0);
assert.equal(build.compatibility.status, "experimental-unversioned");
assert.equal(build.compatibility.abiVersion, null);
assert.equal(build.capabilities.memoryOwner, "module");
assert.equal(build.capabilities.functionImportCount, functionImportCount);
assert.equal(
  build.capabilities.browserAdapter.apiVersion,
  "fir.prettyM.browser/v1",
);
assert.equal(
  build.capabilities.inputLayout.version,
  "lean-4.33-Std.Format.compact/v1",
);
assert.equal(
  build.capabilities.ownership.version,
  "fir.prettyM.module-owned-transfer/v1",
);
assert.equal(
  build.capabilities.ownership.allocator,
  "single-bulk-resident-allocation-per-render",
);
assert.equal(build.functionImports, functionImportCount);
assert.equal(build.memoryImports, 0);
assert.equal(build.memoryExports, 1);
assert.equal(functionSidecar.schemaVersion, "fir.wasm.function-index/v1");
assert.equal(functionSidecar.artifact.byteLength, bytes.length);
assert.equal(functionSidecar.artifact.sha256,
  createHash("sha256").update(bytes).digest("hex"));
assert.equal(build.functionIndex.schemaVersion, functionSidecar.schemaVersion);
assert.equal(build.functionIndex.bytes, functionSidecarBytes.length);
assert.equal(build.functionIndex.sha256,
  createHash("sha256").update(functionSidecarBytes).digest("hex"));
assert.equal(build.functionIndex.artifactSha256,
  functionSidecar.artifact.sha256);
assert.equal(build.functionIndex.identityBoundary,
  "exact-emitter-final-order/v1");
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

console.log(await checkPrettyMBrowserAdapter({ bytes, manifest, build }));
const host = new ConcreteHost(
  manifest.imports,
  undefined,
  {},
  manifest.closureDispatch,
  manifest.closureDescriptors,
);
const artifact = await instantiateModuleArtifact({ bytes, manifest, host });
console.log(checkConcretePrettyFormatTraceModule(artifact));
