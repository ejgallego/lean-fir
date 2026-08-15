import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { inflateRawSync } from "node:zlib";

import {
  LEAN_ZIP_RAW_ADAPTER_API_VERSION,
  LEAN_ZIP_RAW_OWNERSHIP_VERSION,
  LEAN_ZIP_RAW_PERSISTENT_INITIALIZER,
  createLeanZipRawAdapter,
} from "./lean-zip-raw-browser-adapter.mjs";
import { LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION } from
  "./lean-zip-byte-array-browser-adapter.mjs";
import {
  STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES,
  STANDARD_LIBM_RUNTIME_VERSION,
} from "./standard-libm-runtime-contract.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const wasm = readFileSync(join(directory, "lean-zip-raw.wasm"));
const descriptor = JSON.parse(readFileSync(
  join(directory, "lean-zip-raw.wasm.json"), "utf8"));
const functionSidecar = JSON.parse(readFileSync(
  join(directory, "lean-zip-raw.wasm.functions.json"), "utf8"));
const build = JSON.parse(readFileSync(join(directory, "BUILD.json"), "utf8"));
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

for (const line of readFileSync(join(directory, "SHA256SUMS"), "utf8")
    .trim().split("\n")) {
  const [expected, name] = line.split(/\s{2}/);
  assert.equal(sha256(readFileSync(join(directory, name))), expected, name);
}

assert.equal(build.schemaVersion, "fir.lean-zip.raw.build/v3");
assert.equal(build.capabilities.byteArray.layoutVersion,
  LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION);
assert.equal(build.capabilities.adapter.apiVersion,
  LEAN_ZIP_RAW_ADAPTER_API_VERSION);
assert.equal(build.capabilities.ownership.version,
  LEAN_ZIP_RAW_OWNERSHIP_VERSION);
assert.deepEqual(build.entry.levels, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
assert.equal(build.wasm.functionImportCount, 0);
assert.equal(build.wasm.memoryImportCount, 0);
const module = new WebAssembly.Module(wasm);
assert.deepEqual(WebAssembly.Module.imports(module), []);
assert.deepEqual(WebAssembly.Module.exports(module), build.wasm.exports);
assert.equal(functionSidecar.schemaVersion, "fir.wasm.function-index/v1");
assert.deepEqual(functionSidecar.artifact, {
  file: "lean-zip-raw.wasm",
  byteLength: wasm.byteLength,
  sha256: sha256(wasm),
  functionImportCount: 0,
  definedFunctionCount: 2305,
  functionCount: 2305,
});
assert.deepEqual(functionSidecar.functions.map(({ index }) => index),
  Array.from({ length: 2305 }, (_, index) => index));
assert(functionSidecar.functions.every(({ imported }) => imported === false));
const functionExports = functionSidecar.functions.flatMap((function_) =>
  function_.exportedAs.map((name) => ({ name, index: function_.index })));
const functionOrigins = Object.fromEntries([
  "lean-source",
  "optimizer-or-linked-runtime",
  "resident-helper",
].map((origin) => [origin, functionSidecar.functions.filter(
  (function_) => function_.origin === origin).length]));
assert.deepEqual(functionExports, [
  { name: "fir_heap_alloc", index: 17 },
  { name: "fir_heap_frontier", index: 37 },
  { name: "Zip.Wasm.compressRaw", index: 2302 },
  { name: "fir_heap_rewind", index: 2303 },
  { name: "fir_heap_set_frontier", index: 2304 },
]);
assert.deepEqual(build.wasm.functionEvidence, {
  file: "lean-zip-raw.wasm.functions.json",
  schemaVersion: "fir.wasm.function-index/v1",
  byteLength: readFileSync(
    join(directory, "lean-zip-raw.wasm.functions.json")).byteLength,
  sha256: sha256(readFileSync(
    join(directory, "lean-zip-raw.wasm.functions.json"))),
  functionImportCount: 0,
  definedFunctionCount: 2305,
  functionCount: 2305,
  functionsSha256: sha256(JSON.stringify(functionSidecar.functions)),
  origins: functionOrigins,
  exports: functionExports,
  runtimeUse: false,
  releaseBytesIdentical: true,
  protocol: "prepare/restamp/optimize across runtime linking and DCE",
});
assert.deepEqual(functionOrigins, {
  "lean-source": 390,
  "optimizer-or-linked-runtime": 0,
  "resident-helper": 1915,
});
assert.deepEqual(build.wasm.frontier.imports, [
  { module: "lean.extern", name: "Float.log2", kind: "function" },
]);
assert.equal(build.capabilities.completeRuntime.externalRuntime.version,
  STANDARD_LIBM_RUNTIME_VERSION);
assert.equal(
  build.capabilities.completeRuntime.externalRuntime.reservedMemoryBytes,
  STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES);
assert.equal(
  build.capabilities.completeRuntime.externalRuntime.numericContract,
  "platform-libm-special-values-and-bounded-error");
assert.equal(build.entry.persistentInitializer,
  LEAN_ZIP_RAW_PERSISTENT_INITIALIZER);
assert.equal(build.capabilities.persistentCaches.cacheAwareRewind, true);
assert.equal(build.capabilities.persistentCaches.warmCallStable, true);

const adapter = await createLeanZipRawAdapter({ bytes: wasm, descriptor });
assert.equal(adapter.initialization.entry, LEAN_ZIP_RAW_PERSISTENT_INITIALIZER);
assert.equal(adapter.initialization.initialFrontier,
  STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES);
assert.equal(adapter.initialization.frontierGrowth, 0);
const input = Uint8Array.of(0, 1, 127, 128, 254, 255);
let checkpoint = adapter.initialization.checkpoint;
for (let level = 1; level <= 10; level += 1) {
  const result = adapter.compressRaw(input, level);
  assert.deepEqual(new Uint8Array(inflateRawSync(result.bytes)), input,
    `level ${level}`);
  assert.equal(result.memory.frontierBefore, checkpoint);
  assert.ok(result.memory.frontierAfter >= checkpoint);
  checkpoint = result.memory.frontierAfter;
  const warm = adapter.compressRaw(input, level);
  assert.deepEqual(warm.bytes, result.bytes, `warm level ${level}`);
  assert.equal(warm.memory.frontierBefore, checkpoint);
  assert.equal(warm.memory.frontierAfter, checkpoint);
}

console.log("lean-zip raw levels 1–10 package smoke: PASS");
