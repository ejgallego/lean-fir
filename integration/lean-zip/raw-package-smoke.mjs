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
  STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES,
  STANDARD_MATH_RUNTIME_VERSION,
} from "./standard-math-runtime-contract.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const wasm = readFileSync(join(directory, "lean-zip-raw.wasm"));
const descriptor = JSON.parse(readFileSync(
  join(directory, "lean-zip-raw.wasm.json"), "utf8"));
const build = JSON.parse(readFileSync(join(directory, "BUILD.json"), "utf8"));
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

for (const line of readFileSync(join(directory, "SHA256SUMS"), "utf8")
    .trim().split("\n")) {
  const [expected, name] = line.split(/\s{2}/);
  assert.equal(sha256(readFileSync(join(directory, name))), expected, name);
}

assert.equal(build.schemaVersion, "fir.lean-zip.raw.build/v1");
assert.equal(build.capabilities.byteArray.layoutVersion,
  LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION);
assert.equal(build.capabilities.adapter.apiVersion,
  LEAN_ZIP_RAW_ADAPTER_API_VERSION);
assert.equal(build.capabilities.ownership.version,
  LEAN_ZIP_RAW_OWNERSHIP_VERSION);
assert.deepEqual(build.entry.levels, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
assert.equal(build.wasm.functionImportCount, 0);
assert.equal(build.wasm.memoryImportCount, 0);
assert.deepEqual(build.wasm.frontier.imports, [
  { module: "lean.extern", name: "Float.ofNat", kind: "function" },
  { module: "lean.extern", name: "Float.ofScientific", kind: "function" },
  { module: "lean.extern", name: "Float.log2", kind: "function" },
]);
assert.equal(build.capabilities.completeRuntime.externalRuntime.version,
  STANDARD_MATH_RUNTIME_VERSION);
assert.equal(
  build.capabilities.completeRuntime.externalRuntime.reservedMemoryBytes,
  STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES);
assert.equal(build.entry.persistentInitializer,
  LEAN_ZIP_RAW_PERSISTENT_INITIALIZER);
assert.equal(build.capabilities.persistentCaches.idempotent, true);

const adapter = await createLeanZipRawAdapter({ bytes: wasm, descriptor });
assert.equal(adapter.initialization.entry, LEAN_ZIP_RAW_PERSISTENT_INITIALIZER);
assert.equal(adapter.initialization.initialFrontier,
  STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES);
assert.ok(adapter.initialization.frontierGrowth > 0);
const input = Uint8Array.of(0, 1, 127, 128, 254, 255);
for (let level = 1; level <= 10; level += 1) {
  const result = adapter.compressRaw(input, level);
  assert.deepEqual(new Uint8Array(inflateRawSync(result.bytes)), input,
    `level ${level}`);
  assert.equal(result.memory.frontierAfter, result.memory.frontierBefore);
  assert.equal(result.memory.frontierBefore, adapter.initialization.checkpoint);
}

console.log("lean-zip raw levels 1–10 package smoke: PASS");
