import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { inflateRawSync } from "node:zlib";

import {
  LEAN_ZIP_LEVEL1_ADAPTER_API_VERSION,
  LEAN_ZIP_LEVEL1_OWNERSHIP_VERSION,
  createLeanZipLevel1Adapter,
} from "./lean-zip-level1-browser-adapter.mjs";
import { LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION } from
  "./lean-zip-byte-array-browser-adapter.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const wasm = readFileSync(join(directory, "lean-zip-level1.wasm"));
const descriptor = JSON.parse(readFileSync(
  join(directory, "lean-zip-level1.wasm.json"), "utf8"));
const build = JSON.parse(readFileSync(join(directory, "BUILD.json"), "utf8"));
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

for (const line of readFileSync(join(directory, "SHA256SUMS"), "utf8")
    .trim().split("\n")) {
  const [expected, name] = line.split(/\s{2}/);
  assert.equal(sha256(readFileSync(join(directory, name))), expected, name);
}

assert.equal(build.schemaVersion, "fir.lean-zip.level1.build/v1");
assert.equal(build.capabilities.byteArray.layoutVersion,
  LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION);
assert.equal(build.capabilities.adapter.apiVersion,
  LEAN_ZIP_LEVEL1_ADAPTER_API_VERSION);
assert.equal(build.capabilities.ownership.version,
  LEAN_ZIP_LEVEL1_OWNERSHIP_VERSION);
assert.equal(build.wasm.functionImportCount, 0);
assert.equal(build.wasm.memoryImportCount, 0);

const adapter = await createLeanZipLevel1Adapter({ bytes: wasm, descriptor });
const input = Uint8Array.of(0, 1, 127, 128, 254, 255);
const result = adapter.compressLevel1(input);
assert.deepEqual(Array.from(result.bytes), [99, 96, 172, 111, 248, 247, 31, 0]);
assert.deepEqual(new Uint8Array(inflateRawSync(result.bytes)), input);
assert.equal(result.memory.frontierAfter, result.memory.frontierBefore);

console.log("lean-zip Level-1 package smoke: PASS");
