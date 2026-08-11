import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { inflateRawSync } from "node:zlib";

import {
  LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION,
  LEAN_ZIP_STORED_ADAPTER_API_VERSION,
  LEAN_ZIP_STORED_OWNERSHIP_VERSION,
  createLeanZipStoredAdapter,
} from "./lean-zip-stored-browser-adapter.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const wasm = readFileSync(join(directory, "lean-zip-stored.wasm"));
const descriptor = JSON.parse(readFileSync(
  join(directory, "lean-zip-stored.wasm.json"), "utf8"));
const build = JSON.parse(readFileSync(join(directory, "BUILD.json"), "utf8"));

const sha256 = (value) => createHash("sha256").update(value).digest("hex");

for (const line of readFileSync(join(directory, "SHA256SUMS"), "utf8")
    .trim().split("\n")) {
  const [expected, name] = line.split(/\s{2}/);
  assert.equal(sha256(readFileSync(join(directory, name))), expected, name);
}

assert.equal(build.capabilities.byteArray.layoutVersion,
  LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION);
assert.equal(build.capabilities.adapter.apiVersion,
  LEAN_ZIP_STORED_ADAPTER_API_VERSION);
assert.equal(build.capabilities.ownership.version,
  LEAN_ZIP_STORED_OWNERSHIP_VERSION);

function storedReference(input) {
  const blockCount = Math.max(1, Math.ceil(input.length / 65535));
  const output = new Uint8Array(input.length + 5 * blockCount);
  let source = 0;
  let destination = 0;
  for (let block = 0; block < blockCount; block += 1) {
    const count = Math.min(65535, input.length - source);
    const complement = count ^ 0xffff;
    output[destination++] = block + 1 === blockCount ? 1 : 0;
    output[destination++] = count & 0xff;
    output[destination++] = count >>> 8;
    output[destination++] = complement & 0xff;
    output[destination++] = complement >>> 8;
    output.set(input.subarray(source, source + count), destination);
    source += count;
    destination += count;
  }
  return output;
}

const adapter = await createLeanZipStoredAdapter({ bytes: wasm, descriptor });
for (const input of [
  new Uint8Array(),
  Uint8Array.of(0, 1, 127, 128, 255),
  new Uint8Array(65536).map((_, index) => index & 0xff),
  new Uint8Array(1024 * 1024).map((_, index) => index & 0xff),
]) {
  const result = adapter.compressStored(input);
  assert.deepEqual(result.bytes, storedReference(input));
  assert.deepEqual(new Uint8Array(inflateRawSync(result.bytes)), input);
  assert.equal(result.memory.frontierAfter, result.memory.frontierBefore);
}

console.log("lean-zip stored package smoke: PASS");
