import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { inflateRawSync } from "node:zlib";

const [wasmPath, descriptorPath, adapterPath, label = "module",
  lengthText = "65536", family = "structured"] = process.argv.slice(2);
assert.ok(wasmPath && descriptorPath && adapterPath,
  "usage: node array-scaling-bench.mjs WASM DESCRIPTOR ADAPTER [LABEL] [BYTES] [structured|random]");
const length = Number(lengthText);
assert.ok(Number.isSafeInteger(length) && length >= 0,
  "input length must be a nonnegative safe integer");
assert.ok(family === "structured" || family === "random",
  "input family must be structured or random");

const { createLeanZipRawAdapter } = await import(adapterPath);
const bytes = readFileSync(wasmPath);
const descriptor = JSON.parse(readFileSync(descriptorPath, "utf8"));
const sha256 = (value) => createHash("sha256").update(value).digest("hex");
const input = new Uint8Array(length);
let state = 0x10203040;
for (let index = 0; index < input.length; index += 1) {
  state ^= state << 13;
  state ^= state >>> 17;
  state ^= state << 5;
  const random = state >>> 24;
  input[index] = family === "structured" && index % 5 === 0 ? 0x61 : random;
}

const module = await WebAssembly.compile(bytes);
const adapter = await createLeanZipRawAdapter({ module, descriptor });
for (let index = 0; index < 2; index += 1) adapter.compressRaw(input, 6);

const samples = [];
const frontiers = [];
let outputSha256 = null;
for (let index = 0; index < 7; index += 1) {
  const result = adapter.compressRaw(input, 6);
  assert.deepEqual(new Uint8Array(inflateRawSync(result.bytes)), input);
  const digest = sha256(result.bytes);
  outputSha256 ??= digest;
  assert.equal(digest, outputSha256);
  samples.push(result.timings.executeMs);
  frontiers.push(result.memory.frontierAfter);
}
const sorted = samples.toSorted((left, right) => left - right);
console.log(JSON.stringify({
  label,
  family,
  inputBytes: input.byteLength,
  inputSha256: sha256(input),
  outputSha256,
  wasmSha256: sha256(bytes),
  executeMs: {
    median: sorted[Math.floor(sorted.length / 2)],
    min: sorted[0],
    max: sorted.at(-1),
    samples,
  },
  frontierFlat: frontiers.every((value) => value === frontiers[0]),
  frontier: frontiers[0],
}));
