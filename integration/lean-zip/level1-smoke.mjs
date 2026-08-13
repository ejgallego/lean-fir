import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { inflateRawSync } from "node:zlib";

import {
  LEAN_ZIP_LEVEL1_PERSISTENT_INITIALIZER,
  createLeanZipLevel1Adapter,
} from
  "./lean-zip-level1-browser-adapter.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const wasm = readFileSync(join(directory, "_build/lean-zip-level1.wasm"));
const descriptor = JSON.parse(readFileSync(
  join(directory, "_build/lean-zip-level1.wasm.json"), "utf8"));
const oracle = join(directory, ".lake/build/bin/leanZipFirOracle");

const sequence = (length, seed) => {
  const result = new Uint8Array(length);
  let state = seed >>> 0;
  for (let index = 0; index < length; index += 1) {
    state = (Math.imul(state, 1664525) + 1013904223) >>> 0;
    result[index] = state >>> 24;
  }
  return result;
};

const cases = [
  ["empty", new Uint8Array()],
  ["boundaries", Uint8Array.of(0, 1, 127, 128, 254, 255)],
  ["repeated", new Uint8Array(4096).fill(0x61)],
  ["random", sequence(8192, 0x10203040)],
  ["unicode", new TextEncoder().encode("Lean λ → Wasm 🦆".repeat(64))],
];

const adapter = await createLeanZipLevel1Adapter({ bytes: wasm, descriptor });
assert.equal(adapter.initialization.entry,
  LEAN_ZIP_LEVEL1_PERSISTENT_INITIALIZER);
assert.ok(adapter.initialization.checkpoint >
  adapter.initialization.initialFrontier,
"persistent cache initialization must grow the lower arena");
assert.equal(adapter.initialization.frontierGrowth,
  adapter.initialization.checkpoint - adapter.initialization.initialFrontier);
const persistentCheckpoint = adapter.initialization.checkpoint;
const temporary = mkdtempSync(join(tmpdir(), "fir-lean-zip-level1-"));
try {
  for (const [name, input] of cases) {
    const inputPath = join(temporary, `${name}.input`);
    const outputPath = join(temporary, `${name}.oracle`);
    writeFileSync(inputPath, input);
    execFileSync(oracle, ["level1", inputPath, outputPath]);
    const expected = new Uint8Array(readFileSync(outputPath));
    const before = input.slice();
    const result = adapter.compressLevel1(input);
    assert.deepEqual(result.bytes, expected, `${name}: native differential`);
    assert.deepEqual(input, before, `${name}: borrowed input mutated`);
    assert.deepEqual(new Uint8Array(inflateRawSync(result.bytes)), input,
      `${name}: raw DEFLATE roundtrip`);
    assert.equal(result.memory.frontierAfter, result.memory.frontierBefore,
      `${name}: scratch rewind`);
    assert.equal(result.memory.frontierBefore, persistentCheckpoint,
      `${name}: persistent checkpoint moved`);
  }

  let clock = 0;
  const timed = await createLeanZipLevel1Adapter({
    module: await WebAssembly.compile(wasm),
    descriptor,
    now: () => clock++,
  });
  assert.equal(timed.initialization.initializeMs, 1);
  assert.equal(timed.initialization.idempotenceMs, 1);
  assert.deepEqual(timed.compressLevel1(Uint8Array.of(1, 2, 3)).timings, {
    encodeMs: 1,
    executeMs: 1,
    decodeMs: 1,
    totalMs: 7,
    overheadMs: 4,
  });
  console.log(`native/Wasm Level-1 differential: PASS (${cases.length} cases)`);
  console.log("zero-import Level-1 ByteArray adapter: PASS");
  console.log("persistent-cache + scratch checkpoint reclamation: PASS");
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
