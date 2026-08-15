import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { inflateRawSync } from "node:zlib";

import {
  LEAN_ZIP_RAW_PERSISTENT_INITIALIZER,
  createLeanZipRawAdapter,
} from "./lean-zip-raw-browser-adapter.mjs";
import { STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES } from
  "./standard-libm-runtime-contract.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const wasm = readFileSync(join(directory, "_build/lean-zip-raw.wasm"));
const descriptor = JSON.parse(readFileSync(
  join(directory, "_build/lean-zip-raw.wasm.json"), "utf8"));
const oracle = join(directory, ".lake/build/bin/leanZipFirOracle");

const sequence = (length, seed) => {
  const result = new Uint8Array(length);
  let state = seed >>> 0;
  for (let index = 0; index < length; index += 1) {
    state ^= state << 13;
    state ^= state >>> 17;
    state ^= state << 5;
    result[index] = state >>> 24;
  }
  return result;
};

const cases = [
  ["empty", new Uint8Array()],
  ["boundaries", Uint8Array.of(0, 1, 127, 128, 254, 255)],
  ["repeated", new Uint8Array(4096).fill(0x61)],
  ["random", sequence(4096, 0x10203040)],
  ["unicode", new TextEncoder().encode("Lean λ → Wasm 🦆".repeat(64))],
];
const levels = Array.from({ length: 10 }, (_, index) => index + 1);

const adapter = await createLeanZipRawAdapter({ bytes: wasm, descriptor });
assert.equal(adapter.initialization.entry, LEAN_ZIP_RAW_PERSISTENT_INITIALIZER);
assert.equal(adapter.initialization.reservedFrontier,
  STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES);
assert.equal(adapter.initialization.initialFrontier,
  STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES);
assert.equal(adapter.initialization.checkpoint,
  adapter.initialization.initialFrontier);
let persistentCheckpoint = adapter.initialization.checkpoint;
const temporary = mkdtempSync(join(tmpdir(), "fir-lean-zip-raw-"));
try {
  for (const [name, input] of cases) {
    const inputPath = join(temporary, `${name}.input`);
    writeFileSync(inputPath, input);
    for (const level of levels) {
      const outputPath = join(temporary, `${name}-L${level}.oracle`);
      execFileSync(oracle, ["raw", String(level), inputPath, outputPath]);
      const expected = new Uint8Array(readFileSync(outputPath));
      const before = input.slice();
      const result = adapter.compressRaw(input, level);
      assert.deepEqual(result.bytes, expected,
        `${name}/L${level}: native differential`);
      assert.deepEqual(input, before, `${name}/L${level}: borrowed input mutated`);
      assert.deepEqual(new Uint8Array(inflateRawSync(result.bytes)), input,
        `${name}/L${level}: raw DEFLATE roundtrip`);
      assert.equal(result.memory.frontierBefore, persistentCheckpoint,
        `${name}/L${level}: persistent checkpoint moved`);
      assert.ok(result.memory.frontierAfter >= persistentCheckpoint,
        `${name}/L${level}: cache-aware rewind moved backwards`);
      persistentCheckpoint = result.memory.frontierAfter;
      const warm = adapter.compressRaw(input, level);
      assert.deepEqual(warm.bytes, expected,
        `${name}/L${level}: warm native differential`);
      assert.equal(warm.memory.frontierBefore, persistentCheckpoint,
        `${name}/L${level}: warm checkpoint moved`);
      assert.equal(warm.memory.frontierAfter, persistentCheckpoint,
        `${name}/L${level}: warm scratch rewind`);
    }
  }
  assert.throws(() => adapter.compressRaw(Uint8Array.of(1), 0), /1\.\.10/);
  assert.throws(() => adapter.compressRaw(Uint8Array.of(1), 11), /1\.\.10/);

  let clock = 0;
  const timed = await createLeanZipRawAdapter({
    module: await WebAssembly.compile(wasm),
    descriptor,
    now: () => clock++,
  });
  assert.equal(timed.initialization.initializeMs, 0);
  assert.equal(timed.initialization.idempotenceMs, 0);
  assert.deepEqual(timed.compressRaw(Uint8Array.of(1, 2, 3), 6).timings, {
    encodeMs: 1,
    executeMs: 1,
    decodeMs: 1,
    totalMs: 7,
    overheadMs: 4,
  });
  console.log(`native/Wasm raw dispatcher differential: PASS (${cases.length} cases × ${levels.length} levels)`);
  console.log("zero-import complete-runtime levels 1–10 ByteArray adapter: PASS");
  console.log("persistent-cache + scratch checkpoint reclamation: PASS");
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
