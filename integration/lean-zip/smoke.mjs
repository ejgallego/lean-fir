import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { inflateRawSync } from "node:zlib";

import { createLeanZipStoredAdapter } from
  "./lean-zip-stored-browser-adapter.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const wasm = readFileSync(join(directory, "_build/lean-zip-stored.wasm"));
const descriptor = JSON.parse(readFileSync(
  join(directory, "_build/lean-zip-stored.wasm.json"), "utf8"));
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
  ["one", Uint8Array.of(0)],
  ["byte-boundaries", Uint8Array.of(0, 1, 127, 128, 254, 255)],
  ["unicode-utf8", new TextEncoder().encode("Lean λ → Wasm 🦆")],
  ["one-kib", sequence(1024, 0x10203040)],
  ["block-minus-one", sequence(65534, 0x11111111)],
  ["one-block", sequence(65535, 0x22222222)],
  ["block-plus-one", sequence(65536, 0x33333333)],
  ["three-block-edge", sequence(131071, 0x44444444)],
  ["one-mib", sequence(1024 * 1024, 0x55555555)],
];

const adapter = await createLeanZipStoredAdapter({ bytes: wasm, descriptor });
const temporary = mkdtempSync(join(tmpdir(), "fir-lean-zip-stored-"));
try {
  for (const [name, input] of cases) {
    const inputPath = join(temporary, `${name}.input`);
    const outputPath = join(temporary, `${name}.oracle`);
    writeFileSync(inputPath, input);
    execFileSync(oracle, ["stored", inputPath, outputPath]);
    const expected = new Uint8Array(readFileSync(outputPath));
    const before = input.slice();
    const result = adapter.compressStored(input);
    assert.deepEqual(result.bytes, expected, `${name}: native differential`);
    assert.deepEqual(input, before, `${name}: borrowed input mutated`);
    assert.deepEqual(new Uint8Array(inflateRawSync(result.bytes)), input,
      `${name}: raw DEFLATE roundtrip`);
    assert.equal(result.memory.frontierAfter, result.memory.frontierBefore,
      `${name}: scratch rewind`);
    assert.ok(result.memory.peakFrontier >= result.memory.frontierBefore);
    for (const timing of ["encodeMs", "executeMs", "decodeMs", "totalMs",
        "overheadMs"]) {
      assert.ok(Number.isFinite(result.timings[timing]) &&
        result.timings[timing] >= 0, `${name}: ${timing}`);
    }
  }

  const second = await createLeanZipStoredAdapter({
    module: await WebAssembly.compile(wasm), descriptor,
  });
  const left = adapter.compressStored(sequence(257, 1));
  const right = second.compressStored(sequence(257, 2));
  assert.notDeepEqual(left.bytes, right.bytes, "independent instances");
  assert.equal(left.memory.frontierAfter, left.memory.frontierBefore);
  assert.equal(right.memory.frontierAfter, right.memory.frontierBefore);

  let clock = 0;
  const timed = await createLeanZipStoredAdapter({
    bytes: wasm,
    descriptor,
    now: () => clock++,
  });
  const timing = timed.compressStored(Uint8Array.of(1, 2, 3)).timings;
  assert.deepEqual(timing, {
    encodeMs: 1,
    executeMs: 1,
    decodeMs: 1,
    totalMs: 7,
    overheadMs: 4,
  });

  assert.throws(() => adapter.compressStored([1, 2, 3]),
    /ArrayBuffer or view/);
  console.log(`native/Wasm stored differential: PASS (${cases.length} cases)`);
  console.log("zero-import packed ByteArray adapter: PASS");
  console.log("scratch checkpoint reclamation: PASS");
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
