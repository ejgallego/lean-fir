import { readFile } from "node:fs/promises";
import { performance } from "node:perf_hooks";

import {
  asUInt64,
  expectedMix,
  mask,
} from "./reference.mjs";

const wasmPath = process.argv[2];
if (wasmPath === undefined) {
  throw new Error("usage: node check.mjs <Smoke.wasm>");
}

const bytes = await readFile(wasmPath);
const { instance } = await WebAssembly.instantiate(bytes);
const { fir_lcnf_c_affine: affine, fir_lcnf_c_mix: mix } = instance.exports;

if (typeof affine !== "function" || typeof mix !== "function") {
  throw new Error("expected fir_lcnf_c_affine and fir_lcnf_c_mix exports");
}

const affineCases = [
  0n,
  1n,
  7n,
  0xffffffffffffffffn,
];
for (const input of affineCases) {
  const expected = (input * 3n + 1n) & mask;
  const actual = asUInt64(affine(input));
  if (actual !== expected) {
    throw new Error(`affine(${input}): expected ${expected}, got ${actual}`);
  }
}

const mixCases = [
  [0n, 17n],
  [1n, 17n],
  [10n, 17n],
  [1000n, 0x123456789abcdef0n],
];
for (const [rounds, seed] of mixCases) {
  const expected = expectedMix(rounds, seed);
  const actual = asUInt64(mix(rounds, seed));
  if (actual !== expected) {
    throw new Error(
      `mix(${rounds}, ${seed}): expected ${expected}, got ${actual}`,
    );
  }
}

const benchmarkRounds = BigInt(
  process.env.FIR_WASM_BENCH_ROUNDS ?? "100000000",
);
const benchmarkSeed = 0x123456789abcdef0n;
const expected = expectedMix(benchmarkRounds, benchmarkSeed);
const start = performance.now();
const actual = asUInt64(mix(benchmarkRounds, benchmarkSeed));
const elapsedMs = performance.now() - start;

if (actual !== expected) {
  throw new Error(
    `benchmark: expected ${expected}, got ${actual}`,
  );
}

const roundsPerSecond =
  Number(benchmarkRounds) / (elapsedMs / 1000);
console.log(
  JSON.stringify(
    {
      artifact: wasmPath,
      byteLength: bytes.byteLength,
      benchmarkRounds: benchmarkRounds.toString(),
      elapsedMs,
      roundsPerSecond,
      result: actual.toString(),
    },
    null,
    2,
  ),
);
