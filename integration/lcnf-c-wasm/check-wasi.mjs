import { readFile } from "node:fs/promises";
import { performance } from "node:perf_hooks";
import { WASI } from "node:wasi";

import {
  asUInt64,
  expectedMix,
  mask,
} from "./reference.mjs";

const wasmPath = process.argv[2];
if (wasmPath === undefined) {
  throw new Error("usage: node check-wasi.mjs <Smoke.wasm>");
}

const bytes = await readFile(wasmPath);
const compiled = await WebAssembly.compile(bytes);
const imports = WebAssembly.Module.imports(compiled);
const wasiClock = imports.find(
  ({ module, name }) =>
    module === "wasi_snapshot_preview1" && name === "clock_time_get",
);
if (wasiClock === undefined) {
  throw new Error("WASI profile is missing the preview1 clock_time_get import");
}

const wasi = new WASI({
  version: "preview1",
  args: [],
  env: {},
  preopens: {},
});
const instance = await WebAssembly.instantiate(compiled, {
  wasi_snapshot_preview1: wasi.wasiImport,
});
wasi.initialize(instance);

const {
  fir_lcnf_c_affine: affine,
  fir_lcnf_c_mix: mix,
  fir_lcnf_c_wasi_monotonic_ns: monotonicNs,
} = instance.exports;

if (
  typeof affine !== "function" ||
  typeof mix !== "function" ||
  typeof monotonicNs !== "function"
) {
  throw new Error("expected scalar and WASI clock exports");
}

for (const input of [0n, 1n, 7n, mask]) {
  const expected = (input * 3n + 1n) & mask;
  const actual = asUInt64(affine(input));
  if (actual !== expected) {
    throw new Error(`affine(${input}): expected ${expected}, got ${actual}`);
  }
}

for (const [rounds, seed] of [
  [0n, 17n],
  [1n, 17n],
  [10n, 17n],
  [1000n, 0x123456789abcdef0n],
]) {
  const expected = expectedMix(rounds, seed);
  const actual = asUInt64(mix(rounds, seed));
  if (actual !== expected) {
    throw new Error(
      `mix(${rounds}, ${seed}): expected ${expected}, got ${actual}`,
    );
  }
}

const clockBefore = asUInt64(monotonicNs());
const clockAfter = asUInt64(monotonicNs());
if (clockBefore === mask || clockAfter === mask || clockAfter < clockBefore) {
  throw new Error(
    `invalid WASI monotonic clock values: ${clockBefore}, ${clockAfter}`,
  );
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
  throw new Error(`benchmark: expected ${expected}, got ${actual}`);
}

console.log(
  JSON.stringify(
    {
      profile: "wasi-preview1-reactor",
      artifact: wasmPath,
      wasmByteLength: bytes.byteLength,
      imports,
      benchmarkRounds: benchmarkRounds.toString(),
      elapsedMs,
      roundsPerSecond: Number(benchmarkRounds) / (elapsedMs / 1000),
      result: actual.toString(),
    },
    null,
    2,
  ),
);
