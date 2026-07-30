import { readFile } from "node:fs/promises";
import { performance } from "node:perf_hooks";
import { WASI } from "node:wasi";

import {
  asUInt64,
  expectedHeapChecksum,
  expectedMix,
  mask,
} from "./reference.mjs";

const wasmPath = process.argv[2];
const nativeResultsPath = process.argv[3];
if (wasmPath === undefined || nativeResultsPath === undefined) {
  throw new Error(
    "usage: node check-wasi.mjs <HeapSmoke.wasm> <HeapSmoke.native.txt>",
  );
}

const [bytes, nativeResults] = await Promise.all([
  readFile(wasmPath),
  readFile(nativeResultsPath, "utf8"),
]);
const compiled = await WebAssembly.compile(bytes);
const imports = WebAssembly.Module.imports(compiled);
const nonWasiImport = imports.find(
  ({ module }) => module !== "wasi_snapshot_preview1",
);
if (nonWasiImport !== undefined) {
  throw new Error(
    `WASI core profile has a non-WASI import: ${JSON.stringify(nonWasiImport)}`,
  );
}
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
  fir_lcnf_c_heap_checksum: heapChecksum,
  fir_lcnf_c_wasi_runtime_abi: runtimeAbi,
  fir_lcnf_c_wasi_allocations: allocations,
  fir_lcnf_c_wasi_deallocations: deallocations,
  fir_lcnf_c_wasi_live_objects: liveObjects,
  fir_lcnf_c_wasi_peak_live_objects: peakLiveObjects,
} = instance.exports;

if (
  typeof affine !== "function" ||
  typeof mix !== "function" ||
  typeof monotonicNs !== "function" ||
  typeof heapChecksum !== "function" ||
  typeof runtimeAbi !== "function" ||
  typeof allocations !== "function" ||
  typeof deallocations !== "function" ||
  typeof liveObjects !== "function" ||
  typeof peakLiveObjects !== "function"
) {
  throw new Error("expected scalar, heap-runtime, and WASI clock exports");
}
if (runtimeAbi() !== 1) {
  throw new Error(`unsupported WASI Lean core runtime ABI: ${runtimeAbi()}`);
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

const nativeChecksums = new Map(
  nativeResults
    .trim()
    .split("\n")
    .map((line) => {
      const [rounds, seed, checksum] = line.split(" ");
      return [`${rounds}:${seed}`, BigInt(checksum)];
    }),
);
const heapCases = [
  [0n, 17n],
  [1n, 17n],
  [10n, 17n],
  [1000n, 0x123456789abcdef0n],
  [65536n, mask],
];
for (const [rounds, seed] of heapCases) {
  const expected = expectedHeapChecksum(rounds, seed);
  const native = nativeChecksums.get(`${rounds}:${seed}`);
  if (native === undefined) {
    throw new Error(`native heap result is missing for ${rounds}, ${seed}`);
  }
  if (native !== expected) {
    throw new Error(
      `native heapChecksum(${rounds}, ${seed}): expected ${expected}, got ${native}`,
    );
  }

  const allocationsBefore = asUInt64(allocations());
  const deallocationsBefore = asUInt64(deallocations());
  const actual = asUInt64(heapChecksum(rounds, seed));
  const allocationsAfter = asUInt64(allocations());
  const deallocationsAfter = asUInt64(deallocations());
  const expectedObjects = rounds * 2n;

  if (actual !== native) {
    throw new Error(
      `WASI heapChecksum(${rounds}, ${seed}): native ${native}, got ${actual}`,
    );
  }
  if (
    allocationsAfter - allocationsBefore !== expectedObjects ||
    deallocationsAfter - deallocationsBefore !== expectedObjects
  ) {
    throw new Error(
      `WASI heap object accounting mismatch for ${rounds}: ` +
        `${allocationsAfter - allocationsBefore} allocations, ` +
        `${deallocationsAfter - deallocationsBefore} deallocations`,
    );
  }
  if (asUInt64(liveObjects()) !== 0n) {
    throw new Error(`WASI heap leaked objects after ${rounds} rounds`);
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

const heapBenchmarkRounds = BigInt(
  process.env.FIR_WASM_HEAP_BENCH_ROUNDS ?? "1000000",
);
const heapBenchmarkExpected = expectedHeapChecksum(
  heapBenchmarkRounds,
  benchmarkSeed,
);
const heapAllocationsBefore = asUInt64(allocations());
const heapDeallocationsBefore = asUInt64(deallocations());
const heapStart = performance.now();
const heapActual = asUInt64(
  heapChecksum(heapBenchmarkRounds, benchmarkSeed),
);
const heapElapsedMs = performance.now() - heapStart;
const heapAllocationsAfter = asUInt64(allocations());
const heapDeallocationsAfter = asUInt64(deallocations());
const heapBenchmarkObjects = heapBenchmarkRounds * 2n;
if (heapActual !== heapBenchmarkExpected) {
  throw new Error(
    `heap benchmark: expected ${heapBenchmarkExpected}, got ${heapActual}`,
  );
}
if (
  heapAllocationsAfter - heapAllocationsBefore !== heapBenchmarkObjects ||
  heapDeallocationsAfter - heapDeallocationsBefore !== heapBenchmarkObjects
) {
  throw new Error(
    "WASI heap benchmark object accounting does not match its logical size",
  );
}
if (asUInt64(liveObjects()) !== 0n) {
  throw new Error("WASI heap benchmark leaked objects");
}
if (asUInt64(peakLiveObjects()) < heapBenchmarkObjects) {
  throw new Error("WASI heap benchmark did not retain the full constructed list");
}
if (asUInt64(allocations()) !== asUInt64(deallocations())) {
  throw new Error("WASI heap runtime allocation totals are unbalanced");
}

console.log(
  JSON.stringify(
    {
      profile: "wasi-preview1-lean-core-reactor",
      artifact: wasmPath,
      wasmByteLength: bytes.byteLength,
      imports,
      benchmarkRounds: benchmarkRounds.toString(),
      elapsedMs,
      roundsPerSecond: Number(benchmarkRounds) / (elapsedMs / 1000),
      result: actual.toString(),
      heapCases: heapCases.length,
      nativeResults: nativeResultsPath,
      heapBenchmarkRounds: heapBenchmarkRounds.toString(),
      heapElapsedMs,
      heapLogicalElementsPerSecond:
        Number(heapBenchmarkRounds) / (heapElapsedMs / 1000),
      heapResult: heapActual.toString(),
      allocations: asUInt64(allocations()).toString(),
      deallocations: asUInt64(deallocations()).toString(),
      liveObjects: asUInt64(liveObjects()).toString(),
      peakLiveObjects: asUInt64(peakLiveObjects()).toString(),
    },
    null,
    2,
  ),
);
