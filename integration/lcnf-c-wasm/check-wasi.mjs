import { readFile } from "node:fs/promises";
import { performance } from "node:perf_hooks";
import { WASI } from "node:wasi";

import {
  asUInt64,
  expectedHeapChecksum,
  expectedMix,
  expectedWasiCoreChecksum,
  expectedWasiScalarChecksum,
  mask,
} from "./reference.mjs";

const wasmPath = process.argv[2];
const nativeHeapResultsPath = process.argv[3];
const nativeCoreResultsPath = process.argv[4];
const nativeScalarResultsPath = process.argv[5];
if (
  wasmPath === undefined ||
  nativeHeapResultsPath === undefined ||
  nativeCoreResultsPath === undefined ||
  nativeScalarResultsPath === undefined
) {
  throw new Error(
    "usage: node check-wasi.mjs <WasiCoreSmoke.wasm> " +
      "<HeapSmoke.native.txt> <WasiCoreSmoke.native.txt> " +
      "<WasiScalarSmoke.native.txt>",
  );
}

const [
  bytes,
  nativeHeapResults,
  nativeCoreResults,
  nativeScalarResults,
] = await Promise.all([
  readFile(wasmPath),
  readFile(nativeHeapResultsPath, "utf8"),
  readFile(nativeCoreResultsPath, "utf8"),
  readFile(nativeScalarResultsPath, "utf8"),
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
  fir_lcnf_c_wasi_core_checksum: wasiCoreChecksum,
  fir_lcnf_c_wasi_scalar_checksum: wasiScalarChecksum,
  fir_lcnf_c_wasi_runtime_abi: runtimeAbi,
  fir_lcnf_c_wasi_allocations: allocations,
  fir_lcnf_c_wasi_deallocations: deallocations,
  fir_lcnf_c_wasi_live_objects: liveObjects,
  fir_lcnf_c_wasi_peak_live_objects: peakLiveObjects,
  fir_lcnf_c_wasi_constructor_deallocations: constructorDeallocations,
  fir_lcnf_c_wasi_closure_deallocations: closureDeallocations,
  fir_lcnf_c_wasi_array_deallocations: arrayDeallocations,
  fir_lcnf_c_wasi_scalar_array_deallocations: scalarArrayDeallocations,
  fir_lcnf_c_wasi_string_deallocations: stringDeallocations,
} = instance.exports;

if (
  typeof affine !== "function" ||
  typeof mix !== "function" ||
  typeof monotonicNs !== "function" ||
  typeof heapChecksum !== "function" ||
  typeof wasiCoreChecksum !== "function" ||
  typeof wasiScalarChecksum !== "function" ||
  typeof runtimeAbi !== "function" ||
  typeof allocations !== "function" ||
  typeof deallocations !== "function" ||
  typeof liveObjects !== "function" ||
  typeof peakLiveObjects !== "function" ||
  typeof constructorDeallocations !== "function" ||
  typeof closureDeallocations !== "function" ||
  typeof arrayDeallocations !== "function" ||
  typeof scalarArrayDeallocations !== "function" ||
  typeof stringDeallocations !== "function"
) {
  throw new Error(
    "expected scalar, core-object runtime, telemetry, and WASI clock exports",
  );
}
if (runtimeAbi() !== 3) {
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

function parseNativeChecksums(results) {
  return new Map(
    results
      .trim()
      .split("\n")
      .map((line) => {
        const [rounds, seed, checksum] = line.split(" ");
        return [`${rounds}:${seed}`, BigInt(checksum)];
      }),
  );
}

const nativeHeapChecksums = parseNativeChecksums(nativeHeapResults);
const heapCases = [
  [0n, 17n],
  [1n, 17n],
  [10n, 17n],
  [1000n, 0x123456789abcdef0n],
  [65536n, mask],
];
for (const [rounds, seed] of heapCases) {
  const expected = expectedHeapChecksum(rounds, seed);
  const native = nativeHeapChecksums.get(`${rounds}:${seed}`);
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

const nativeCoreChecksums = parseNativeChecksums(nativeCoreResults);
const coreCases = [
  [0n, 17n],
  [1n, 17n],
  [10n, 17n],
  [1000n, 0x123456789abcdef0n],
  [65536n, mask],
];
for (const [rounds, seed] of coreCases) {
  const expected = expectedWasiCoreChecksum(rounds, seed);
  const native = nativeCoreChecksums.get(`${rounds}:${seed}`);
  if (native === undefined) {
    throw new Error(`native core result is missing for ${rounds}, ${seed}`);
  }
  if (native !== expected) {
    throw new Error(
      `native wasiCoreChecksum(${rounds}, ${seed}): ` +
        `expected ${expected}, got ${native}`,
    );
  }

  const allocationsBefore = asUInt64(allocations());
  const deallocationsBefore = asUInt64(deallocations());
  const constructorBefore = asUInt64(constructorDeallocations());
  const closureBefore = asUInt64(closureDeallocations());
  const arrayBefore = asUInt64(arrayDeallocations());
  const scalarArrayBefore = asUInt64(scalarArrayDeallocations());
  const stringBefore = asUInt64(stringDeallocations());
  const actual = asUInt64(wasiCoreChecksum(rounds, seed));
  const allocationDelta = asUInt64(allocations()) - allocationsBefore;
  const deallocationDelta = asUInt64(deallocations()) - deallocationsBefore;
  const constructorDelta =
    asUInt64(constructorDeallocations()) - constructorBefore;
  const closureDelta = asUInt64(closureDeallocations()) - closureBefore;
  const arrayDelta = asUInt64(arrayDeallocations()) - arrayBefore;
  const scalarArrayDelta =
    asUInt64(scalarArrayDeallocations()) - scalarArrayBefore;
  const stringDelta = asUInt64(stringDeallocations()) - stringBefore;

  if (actual !== native) {
    throw new Error(
      `WASI wasiCoreChecksum(${rounds}, ${seed}): native ${native}, ` +
        `got ${actual}`,
    );
  }
  if (allocationDelta !== deallocationDelta) {
    throw new Error(
      `WASI core object accounting mismatch for ${rounds}: ` +
        `${allocationDelta} allocations, ${deallocationDelta} deallocations`,
    );
  }
  if (
    constructorDelta === 0n ||
    closureDelta !== 2n ||
    arrayDelta === 0n ||
    scalarArrayDelta !== 0n ||
    stringDelta !== 1n
  ) {
    throw new Error(
      `WASI core type reclamation mismatch for ${rounds}: ` +
        `${constructorDelta} constructors, ${closureDelta} closures, ` +
        `${arrayDelta} arrays, ${scalarArrayDelta} scalar arrays, ` +
        `${stringDelta} strings`,
    );
  }
  if (
    constructorDelta +
      closureDelta +
      arrayDelta +
      scalarArrayDelta +
      stringDelta !==
    deallocationDelta
  ) {
    throw new Error(
      `WASI core deallocation dispatch did not account for ${rounds}`,
    );
  }
  if (asUInt64(liveObjects()) !== 0n) {
    throw new Error(`WASI core leaked objects after ${rounds} rounds`);
  }
}

const nativeScalarChecksums = parseNativeChecksums(nativeScalarResults);
const scalarCases = [
  [0n, 17n],
  [1n, 17n],
  [10n, 17n],
  [1000n, 0x123456789abcdef0n],
  [65536n, mask],
];
for (const [rounds, seed] of scalarCases) {
  const expected = expectedWasiScalarChecksum(rounds, seed);
  const native = nativeScalarChecksums.get(`${rounds}:${seed}`);
  if (native === undefined) {
    throw new Error(`native scalar result is missing for ${rounds}, ${seed}`);
  }
  if (native !== expected) {
    throw new Error(
      `native wasiScalarChecksum(${rounds}, ${seed}): ` +
        `expected ${expected}, got ${native}`,
    );
  }

  const allocationsBefore = asUInt64(allocations());
  const deallocationsBefore = asUInt64(deallocations());
  const constructorBefore = asUInt64(constructorDeallocations());
  const closureBefore = asUInt64(closureDeallocations());
  const arrayBefore = asUInt64(arrayDeallocations());
  const scalarArrayBefore = asUInt64(scalarArrayDeallocations());
  const stringBefore = asUInt64(stringDeallocations());
  const actual = asUInt64(wasiScalarChecksum(rounds, seed));
  const allocationDelta = asUInt64(allocations()) - allocationsBefore;
  const deallocationDelta = asUInt64(deallocations()) - deallocationsBefore;
  const constructorDelta =
    asUInt64(constructorDeallocations()) - constructorBefore;
  const closureDelta = asUInt64(closureDeallocations()) - closureBefore;
  const arrayDelta = asUInt64(arrayDeallocations()) - arrayBefore;
  const scalarArrayDelta =
    asUInt64(scalarArrayDeallocations()) - scalarArrayBefore;
  const stringDelta = asUInt64(stringDeallocations()) - stringBefore;

  if (actual !== native) {
    throw new Error(
      `WASI wasiScalarChecksum(${rounds}, ${seed}): native ${native}, ` +
        `got ${actual}`,
    );
  }
  if (allocationDelta !== deallocationDelta) {
    throw new Error(
      `WASI scalar object accounting mismatch for ${rounds}: ` +
        `${allocationDelta} allocations, ${deallocationDelta} deallocations`,
    );
  }
  if (
    constructorDelta === 0n ||
    closureDelta !== 2n ||
    arrayDelta === 0n ||
    scalarArrayDelta === 0n ||
    stringDelta !== 0n
  ) {
    throw new Error(
      `WASI scalar type reclamation mismatch for ${rounds}: ` +
        `${constructorDelta} constructors, ${closureDelta} closures, ` +
        `${arrayDelta} arrays, ${scalarArrayDelta} scalar arrays, ` +
        `${stringDelta} strings`,
    );
  }
  if (
    constructorDelta +
      closureDelta +
      arrayDelta +
      scalarArrayDelta +
      stringDelta !==
    deallocationDelta
  ) {
    throw new Error(
      `WASI scalar deallocation dispatch did not account for ${rounds}`,
    );
  }
  if (asUInt64(liveObjects()) !== 0n) {
    throw new Error(`WASI scalar leaked objects after ${rounds} rounds`);
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

const coreBenchmarkRounds = BigInt(
  process.env.FIR_WASM_CORE_BENCH_ROUNDS ?? "262144",
);
const coreBenchmarkExpected = expectedWasiCoreChecksum(
  coreBenchmarkRounds,
  benchmarkSeed,
);
const coreAllocationsBefore = asUInt64(allocations());
const coreDeallocationsBefore = asUInt64(deallocations());
const coreStart = performance.now();
const coreActual = asUInt64(
  wasiCoreChecksum(coreBenchmarkRounds, benchmarkSeed),
);
const coreElapsedMs = performance.now() - coreStart;
const coreAllocationDelta =
  asUInt64(allocations()) - coreAllocationsBefore;
const coreDeallocationDelta =
  asUInt64(deallocations()) - coreDeallocationsBefore;
if (coreActual !== coreBenchmarkExpected) {
  throw new Error(
    `core benchmark: expected ${coreBenchmarkExpected}, got ${coreActual}`,
  );
}
if (coreAllocationDelta !== coreDeallocationDelta) {
  throw new Error(
    "WASI core benchmark allocation and deallocation totals differ",
  );
}
if (asUInt64(liveObjects()) !== 0n) {
  throw new Error("WASI core benchmark leaked objects");
}
if (asUInt64(allocations()) !== asUInt64(deallocations())) {
  throw new Error("WASI core runtime allocation totals are unbalanced");
}

const scalarBenchmarkRounds = BigInt(
  process.env.FIR_WASM_SCALAR_ARRAY_BENCH_ROUNDS ?? "262144",
);
const scalarBenchmarkExpected = expectedWasiScalarChecksum(
  scalarBenchmarkRounds,
  benchmarkSeed,
);
const scalarAllocationsBefore = asUInt64(allocations());
const scalarDeallocationsBefore = asUInt64(deallocations());
const scalarStart = performance.now();
const scalarActual = asUInt64(
  wasiScalarChecksum(scalarBenchmarkRounds, benchmarkSeed),
);
const scalarElapsedMs = performance.now() - scalarStart;
const scalarAllocationDelta =
  asUInt64(allocations()) - scalarAllocationsBefore;
const scalarDeallocationDelta =
  asUInt64(deallocations()) - scalarDeallocationsBefore;
if (scalarActual !== scalarBenchmarkExpected) {
  throw new Error(
    `scalar benchmark: expected ${scalarBenchmarkExpected}, ` +
      `got ${scalarActual}`,
  );
}
if (scalarAllocationDelta !== scalarDeallocationDelta) {
  throw new Error(
    "WASI scalar benchmark allocation and deallocation totals differ",
  );
}
if (asUInt64(liveObjects()) !== 0n) {
  throw new Error("WASI scalar benchmark leaked objects");
}
if (asUInt64(allocations()) !== asUInt64(deallocations())) {
  throw new Error("WASI core runtime allocation totals are unbalanced");
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
      nativeHeapResults: nativeHeapResultsPath,
      heapBenchmarkRounds: heapBenchmarkRounds.toString(),
      heapElapsedMs,
      heapLogicalElementsPerSecond:
        Number(heapBenchmarkRounds) / (heapElapsedMs / 1000),
      heapResult: heapActual.toString(),
      coreCases: coreCases.length,
      nativeCoreResults: nativeCoreResultsPath,
      coreBenchmarkRounds: coreBenchmarkRounds.toString(),
      coreElapsedMs,
      coreLogicalElementsPerSecond:
        Number(coreBenchmarkRounds) / (coreElapsedMs / 1000),
      coreResult: coreActual.toString(),
      scalarCases: scalarCases.length,
      nativeScalarResults: nativeScalarResultsPath,
      scalarBenchmarkRounds: scalarBenchmarkRounds.toString(),
      scalarElapsedMs,
      scalarLogicalElementsPerSecond:
        Number(scalarBenchmarkRounds) / (scalarElapsedMs / 1000),
      scalarResult: scalarActual.toString(),
      allocations: asUInt64(allocations()).toString(),
      deallocations: asUInt64(deallocations()).toString(),
      liveObjects: asUInt64(liveObjects()).toString(),
      peakLiveObjects: asUInt64(peakLiveObjects()).toString(),
      constructorDeallocations:
        asUInt64(constructorDeallocations()).toString(),
      closureDeallocations:
        asUInt64(closureDeallocations()).toString(),
      arrayDeallocations: asUInt64(arrayDeallocations()).toString(),
      scalarArrayDeallocations:
        asUInt64(scalarArrayDeallocations()).toString(),
      stringDeallocations: asUInt64(stringDeallocations()).toString(),
    },
    null,
    2,
  ),
);
