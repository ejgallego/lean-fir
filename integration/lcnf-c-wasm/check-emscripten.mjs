import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { performance } from "node:perf_hooks";

import {
  asUInt64,
  expectedHeapChecksum,
} from "./reference.mjs";

const modulePath = process.argv[2];
const wasmPath = process.argv[3];
if (modulePath === undefined || wasmPath === undefined) {
  throw new Error(
    "usage: node check-emscripten.mjs <HeapSmoke.mjs> <HeapSmoke.wasm>",
  );
}

const [{ default: createModule }, bytes] = await Promise.all([
  import(pathToFileURL(resolve(modulePath))),
  readFile(wasmPath),
]);
const module = await createModule();
const heapChecksum = module._fir_lcnf_c_heap_checksum;

if (typeof heapChecksum !== "function") {
  throw new Error("expected fir_lcnf_c_heap_checksum export");
}

const cases = [
  [0n, 17n],
  [1n, 17n],
  [10n, 17n],
  [1000n, 0x123456789abcdef0n],
  [65536n, 0xffffffffffffffffn],
];
for (const [rounds, seed] of cases) {
  const expected = expectedHeapChecksum(rounds, seed);
  const actual = asUInt64(heapChecksum(rounds, seed));
  if (actual !== expected) {
    throw new Error(
      `heapChecksum(${rounds}, ${seed}): expected ${expected}, got ${actual}`,
    );
  }
}

const benchmarkRounds = BigInt(
  process.env.FIR_WASM_HEAP_BENCH_ROUNDS ?? "1000000",
);
const benchmarkSeed = 0x123456789abcdef0n;
const expected = expectedHeapChecksum(benchmarkRounds, benchmarkSeed);
const start = performance.now();
const actual = asUInt64(heapChecksum(benchmarkRounds, benchmarkSeed));
const elapsedMs = performance.now() - start;

if (actual !== expected) {
  throw new Error(`benchmark: expected ${expected}, got ${actual}`);
}

console.log(
  JSON.stringify(
    {
      profile: "emscripten",
      module: modulePath,
      wasm: wasmPath,
      wasmByteLength: bytes.byteLength,
      benchmarkRounds: benchmarkRounds.toString(),
      elapsedMs,
      logicalElementsPerSecond:
        Number(benchmarkRounds) / (elapsedMs / 1000),
      result: actual.toString(),
    },
    null,
    2,
  ),
);
