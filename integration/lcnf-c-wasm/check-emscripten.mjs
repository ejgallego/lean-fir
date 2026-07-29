import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { performance } from "node:perf_hooks";

import {
  asUInt64,
  expectedHeapChecksum,
  expectedRuntimeChecksum,
} from "./reference.mjs";

const modulePath = process.argv[2];
const wasmPath = process.argv[3];
const nativeResultsPath = process.argv[4];
if (
  modulePath === undefined ||
  wasmPath === undefined ||
  nativeResultsPath === undefined
) {
  throw new Error(
    "usage: node check-emscripten.mjs <RuntimeSmoke.mjs> <RuntimeSmoke.wasm> <RuntimeSmoke.native.txt>",
  );
}

const [{ default: createModule }, bytes, nativeResults] = await Promise.all([
  import(pathToFileURL(resolve(modulePath))),
  readFile(wasmPath),
  readFile(nativeResultsPath, "utf8"),
]);
const stderr = [];
const module = await createModule({
  printErr: (line) => stderr.push(String(line)),
});
const heapChecksum = module._fir_lcnf_c_heap_checksum;
const runtimeChecksum = module._fir_lcnf_c_runtime_checksum;
const runtimeInitialize = module._fir_lcnf_c_runtime_initialize;

if (typeof heapChecksum !== "function") {
  throw new Error("expected fir_lcnf_c_heap_checksum export");
}
if (typeof runtimeChecksum !== "function") {
  throw new Error("expected fir_lcnf_c_runtime_checksum export");
}
if (typeof runtimeInitialize !== "function") {
  throw new Error("expected fir_lcnf_c_runtime_initialize export");
}

const initializationCode = runtimeInitialize();
if (initializationCode !== 0) {
  throw new Error(
    `runtime initialization failed with ${initializationCode}: ${JSON.stringify(stderr)}`,
  );
}
if (!stderr.includes("fir-lcnf-c:init-std")) {
  throw new Error(
    `full Init IO probe did not reach stderr: ${JSON.stringify(stderr)}`,
  );
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

const runtimeCases = [
  [0n, 17n],
  [1n, 17n],
  [10n, 17n],
  [1000n, 0x123456789abcdef0n],
  [16384n, 0xffffffffffffffffn],
];
const nativeChecksums = new Map(
  nativeResults
    .trim()
    .split("\n")
    .map((line) => {
      const [rounds, seed, checksum] = line.split(" ");
      return [`${rounds}:${seed}`, BigInt(checksum)];
    }),
);
for (const [rounds, seed] of runtimeCases) {
  const expected = expectedRuntimeChecksum(rounds, seed);
  const native = nativeChecksums.get(`${rounds}:${seed}`);
  if (native === undefined) {
    throw new Error(`native runtime result is missing for ${rounds}, ${seed}`);
  }
  if (native !== expected) {
    throw new Error(
      `native runtimeChecksum(${rounds}, ${seed}): expected ${expected}, got ${native}`,
    );
  }
  const actual = asUInt64(runtimeChecksum(rounds, seed));
  if (actual !== native) {
    throw new Error(
      `Wasm runtimeChecksum(${rounds}, ${seed}): native ${native}, got ${actual}`,
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
      runtimeCases: runtimeCases.length,
      nativeResults: nativeResultsPath,
      stderr,
      result: actual.toString(),
    },
    null,
    2,
  ),
);
