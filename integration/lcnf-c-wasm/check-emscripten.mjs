import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { performance } from "node:perf_hooks";

import { loadEmscriptenModule } from "./emscripten-loader.mjs";
import {
  asUInt64,
  expectedHeapChecksum,
  expectedRuntimeChecksum,
} from "./reference.mjs";

const manifestPath = process.argv[2];
const nativeResultsPath = process.argv[3];
if (manifestPath === undefined || nativeResultsPath === undefined) {
  throw new Error(
    "usage: node check-emscripten.mjs <RuntimeSmoke.manifest.json> <RuntimeSmoke.native.txt>",
  );
}

const resolvedManifestPath = resolve(manifestPath);
const manifestURL = pathToFileURL(resolvedManifestPath);
const [manifestText, nativeResults] = await Promise.all([
  readFile(resolvedManifestPath, "utf8"),
  readFile(nativeResultsPath, "utf8"),
]);
const parsedManifest = JSON.parse(manifestText);
if (parsedManifest.build?.runtimeProfile !== "threaded") {
  throw new Error(
    `unexpected default runtime profile: ${parsedManifest.build?.runtimeProfile}`,
  );
}
if (
  parsedManifest.runtime?.threads !== true ||
  parsedManifest.runtime.crossOriginIsolated !== true
) {
  throw new Error(
    `untruthful threaded metadata: ${JSON.stringify(parsedManifest.runtime)}`,
  );
}
if (!parsedManifest.build.compileFlags.includes("-pthread")) {
  throw new Error("threaded compile flags omit -pthread");
}
if (!parsedManifest.build.linkFlags.includes("-pthread")) {
  throw new Error("threaded link flags omit -pthread");
}

async function requireDigestRejection(artifact, label) {
  const tamperedManifest = structuredClone(parsedManifest);
  tamperedManifest.artifacts[artifact].sha256 = "0".repeat(64);
  let rejected = false;
  try {
    await loadEmscriptenModule(tamperedManifest, {
      baseURL: new URL(".", manifestURL),
    });
  } catch (error) {
    if (String(error).includes(`${label} digest mismatch`)) {
      rejected = true;
    } else {
      throw error;
    }
  }
  if (!rejected) {
    throw new Error(`loader accepted a false ${label} digest`);
  }
}

await Promise.all([
  requireDigestRejection("module", "JavaScript module"),
  requireDigestRejection("wasm", "Wasm"),
]);

const stderr = [];
const loaded = await loadEmscriptenModule(manifestURL, {
  moduleOptions: {
    printErr: (line) => stderr.push(String(line)),
  },
});
const heapChecksum = loaded.exports.fir_lcnf_c_heap_checksum;
const runtimeChecksum = loaded.exports.fir_lcnf_c_runtime_checksum;
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
      manifest: manifestPath,
      module: loaded.manifest.artifacts.module.file,
      wasm: loaded.manifest.artifacts.wasm.file,
      wasmByteLength: loaded.wasmByteLength,
      verifiedDigests: true,
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
