import { readFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { pathToFileURL } from "node:url";

import { loadEmscriptenModule } from "./emscripten-loader.mjs";
import { inspectSingleImportedMemory } from "./wasm-memory.mjs";

function fail(message) {
  throw new Error(`benchmark-emscripten.mjs: ${message}`);
}

function unsigned(name, text, { safe = false } = {}) {
  if (text === undefined || !/^(0|[1-9][0-9]*)$/.test(text)) {
    fail(`${name} must be an unsigned decimal integer`);
  }
  const value = BigInt(text);
  if (safe) {
    const number = Number(value);
    if (!Number.isSafeInteger(number)) {
      fail(`${name} exceeds the JavaScript safe integer range`);
    }
    return number;
  }
  return value;
}

async function processThreadCount() {
  try {
    const status = await readFile("/proc/self/status", "utf8");
    const match = /^Threads:\s+([0-9]+)$/m.exec(status);
    return match === null ? null : Number(match[1]);
  } catch (error) {
    if (error?.code === "ENOENT") {
      return null;
    }
    throw error;
  }
}

const [
  manifestArgument,
  phase,
  roundsArgument,
  iterationsArgument,
  warmupIterationsArgument,
  seedArgument,
] = process.argv.slice(2);
if (
  manifestArgument === undefined ||
  !["startup", "steady"].includes(phase)
) {
  fail(
    "usage: node benchmark-emscripten.mjs <manifest> <startup|steady> " +
      "<rounds> <iterations> <warmup-iterations> <seed>",
  );
}

const rounds = unsigned("rounds", roundsArgument);
const iterations = unsigned("iterations", iterationsArgument, { safe: true });
const warmupIterations = unsigned(
  "warmup iterations",
  warmupIterationsArgument,
  { safe: true },
);
const seed = unsigned("seed", seedArgument);
if (iterations === 0) {
  fail("iterations must be positive");
}

const manifestPath = resolve(manifestArgument);
const manifest = JSON.parse(await readFile(manifestPath, "utf8"));
const wasmPath = resolve(dirname(manifestPath), manifest.artifacts.wasm.file);
const declaredMemory = inspectSingleImportedMemory(await readFile(wasmPath));
const stderr = [];
const loadStart = process.hrtime.bigint();
const loaded = await loadEmscriptenModule(
  pathToFileURL(manifestPath),
  {
    moduleOptions: {
      printErr: (line) => stderr.push(String(line)),
    },
  },
);
const initializationElapsedNs = process.hrtime.bigint() - loadStart;
const runtimeChecksum = loaded.exports.fir_lcnf_c_runtime_checksum;
let subjectElapsedNs;
let result;

if (phase === "startup") {
  result = BigInt.asUintN(64, runtimeChecksum(rounds, seed));
  subjectElapsedNs = initializationElapsedNs;
} else {
  for (let index = 0; index < warmupIterations; index += 1) {
    runtimeChecksum(rounds, seed);
  }
  const start = process.hrtime.bigint();
  let aggregate = 0n;
  for (let index = 0; index < iterations; index += 1) {
    aggregate = BigInt.asUintN(
      64,
      aggregate +
        BigInt.asUintN(64, runtimeChecksum(rounds, seed)) +
        BigInt(index),
    );
  }
  subjectElapsedNs = process.hrtime.bigint() - start;
  result = aggregate;
}

const usage = process.resourceUsage();
const threads = await processThreadCount();

console.log(
  JSON.stringify({
    schemaVersion: 1,
    profile: "emscripten",
    phase,
    subjectElapsedNs: subjectElapsedNs.toString(),
    initializationElapsedNs: initializationElapsedNs.toString(),
    result: result.toString(),
    runtime: {
      maxRssBytes: usage.maxRSS * 1024,
      processThreadCount: threads,
      declaredMemory,
      sharedMemory: declaredMemory.shared,
    },
    stderr,
  }),
);
