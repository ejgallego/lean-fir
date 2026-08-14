import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile, realpath, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { performance } from "node:perf_hooks";
import { pathToFileURL } from "node:url";

const directory = path.dirname(new URL(import.meta.url).pathname);
const illuminateRoot = await realpath(process.env.ILLUMINATE_ROOT ??
  path.join(directory, ".illuminate"));
const packageRoot = await realpath(process.env.ILLUMINATE_FIR_V4_PLAYER_DIR ??
  path.join(directory, "_build/illuminate-selection-player-current"));
const rounds = Number(process.env.FIR_HOT_EVENT_BENCHMARK_ROUNDS ?? 8);
const samplesPerRound = Number(
  process.env.FIR_HOT_EVENT_BENCHMARK_SAMPLES ?? 240);
assert.ok(Number.isSafeInteger(rounds) && rounds >= 7);
assert.ok(Number.isSafeInteger(samplesPerRound) && samplesPerRound > 0);

const sha256 = (value) => createHash("sha256").update(value).digest("hex");

function quantile(values, fraction) {
  const sorted = [...values].sort((left, right) => left - right);
  return sorted[Math.floor((sorted.length - 1) * fraction)];
}

function summarize(values) {
  const median = quantile(values, 0.5);
  return {
    median,
    p95: quantile(values, 0.95),
    minimum: Math.min(...values),
    maximum: Math.max(...values),
    mean: values.reduce((sum, value) => sum + value, 0) / values.length,
    medianAbsoluteDeviation: quantile(
      values.map((value) => Math.abs(value - median)), 0.5),
  };
}

function summarizeRecords(records, fields) {
  return Object.fromEntries(fields.map((field) =>
    [field, summarize(records.map((record) => record[field]))]));
}

async function loadPackage() {
  const prefix = "illuminate-selection-player";
  const [adapterModule, wasm, manifestText, buildText] = await Promise.all([
    import(pathToFileURL(path.join(packageRoot,
      `${prefix}-browser-adapter.mjs`)).href),
    readFile(path.join(packageRoot, `${prefix}.wasm`)),
    readFile(path.join(packageRoot, `${prefix}.wasm.json`), "utf8"),
    readFile(path.join(packageRoot, "BUILD.json"), "utf8"),
  ]);
  const build = JSON.parse(buildText);
  assert.equal(sha256(wasm), build.wasm.sha256);
  return {
    adapter: await adapterModule.createIlluminateSelectionPlayerAdapter({
      bytes: wasm,
      manifest: JSON.parse(manifestText),
      build,
    }),
    identity: {
      directory: packageRoot,
      wasmBytes: wasm.byteLength,
      wasmSha256: sha256(wasm),
      firCommit: build.sources.fir.commit,
      illuminateCommit: build.sources.illuminate.commit,
      hotEvent: build.capabilities.hotEvent,
    },
  };
}

async function readExamples() {
  const html = await readFile(path.join(illuminateRoot,
    "test_output/anim-comparison.html"), "utf8");
  const marker = "var examples = ";
  const start = html.indexOf(marker);
  assert.notEqual(start, -1, "comparison example payload is missing");
  const jsonStart = start + marker.length;
  const jsonEnd = html.indexOf(";\n", jsonStart);
  assert.notEqual(jsonEnd, -1, "comparison example payload is incomplete");
  return {
    examples: JSON.parse(html.slice(jsonStart, jsonEnd)),
    identity: {
      htmlSha256: sha256(html),
      sourceRoot: illuminateRoot,
    },
  };
}

function dispatchTick(adapter, player, mode, timestamp) {
  return mode === "production"
    ? adapter.dispatchTick(player, timestamp)
    : adapter.dispatchTickTimed(player, timestamp);
}

function runRound(adapter, animation, mode, round) {
  const created = adapter.createPlayer(animation);
  assert.equal(created.ok, true, created.error);
  const records = [];
  let digest;
  try {
    for (let sample = 0; sample < samplesPerRound; ++sample) {
      for (const event of [
        { kind: "seek", frame: 0 },
        { kind: "advance" },
      ]) {
        const setup = adapter.dispatch(created.player, event);
        assert.equal(setup.ok, true, setup.error);
      }
      const setupTick = dispatchTick(adapter, created.player, mode, 0.125);
      assert.equal(setupTick.ok, true, setupTick.error);

      const started = performance.now();
      const result = dispatchTick(adapter, created.player, mode, 50.125);
      const wallMs = performance.now() - started;
      assert.equal(result.ok, true, result.error);
      if (mode === "production") {
        assert.equal(Object.hasOwn(result, "timings"), false);
        assert.equal(Object.hasOwn(result, "memory"), false);
      } else {
        assert.equal(result.memory.postRewindFrontier,
          result.memory.persistentCheckpoint);
        assert.equal(result.memory.scratchBytes, 0);
        assert.equal(result.memory.scratchAllocationCalls, 0);
      }
      const currentDigest = sha256(JSON.stringify({
        action: result.action,
        scheduleNextFrame: result.scheduleNextFrame,
      }));
      if (digest === undefined) digest = currentDigest;
      else assert.equal(currentDigest, digest);
      records.push({
        round,
        sample,
        mode,
        wallMs,
        ...(mode === "diagnostic" ? {
          ...result.timings,
          scratchBytes: result.memory.scratchBytes,
          scratchAllocationCalls: result.memory.scratchAllocationCalls,
          clearedBytes: result.memory.clearedBytes,
          frontierAfterEncode: result.memory.frontierAfterEncode,
          peakFrontier: result.memory.peakFrontier,
          postRewindFrontier: result.memory.postRewindFrontier,
        } : {}),
      });
    }
  } finally {
    adapter.disposePlayer(created.player);
  }
  return { records, digest };
}

const [{ adapter, identity }, examplesInput] = await Promise.all([
  loadPackage(),
  readExamples(),
]);
const examples = examplesInput.examples;
const titles = ["Pause-driven slide show", "Morphing arrows and final loop"];
const workloads = [];
for (const title of titles) {
  const example = examples.find((candidate) => candidate.title === title);
  assert.ok(example, `missing dashboard example ${title}`);

  runRound(adapter, example.data, "diagnostic", -1);
  runRound(adapter, example.data, "production", -1);

  const raw = { diagnostic: [], production: [] };
  const digests = { diagnostic: undefined, production: undefined };
  for (let round = 0; round < rounds; ++round) {
    const order = round % 2 === 0
      ? ["diagnostic", "production"]
      : ["production", "diagnostic"];
    for (const mode of order) {
      const result = runRound(adapter, example.data, mode, round);
      raw[mode].push(...result.records);
      digests[mode] = result.digest;
    }
  }
  assert.equal(digests.production, digests.diagnostic,
    `${title}: production tick differs from diagnostic tick`);
  assert.ok(raw.diagnostic.every((record) => record.scratchBytes === 0 &&
    record.scratchAllocationCalls === 0));
  workloads.push({
    title,
    actionDigest: digests.production,
    summary: {
      production: summarizeRecords(raw.production, ["wallMs"]),
      diagnostic: summarizeRecords(raw.diagnostic, [
        "wallMs", "encodeMs", "executeMs", "decodeMs", "rewindMs",
        "totalMs", "overheadMs", "scratchBytes", "scratchAllocationCalls",
        "clearedBytes",
      ]),
    },
    raw,
  });
}

const report = {
  schema: "fir.illuminate-selection-player.hot-event-benchmark/v2",
  generatedAt: new Date().toISOString(),
  policy: {
    warmupRounds: 1,
    measuredRounds: rounds,
    samplesPerRound,
    orderBalanced: true,
    profilerAttached: false,
    semanticOracle:
      "dispatchTickTimed uses the same bit-exact Wasm entry; generic dispatch(PlayerEvent.tick) is checked by package and 107-trace gates",
  },
  environment: {
    node: process.version,
    v8: process.versions.v8,
    platform: process.platform,
    arch: process.arch,
    cpu: os.cpus()[0]?.model ?? "unknown",
  },
  input: examplesInput.identity,
  package: identity,
  workloads,
};
const output = path.join(directory,
  "_build/illuminate-selection-hot-event-benchmark.json");
await writeFile(output, `${JSON.stringify(report, null, 2)}\n`);

for (const workload of workloads) {
  const diagnostic = workload.summary.diagnostic;
  const production = workload.summary.production;
  console.log(workload.title);
  console.log(`  whole callback median diagnostic -> production: ` +
    `${diagnostic.wallMs.median.toFixed(5)} -> ` +
    `${production.wallMs.median.toFixed(5)} ms`);
  console.log(`  whole callback p95 diagnostic -> production: ` +
    `${diagnostic.wallMs.p95.toFixed(5)} -> ` +
    `${production.wallMs.p95.toFixed(5)} ms`);
  console.log(`  diagnostic phase medians: encode ` +
    `${diagnostic.encodeMs.median.toFixed(5)}, execute ` +
    `${diagnostic.executeMs.median.toFixed(5)}, decode ` +
    `${diagnostic.decodeMs.median.toFixed(5)}, rewind ` +
    `${diagnostic.rewindMs.median.toFixed(5)} ms`);
}
console.log(`wrote ${output}`);
