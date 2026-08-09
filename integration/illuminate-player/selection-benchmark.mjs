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
const v3Root = await realpath(process.env.ILLUMINATE_FIR_V3_PLAYER_DIR ??
  path.join(directory, "_build/illuminate-player-current"));
const v4Root = await realpath(process.env.ILLUMINATE_FIR_V4_PLAYER_DIR ??
  path.join(directory, "_build/illuminate-selection-player-current"));
const rounds = Number(process.env.FIR_SELECTION_BENCHMARK_ROUNDS ?? 8);
const samplesPerRound = Number(process.env.FIR_SELECTION_BENCHMARK_SAMPLES ?? 120);
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

async function loadPackage(root, selection) {
  const prefix = selection ? "illuminate-selection-player" : "illuminate-player";
  const [adapterModule, wasm, manifestText, buildText] = await Promise.all([
    import(pathToFileURL(path.join(root, `${prefix}-browser-adapter.mjs`)).href),
    readFile(path.join(root, `${prefix}.wasm`)),
    readFile(path.join(root, `${prefix}.wasm.json`), "utf8"),
    readFile(path.join(root, "BUILD.json"), "utf8"),
  ]);
  const manifest = JSON.parse(manifestText);
  const build = JSON.parse(buildText);
  assert.equal(sha256(wasm), build.wasm.sha256);
  const create = selection
    ? adapterModule.createIlluminateSelectionPlayerAdapter
    : adapterModule.createIlluminatePlayerAdapter;
  return {
    root,
    selection,
    adapter: await create({ bytes: wasm, manifest, build }),
    identity: {
      wasmBytes: wasm.byteLength,
      wasmSha256: sha256(wasm),
      sourceDeclarations: build.runtime.sourceDeclarationCount,
      retainedSourceFunctions: build.runtime.retainedSourceFunctionCount,
      residentHelpers: build.runtime.residentHelperCount,
      functionImports: build.wasm.functionImportCount,
      memoryImports: build.wasm.memoryImportCount,
      functionExports: build.wasm.functionExportCount,
      adapterApi: build.capabilities.browserAdapter.apiVersion,
      inputLayout: build.capabilities.inputLayout.version,
      ownership: build.capabilities.ownership.version,
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
  return JSON.parse(html.slice(jsonStart, jsonEnd));
}

function v3Projection(animation) {
  return {
    fps: animation.fps,
    totalFrames: animation.totalFrames,
    segments: animation.segments.map((segment) => ({
      startFrame: segment.sf,
      frameCount: segment.fc,
      paramMap: segment.pmap.map((binding) => ({
        element: binding.e,
        target: binding.a === "textContent"
          ? { kind: "textContent" }
          : { kind: "attribute", name: binding.a },
      })),
      params: segment.params,
    })),
    steps: animation.steps,
  };
}

function v4Projection(animation) {
  return {
    timeline: {
      fps: animation.fps,
      totalFrames: animation.totalFrames,
      segments: animation.segments.map((segment) => ({
        startFrame: segment.sf,
        frameCount: segment.fc,
        paramMap: [],
        params: [],
      })),
      steps: animation.steps,
    },
  };
}

function materialize(animation, action) {
  const segment = animation.segments[action.segment];
  const values = segment.params[action.localFrame] ?? [];
  return {
    frame: action.frame,
    step: action.step,
    segment: action.segment,
    localFrame: action.localFrame,
    segmentChanged: action.segmentChanged,
    updates: segment.pmap.flatMap((binding, index) =>
      values[index] === undefined ? [] : [{
        e: binding.e,
        a: binding.a,
        v: values[index],
      }]),
    playback: action.playback,
  };
}

function runCandidate(candidate, animation, round) {
  const creationWallStarted = performance.now();
  const created = candidate.adapter.createPlayer(animation);
  const creationWallMs = performance.now() - creationWallStarted;
  assert.equal(created.ok, true, created.error);
  const dispatches = [];
  let actionDigest;
  try {
    for (let sample = 0; sample < samplesPerRound; ++sample) {
      for (const event of [
        { kind: "seek", frame: 0 },
        { kind: "advance" },
        { kind: "tick", timestamp: 0.125 },
      ]) {
        const setup = candidate.adapter.dispatch(created.player, event);
        assert.equal(setup.ok, true, setup.error);
      }
      const wallStarted = performance.now();
      const result = candidate.adapter.dispatch(created.player,
        { kind: "tick", timestamp: 50.125 });
      const adapterWallMs = performance.now() - wallStarted;
      assert.equal(result.ok, true, result.error);
      const hostStarted = performance.now();
      const action = candidate.selection
        ? materialize(animation, result.action)
        : result.action;
      const hostMaterializeMs = performance.now() - hostStarted;
      const digest = sha256(JSON.stringify(action));
      if (actionDigest === undefined) actionDigest = digest;
      else assert.equal(digest, actionDigest);
      dispatches.push({
        round,
        sample,
        adapterWallMs,
        hostMaterializeMs,
        wallIncludingMaterializeMs: adapterWallMs + hostMaterializeMs,
        ...result.timings,
        scratchBytes: result.memory.scratchBytes,
        scratchAllocationCalls: result.memory.scratchAllocationCalls,
        peakFrontier: result.memory.peakFrontier,
        postRewindFrontier: result.memory.postRewindFrontier,
      });
    }
  } finally {
    candidate.adapter.disposePlayer(created.player);
  }
  return {
    creation: {
      round,
      wallMs: creationWallMs,
      ...created.timings,
      residentBytes: candidate.selection
        ? created.memory.selectionBytes
        : created.memory.animationBytes,
      persistentAllocationCalls: created.memory.persistentAllocationCalls,
      persistentCheckpoint: created.memory.persistentCheckpoint,
      pagesAfter: created.memory.pagesAfter,
    },
    dispatches,
    actionDigest,
  };
}

const [v3, v4, examples] = await Promise.all([
  loadPackage(v3Root, false),
  loadPackage(v4Root, true),
  readExamples(),
]);
const candidates = { v3, v4 };
const titles = ["Pause-driven slide show", "Morphing arrows and final loop"];
const workloads = [];
for (const title of titles) {
  const example = examples.find((candidate) => candidate.title === title);
  assert.ok(example, `missing dashboard example ${title}`);
  const animation = example.data;

  for (const candidate of [v3, v4]) {
    const warmup = runCandidate(candidate, animation, -1);
    assert.equal(warmup.dispatches.length, samplesPerRound);
  }

  const raw = { v3: { creation: [], dispatches: [] },
    v4: { creation: [], dispatches: [] } };
  const digests = { v3: undefined, v4: undefined };
  for (let round = 0; round < rounds; ++round) {
    const order = round % 2 === 0 ? ["v3", "v4"] : ["v4", "v3"];
    for (const name of order) {
      const result = runCandidate(candidates[name], animation, round);
      raw[name].creation.push(result.creation);
      raw[name].dispatches.push(...result.dispatches);
      digests[name] = result.actionDigest;
    }
  }
  assert.equal(digests.v4, digests.v3,
    `${title}: host-materialized v4 action differs from v3`);

  const summarizeCandidate = (name) => {
    const creation = raw[name].creation;
    const dispatches = raw[name].dispatches;
    return {
      creation: summarizeRecords(creation, [
        "wallMs", "projectMs",
        name === "v4" ? "selectionEncodeMs" : "animationEncodeMs",
        "executeMs", "decodeMs", "rewindMs", "totalMs", "overheadMs",
        "residentBytes", "persistentAllocationCalls", "pagesAfter",
      ]),
      dispatch: summarizeRecords(dispatches, [
        "adapterWallMs", "hostMaterializeMs", "wallIncludingMaterializeMs",
        "encodeMs", "executeMs", "decodeMs", "rewindMs", "totalMs",
        "overheadMs", "scratchBytes", "scratchAllocationCalls",
      ]),
    };
  };

  workloads.push({
    title,
    browserAnimationBytes: Buffer.byteLength(JSON.stringify(animation)),
    projectedInputBytes: {
      v3: Buffer.byteLength(JSON.stringify(v3Projection(animation))),
      v4: Buffer.byteLength(JSON.stringify(v4Projection(animation))),
    },
    actionDigest: digests.v3,
    summary: { v3: summarizeCandidate("v3"), v4: summarizeCandidate("v4") },
    raw,
  });
}

const report = {
  schema: "fir.illuminate-selection-player.benchmark/v1",
  generatedAt: new Date().toISOString(),
  policy: {
    warmupRounds: 1,
    measuredRounds: rounds,
    samplesPerRound,
    orderBalanced: true,
    profilerAttached: false,
  },
  environment: {
    node: process.version,
    v8: process.versions.v8,
    platform: process.platform,
    arch: process.arch,
    cpu: os.cpus()[0]?.model ?? "unknown",
  },
  packages: { v3: v3.identity, v4: v4.identity },
  workloads,
};
const output = path.join(directory, "_build/illuminate-selection-benchmark.json");
await writeFile(output, `${JSON.stringify(report, null, 2)}\n`);

for (const workload of workloads) {
  const v3Create = workload.summary.v3.creation;
  const v4Create = workload.summary.v4.creation;
  const v3Dispatch = workload.summary.v3.dispatch;
  const v4Dispatch = workload.summary.v4.dispatch;
  console.log(workload.title);
  console.log(`  projected bytes: ${workload.projectedInputBytes.v3} -> ` +
    `${workload.projectedInputBytes.v4}`);
  console.log(`  create median: ${v3Create.wallMs.median.toFixed(3)} -> ` +
    `${v4Create.wallMs.median.toFixed(3)} ms`);
  console.log(`  resident bytes: ${v3Create.residentBytes.median} -> ` +
    `${v4Create.residentBytes.median}`);
  console.log(`  dispatch+materialize median: ` +
    `${v3Dispatch.wallIncludingMaterializeMs.median.toFixed(4)} -> ` +
    `${v4Dispatch.wallIncludingMaterializeMs.median.toFixed(4)} ms`);
}
console.log(`wrote ${output}`);
