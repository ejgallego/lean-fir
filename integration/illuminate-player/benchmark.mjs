import assert from "node:assert/strict";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { pathToFileURL } from "node:url";

const rounds = Number.parseInt(process.env.ILLUMINATE_BENCH_ROUNDS ?? "8", 10);
const warmups = Number.parseInt(process.env.ILLUMINATE_BENCH_WARMUPS ?? "1", 10);
assert.ok(Number.isSafeInteger(rounds) && rounds >= 7,
  "ILLUMINATE_BENCH_ROUNDS must be at least seven");
assert.ok(Number.isSafeInteger(warmups) && warmups >= 1,
  "ILLUMINATE_BENCH_WARMUPS must be positive");

const directory = path.dirname(new URL(import.meta.url).pathname);
const illuminateRoot = path.resolve(process.env.ILLUMINATE_ROOT ??
  path.join(directory, ".illuminate"));
const oldRoot = path.resolve(process.env.ILLUMINATE_OLD_PLAYER_DIR ??
  path.join(illuminateRoot, "native-player"));
const newRoot = path.resolve(process.env.ILLUMINATE_NEW_PLAYER_DIR ??
  path.join(directory, "_build/illuminate-player-current"));
const dashboardPath = path.resolve(process.env.ILLUMINATE_DASHBOARD_HTML ??
  path.join(illuminateRoot, "test_output/anim-comparison.html"));
const outputPath = path.resolve(process.env.ILLUMINATE_BENCH_OUTPUT ??
  path.join(directory, "_build/illuminate-player-benchmark.json"));

function dashboardExamples(source) {
  const prefix = "var examples = ";
  const suffix = ";\n    var runtimeUrl";
  const start = source.indexOf(prefix);
  assert.notEqual(start, -1, "dashboard example marker is absent");
  const valueStart = start + prefix.length;
  const end = source.indexOf(suffix, valueStart);
  assert.notEqual(end, -1, "dashboard example terminator is absent");
  return JSON.parse(source.slice(valueStart, end));
}

function eventsFor(animation) {
  const finalFrame = Math.max(0, animation.totalFrames - 1);
  const middle = Math.floor(finalFrame / 2);
  const frameMs = 1000 / animation.fps;
  return [
    { kind: "pause" },
    { kind: "playTo", frame: middle, loopAfter: true },
    { kind: "tick", timestamp: 0.125 },
    { kind: "tick", timestamp: 3.5 * frameMs + 0.125 },
    { kind: "loopAt", frame: middle },
    { kind: "advance" },
    { kind: "seek", frame: finalFrame },
  ];
}

async function loadPackage(root, label) {
  const [bytes, manifest, build, adapter] = await Promise.all([
    readFile(path.join(root, "illuminate-player.wasm")),
    readFile(path.join(root, "illuminate-player.wasm.json"), "utf8")
      .then(JSON.parse),
    readFile(path.join(root, "BUILD.json"), "utf8").then(JSON.parse),
    import(pathToFileURL(path.join(root,
      "illuminate-player-browser-adapter.mjs")).href),
  ]);
  const module = new WebAssembly.Module(bytes);
  const imports = WebAssembly.Module.imports(module);
  const exports = WebAssembly.Module.exports(module);
  return {
    label,
    root,
    bytes,
    manifest,
    build,
    create: adapter.createIlluminatePlayerAdapter,
    artifact: {
      sourceEntry: build.entries?.map(({ sourceName }) => sourceName) ??
        build.entry.sourceName,
      completeWasmBytes: bytes.byteLength,
      completeWasmSha256: build.wasm.sha256,
      baseWasmBytes: build.wasm.base?.byteLength ?? null,
      baseWasmSha256: build.wasm.base?.sha256 ?? null,
      sourceDeclarations: build.runtime.sourceDeclarationCount,
      residentHelpers: build.runtime.residentHelperCount,
      functionImports: imports.filter(({ kind }) => kind === "function").length,
      memoryImports: imports.filter(({ kind }) => kind === "memory").length,
      functionExports: exports.filter(({ kind }) => kind === "function")
        .map(({ name }) => name),
      memoryExports: exports.filter(({ kind }) => kind === "memory")
        .map(({ name }) => name),
    },
  };
}

async function freshAdapter(package_) {
  return package_.create({
    bytes: package_.bytes,
    manifest: package_.manifest,
    build: package_.build,
  });
}

async function runOne(package_, example, events) {
  const adapter = await freshAdapter(package_);
  const result = adapter.replayTrace(example.data, events);
  assert.equal(result.ok, true, `${package_.label}/${example.title}: ${result.error}`);
  const memory = result.memory;
  const creation = result.timings.creation;
  const dispatches = result.timings.dispatches ?? [];
  const sum = (field) => dispatches.reduce((total, timing) =>
    total + (timing[field] ?? 0), 0);
  return {
    actions: result.actions,
    sample: {
      projectMs: creation?.projectMs ?? result.timings.projectMs ?? null,
      encodeMs: creation === undefined ? result.timings.encodeMs ?? null :
        creation.animationEncodeMs + sum("encodeMs"),
      prepareMs: result.timings.prepareMs ?? null,
      executeMs: creation === undefined ? result.timings.executeMs :
        creation.executeMs + sum("executeMs"),
      decodeMs: creation === undefined ? result.timings.decodeMs :
        creation.decodeMs + sum("decodeMs"),
      rewindMs: creation === undefined ? null :
        creation.rewindMs + sum("rewindMs"),
      totalMs: result.timings.totalMs,
      overheadMs: result.timings.overheadMs ?? null,
      inputBytes: memory.creation?.animationBytes ?? memory.inputBytes,
      persistentBytes: memory.creation === undefined ? null :
        memory.persistentCheckpoint - memory.creation.frontierBefore,
      scratchPeakBytes: memory.creation === undefined ? null :
        memory.peakFrontier - memory.persistentCheckpoint,
      postRewindFrontier: memory.postRewindFrontier ?? null,
      frontierGrowthPrepare: memory.frontierGrowthPrepare ??
        (memory.frontierAfterPrepare === undefined ? null :
          memory.frontierAfterPrepare - memory.frontierBefore),
      frontierGrowthExecute: memory.frontierGrowthExecute ??
        (memory.frontierAfterExecute === undefined ? null :
          memory.frontierAfterExecute - memory.frontierBeforeExecute),
      frontierGrowthTotal: memory.frontierGrowthTotal ??
        (memory.frontierAfterDecode === undefined ? null :
          memory.frontierAfterDecode - memory.frontierBefore),
    },
  };
}

function median(values) {
  const sorted = [...values].sort((left, right) => left - right);
  const middle = Math.floor(sorted.length / 2);
  return sorted.length % 2 === 0
    ? (sorted[middle - 1] + sorted[middle]) / 2
    : sorted[middle];
}

function distribution(values) {
  if (values.length === 0) return null;
  const center = median(values);
  return {
    count: values.length,
    median: center,
    mad: median(values.map((value) => Math.abs(value - center))),
    minimum: Math.min(...values),
    maximum: Math.max(...values),
  };
}

const metrics = ["projectMs", "encodeMs", "prepareMs", "executeMs",
  "decodeMs", "rewindMs", "totalMs", "overheadMs", "inputBytes",
  "persistentBytes", "scratchPeakBytes", "postRewindFrontier",
  "frontierGrowthPrepare", "frontierGrowthExecute", "frontierGrowthTotal"];

function summarize(samples) {
  return Object.fromEntries(metrics.map((metric) => [metric,
    distribution(samples.map((sample) => sample[metric])
      .filter((value) => value !== null))]));
}

const examples = dashboardExamples(await readFile(dashboardPath, "utf8"));
assert.ok(examples.length > 0, "dashboard benchmark corpus is empty");
const oldPackage = await loadPackage(oldRoot, "old");
const newPackage = await loadPackage(newRoot, "new");
const packages = { old: oldPackage, new: newPackage };

for (const example of examples) {
  const events = eventsFor(example.data);
  for (let warmup = 0; warmup < warmups; warmup += 1) {
    const order = warmup % 2 === 0 ? [oldPackage, newPackage] :
      [newPackage, oldPackage];
    const results = [];
    for (const package_ of order) results.push(await runOne(package_, example, events));
    assert.deepEqual(results[0].actions, results[1].actions,
      `${example.title}: warmup outputs differ`);
  }
}

const raw = [];
for (let round = 0; round < rounds; round += 1) {
  const order = round % 2 === 0 ? ["old", "new"] : ["new", "old"];
  for (const [exampleIndex, example] of examples.entries()) {
    const events = eventsFor(example.data);
    const results = {};
    for (const [position, label] of order.entries()) {
      const result = await runOne(packages[label], example, events);
      results[label] = result;
      raw.push({ round, position, engine: label, exampleIndex,
        example: example.title, ...result.sample });
    }
    assert.deepEqual(results.old.actions, results.new.actions,
      `${example.title}: measured outputs differ`);
  }
}

const byEngine = Object.fromEntries(["old", "new"].map((engine) => [engine,
  summarize(raw.filter((sample) => sample.engine === engine))]));
const byExample = examples.map((example, exampleIndex) => ({
  exampleIndex,
  example: example.title,
  old: summarize(raw.filter((sample) =>
    sample.engine === "old" && sample.exampleIndex === exampleIndex)),
  new: summarize(raw.filter((sample) =>
    sample.engine === "new" && sample.exampleIndex === exampleIndex)),
}));
const report = {
  schemaVersion: "fir.illuminate-player.benchmark/v1",
  protocol: {
    corpus: "all examples embedded in Illuminate test_output/anim-comparison.html",
    examples: examples.length,
    eventsPerExample: 7,
    rounds,
    warmups,
    order: "old/new on even rounds; new/old on odd rounds",
    ownership: "fresh Wasm instance for every replay sample",
    profiler: false,
  },
  packages: {
    old: oldPackage.artifact,
    new: newPackage.artifact,
  },
  summary: { byEngine, byExample },
  raw,
};
await writeFile(outputPath, `${JSON.stringify(report, null, 2)}\n`);
console.log(JSON.stringify({ ok: true, outputPath, examples: examples.length,
  rounds, samples: raw.length, byEngine }));
