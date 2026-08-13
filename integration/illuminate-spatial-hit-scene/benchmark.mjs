import assert from "node:assert/strict";
import { mkdir, readFile, realpath, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const directory = path.dirname(fileURLToPath(import.meta.url));
const referenceRoot = await realpath(process.env.FIR_REFERENCE_HIT_SCENE_DIR ??
  path.join(directory, "../illuminate-hit-scene/_build/illuminate-hit-scene-current"));
const spatialRoot = await realpath(process.env.FIR_SPATIAL_HIT_SCENE_DIR ??
  path.join(directory, "_build/illuminate-spatial-hit-scene-current"));
const rounds = Number(process.env.FIR_HIT_SCENE_BENCHMARK_ROUNDS ?? 9);
const warmups = Number(process.env.FIR_HIT_SCENE_BENCHMARK_WARMUPS ?? 3);
assert(Number.isSafeInteger(rounds) && rounds >= 7, "at least seven rounds required");
assert(Number.isSafeInteger(warmups) && warmups >= 1, "at least one warmup required");

const bitsView = new DataView(new ArrayBuffer(8));
function fromBits(bits) {
  bitsView.setBigUint64(0, BigInt(bits), true);
  return bitsView.getFloat64(0, true);
}

function sameResult(actual, expected) {
  return actual.kind === expected.kind &&
    (actual.kind !== "tag" ||
      (actual.value === expected.value && actual.label === expected.label));
}

function median(values) {
  const sorted = [...values].sort((a, b) => a - b);
  const middle = Math.floor(sorted.length / 2);
  return sorted.length % 2 === 0
    ? (sorted[middle - 1] + sorted[middle]) / 2
    : sorted[middle];
}

function p95(values) {
  const sorted = [...values].sort((a, b) => a - b);
  return sorted[Math.ceil(0.95 * sorted.length) - 1];
}

function summarize(values) {
  const center = median(values);
  return {
    median: center,
    p95: p95(values),
    mad: median(values.map((value) => Math.abs(value - center))),
    minimum: Math.min(...values),
    maximum: Math.max(...values),
  };
}

async function loadAdapter(root, kind) {
  const prefix = kind === "reference"
    ? "illuminate-hit-scene" : "illuminate-spatial-hit-scene";
  const module = await import(pathToFileURL(
    path.join(root, `${prefix}-browser-adapter.mjs`)));
  const create = kind === "reference"
    ? module.createIlluminateHitSceneAdapter
    : module.createIlluminateSpatialHitSceneAdapter;
  const [bytes, build] = await Promise.all([
    readFile(path.join(root, `${prefix}.wasm`)),
    readFile(path.join(root, "BUILD.json"), "utf8").then(JSON.parse),
  ]);
  return {
    adapter: await create({ bytes, build }),
    build,
    wasmBytes: bytes.byteLength,
  };
}

const suite = JSON.parse(await readFile(
  path.join(spatialRoot, "hit-scene-benchmark-suite.json"), "utf8"));
assert.equal(suite.schemaVersion, "illuminate.hit-scene-benchmark-suite/v1");
const backends = {
  reference: await loadAdapter(referenceRoot, "reference"),
  spatial: await loadAdapter(spatialRoot, "spatial"),
};

function runBackend(name) {
  const { adapter } = backends[name];
  let creationMs = 0;
  let projectMs = 0;
  let encodeMs = 0;
  let prepareMs = 0;
  let residentBytes = 0;
  let queryCount = 0;
  const scenes = [];
  for (const fixture of suite.fixtures) {
    const created = adapter.createHitScene(fixture.encodedScene);
    creationMs += created.timings.totalMs;
    projectMs += created.timings.parseProjectMs;
    encodeMs += created.timings.encodeMs;
    prepareMs += created.timings.prepareMs ?? 0;
    residentBytes += created.memory.persistentBytes ??
      created.memory.persistentCheckpoint - created.memory.reservedFrontier;
    scenes.push({ fixture, scene: created.scene });
  }
  const started = performance.now();
  for (const { fixture, scene } of scenes) {
    for (const query of fixture.queries) {
      const actual = adapter.hitTest(scene,
        fromBits(query.xBits), fromBits(query.yBits));
      assert(sameResult(actual, query.expected),
        `${name}/${fixture.name}/${query.name} disagreed with the oracle`);
      queryCount += 1;
    }
  }
  const queryMs = performance.now() - started;
  for (const { scene } of scenes) adapter.disposeHitScene(scene);
  assert.equal(queryCount, 1_009);
  return {
    creationMs,
    projectMs,
    encodeMs,
    prepareMs,
    queryMs,
    nsPerQuery: queryMs * 1e6 / queryCount,
    queryCount,
    residentBytes,
  };
}

for (let index = 0; index < warmups; ++index) {
  for (const name of index % 2 === 0
      ? ["reference", "spatial"] : ["spatial", "reference"]) {
    runBackend(name);
  }
}

const raw = [];
for (let index = 0; index < rounds; ++index) {
  const order = index % 2 === 0
    ? ["reference", "spatial"] : ["spatial", "reference"];
  const samples = {};
  for (const name of order) samples[name] = runBackend(name);
  raw.push({ round: index + 1, order, ...samples,
    queryDeltaMs: samples.spatial.queryMs - samples.reference.queryMs,
    creationDeltaMs: samples.spatial.creationMs - samples.reference.creationMs });
}

const metrics = ["creationMs", "projectMs", "encodeMs", "prepareMs",
  "queryMs", "nsPerQuery", "residentBytes"];
const summary = Object.fromEntries(["reference", "spatial"].map((name) =>
  [name, Object.fromEntries(metrics.map((metric) =>
    [metric, summarize(raw.map((sample) => sample[name][metric]))]))]));
summary.paired = {
  queryDeltaMs: summarize(raw.map(({ queryDeltaMs }) => queryDeltaMs)),
  creationDeltaMs: summarize(raw.map(({ creationDeltaMs }) => creationDeltaMs)),
};

const report = {
  schemaVersion: "fir.illuminate-spatial-hit-scene.benchmark/v1",
  rounds,
  warmups,
  queryCountPerRound: 1_009,
  source: { referenceRoot, spatialRoot },
  artifacts: {
    reference: {
      wasmBytes: backends.reference.wasmBytes,
      wasmSha256: backends.reference.build.wasm.sha256,
    },
    spatial: {
      wasmBytes: backends.spatial.wasmBytes,
      wasmSha256: backends.spatial.build.wasm.sha256,
    },
  },
  summary,
  raw,
};
await mkdir(path.join(directory, "_build"), { recursive: true });
const output = path.join(directory, "_build/spatial-benchmark.json");
await writeFile(output, `${JSON.stringify(report, null, 2)}\n`);
console.log(JSON.stringify({
  output,
  rounds,
  warmups,
  queryCountPerRound: report.queryCountPerRound,
  artifacts: report.artifacts,
  summary: report.summary,
}, null, 2));
