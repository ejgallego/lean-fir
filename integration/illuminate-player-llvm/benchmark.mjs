import assert from "node:assert/strict";
import { writeFile } from "node:fs/promises";
import { pathToFileURL } from "node:url";

import {
  loadEmscriptenIlluminateSelectionPlayerAdapter,
} from "./illuminate-selection-player-emscripten-adapter.mjs";

function parseNatural(value, label) {
  const parsed = Number(value);
  if (!Number.isSafeInteger(parsed) || parsed <= 0) {
    throw new Error(`${label} must be a positive safe integer`);
  }
  return parsed;
}

const options = {
  warmups: 2,
  rounds: 9,
  events: 1_000,
  out: undefined,
  manifest: undefined,
};
for (const argument of process.argv.slice(2)) {
  const [name, value] = argument.split("=", 2);
  switch (name) {
    case "--warmups":
      options.warmups = parseNatural(value, name);
      break;
    case "--rounds":
      options.rounds = parseNatural(value, name);
      break;
    case "--events":
      options.events = parseNatural(value, name);
      break;
    case "--out":
      options.out = value;
      break;
    case "--manifest":
      options.manifest = value;
      break;
    default:
      throw new Error(`unknown argument ${argument}`);
  }
}
if (options.rounds < 7) throw new Error("headline benchmark requires at least seven measured rounds");

const manifestUrl = options.manifest === undefined
  ? new URL("./illuminate-selection-player.manifest.json", import.meta.url)
  : pathToFileURL(options.manifest);
const adapter = await loadEmscriptenIlluminateSelectionPlayerAdapter(manifestUrl);

const animation = {
  fps: 60,
  totalFrames: 360,
  segments: [
    { sf: 0, fc: 120, sync: "host-only-a", pmap: [], params: [] },
    { sf: 120, fc: 120, sync: "host-only-b", pmap: [], params: [] },
    { sf: 240, fc: 120, sync: "host-only-c", pmap: [], params: [] },
  ],
  steps: [
    { frame: 0, pause: false, loop: false },
    { frame: 120, pause: false, loop: true },
    { frame: 240, pause: false, loop: false },
  ],
};

function quantile(sorted, fraction) {
  if (sorted.length === 0) return 0;
  return sorted[Math.min(sorted.length - 1, Math.ceil(sorted.length * fraction) - 1)];
}

function summarize(values) {
  const sorted = [...values].sort((left, right) => left - right);
  const median = quantile(sorted, 0.5);
  const deviations = sorted.map((value) => Math.abs(value - median)).sort((left, right) => left - right);
  return {
    count: values.length,
    median,
    p95: quantile(sorted, 0.95),
    mad: quantile(deviations, 0.5),
    minimum: sorted[0] ?? 0,
    maximum: sorted.at(-1) ?? 0,
  };
}

function requireResult(result, label) {
  assert.equal(result.ok, true, `${label}: ${result.error ?? "unknown error"}`);
  return result;
}

function runCandidate(kind, timestamps) {
  const created = requireResult(adapter.createPlayer(animation), `${kind} create`);
  requireResult(adapter.dispatch(created.player, { kind: "advance" }), `${kind} advance`);
  const actions = [];
  const samples = [];
  let memory = created.memory;
  try {
    for (const timestamp of timestamps) {
      const outerStarted = performance.now();
      const result = requireResult(
        kind === "scalar"
          ? adapter.dispatchTick(created.player, timestamp)
          : adapter.dispatch(created.player, { kind: "tick", timestamp }),
        `${kind} tick`,
      );
      const outerMs = performance.now() - outerStarted;
      memory = result.memory;
      actions.push(result.action);
      samples.push({
        callbackMs: result.timings.totalMs,
        encodeMs: result.timings.encodeMs,
        executeMs: result.timings.executeMs,
        decodeMs: result.timings.decodeMs,
        marshalMs: result.timings.encodeMs + result.timings.decodeMs,
        adapterOverheadMs: result.timings.overheadMs,
        outerOverheadMs: Math.max(0, outerMs - result.timings.totalMs),
      });
    }
    return { actions, samples, memory };
  } finally {
    adapter.disposePlayer(created.player);
  }
}

function candidateSummary(rounds, kind) {
  const samples = rounds.flatMap((round) => round[kind].samples);
  const phases = {};
  for (const phase of [
    "callbackMs",
    "encodeMs",
    "executeMs",
    "decodeMs",
    "marshalMs",
    "adapterOverheadMs",
    "outerOverheadMs",
  ]) {
    phases[phase] = summarize(samples.map((sample) => sample[phase]));
  }
  return phases;
}

const timestamps = Array.from({ length: options.events }, (_, index) => index * 16.25 + 0.125);
const allRounds = [];
for (let index = 0; index < options.warmups + options.rounds; index += 1) {
  const order = index % 2 === 0 ? ["generic", "scalar"] : ["scalar", "generic"];
  const candidates = {};
  for (const kind of order) candidates[kind] = runCandidate(kind, timestamps);
  assert.deepEqual(candidates.scalar.actions, candidates.generic.actions, `round ${index} changed semantics`);
  if (index >= options.warmups) {
    allRounds.push({
      index: index - options.warmups,
      order,
      generic: { samples: candidates.generic.samples, memory: candidates.generic.memory },
      scalar: { samples: candidates.scalar.samples, memory: candidates.scalar.memory },
    });
  }
}

const report = {
  schemaVersion: "fir.illuminate-selection-player.benchmark/v1",
  design: {
    warmups: options.warmups,
    measuredRounds: options.rounds,
    eventsPerCandidate: options.events,
    order: "alternating generic/scalar within each round",
    workload: "fixed non-integer tick timestamps on identical retained players",
    profiler: "none",
  },
  summary: {
    generic: candidateSummary(allRounds, "generic"),
    scalar: candidateSummary(allRounds, "scalar"),
  },
  rounds: allRounds,
};
const json = `${JSON.stringify(report, null, 2)}\n`;
if (options.out !== undefined) await writeFile(options.out, json);
process.stdout.write(json);
