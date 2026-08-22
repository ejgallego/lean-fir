import assert from "node:assert/strict";
import {
  existsSync,
  mkdirSync,
  readFileSync,
  renameSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { basename, dirname, resolve } from "node:path";

import {
  profileEvidenceSchema,
  profileFunctionFamily,
  summarizeCpuProfile,
} from "./node-profile-lib.mjs";
import {
  sha256,
  validateSidecar,
} from "../wasm/function-index-lib.mjs";

export const profileAggregateSchema = "fir.sampled-profile-aggregate/v2";

function json(bytes, label) {
  try {
    return JSON.parse(bytes);
  } catch (error) {
    throw new Error(`${label} is not valid JSON: ${error.message}`);
  }
}

function descriptorMatches(bytes, descriptor, label) {
  assert(descriptor !== null && typeof descriptor === "object",
    `${label} has no identity descriptor`);
  assert.equal(descriptor.byteLength, bytes.length,
    `${label} byte length does not match its descriptor`);
  assert.equal(descriptor.sha256, sha256(bytes),
    `${label} SHA-256 does not match its descriptor`);
}

function median(values) {
  assert(values.length !== 0, "cannot summarize an empty value set");
  const ordered = [...values].sort((left, right) => left - right);
  const middle = Math.floor(ordered.length / 2);
  return ordered.length % 2 === 0 ?
    (ordered[middle - 1] + ordered[middle]) / 2 : ordered[middle];
}

function statistics(values) {
  assert(values.every(Number.isFinite), "summary values must be finite");
  const center = median(values);
  return {
    median: center,
    mad: median(values.map((value) => Math.abs(value - center))),
    min: Math.min(...values),
    max: Math.max(...values),
    span: Math.max(...values) - Math.min(...values),
  };
}

function rawProfilePath(evidencePath, evidence) {
  const file = evidence.rawProfile?.file;
  assert.equal(typeof file, "string", "profile evidence has no raw profile file");
  assert.equal(file, basename(file),
    "raw profile file must be a sibling filename, not a path");
  return resolve(dirname(evidencePath), file);
}

function summarizeRun(profile, sidecar, options, label) {
  const summary = summarizeCpuProfile(profile, sidecar, {
    ...options,
    strictFunctionIndices: true,
  });
  assert.equal(summary.unresolvedWasmSamples, 0,
    `${label} contains unresolved Wasm samples`);
  assert(summary.resolvedWasmSamples > 0,
    `${label} contains no Wasm self samples`);
  const functions = new Map(summary.functions.map((function_) =>
    [function_.index, function_]));
  const ranked = summary.functions.filter(({ selfSamples }) => selfSamples > 0)
    .sort((left, right) => right.selfSamples - left.selfSamples ||
      right.selfMicros - left.selfMicros || left.index - right.index);
  const ranks = new Map(ranked.map(({ index }, index_) => [index, index_ + 1]));
  const callerEdges = new Map();
  for (const edge of summary.callerEdges) {
    const target = callerEdges.get(edge.targetIndex) ?? new Map();
    const identity = JSON.stringify([
      edge.caller.kind,
      edge.caller.index,
      edge.caller.name,
      edge.caller.url,
    ]);
    assert.equal(target.has(identity), false,
      "CPU profile summary contains a duplicate caller edge");
    target.set(identity, edge);
    callerEdges.set(edge.targetIndex, target);
  }
  assert.equal(summary.callerAttribution.attributedWasmSelfSamples,
    summary.resolvedWasmSamples + summary.unresolvedWasmSamples,
    `${label} does not attribute every Wasm self sample to a caller edge`);
  return { summary, functions, ranks, callerEdges };
}

function loadRun(evidencePath, runIndex, artifact, functionSidecar,
  sidecar) {
  const resolvedEvidence = resolve(evidencePath);
  const evidenceBytes = readFileSync(resolvedEvidence);
  const evidence = json(evidenceBytes, `profile evidence ${resolvedEvidence}`);
  assert.equal(evidence.schemaVersion, profileEvidenceSchema,
    `unsupported profile evidence schema ${evidence.schemaVersion}`);
  assert.equal(evidence.evidenceClass, "sampled-profile",
    "input evidence is not a sampled profile");
  assert.equal(evidence.artifact?.sha256, artifact.sha256,
    "profile evidence was collected from a different Wasm artifact");
  assert.equal(evidence.artifact?.byteLength, artifact.byteLength,
    "profile evidence Wasm byte length does not match");
  assert.equal(evidence.functionSidecar?.sha256, functionSidecar.sha256,
    "profile evidence was resolved with a different function sidecar");
  assert.equal(evidence.functionSidecar?.byteLength,
    functionSidecar.byteLength,
    "profile evidence function-sidecar byte length does not match");
  assert.equal(evidence.functionSidecar?.artifactSha256, artifact.sha256,
    "profile evidence sidecar is not bound to the selected Wasm artifact");
  assert.equal(evidence.functionSidecar?.schemaVersion,
    sidecar.schemaVersion,
    "profile evidence sidecar schema does not match");

  const rawPath = rawProfilePath(resolvedEvidence, evidence);
  const rawBytes = readFileSync(rawPath);
  descriptorMatches(rawBytes, evidence.rawProfile, "raw CPU profile");
  const profile = json(rawBytes, `raw CPU profile ${rawPath}`);
  const window = evidence.summary?.window;
  assert.equal(window?.method, "phase-overlap-time-deltas/v1",
    "profile evidence has an unsupported attribution window");
  assert(Number.isFinite(window.startMicros) && window.startMicros >= 0,
    "profile evidence has an invalid attribution-window start");
  const durationMicros = window.durationMicros === null ?
    Number.POSITIVE_INFINITY : window.durationMicros;
  assert((Number.isFinite(durationMicros) && durationMicros >= 0) ||
    durationMicros === Number.POSITIVE_INFINITY,
    "profile evidence has an invalid attribution-window duration");
  const { summary, functions, ranks, callerEdges } = summarizeRun(
    profile, sidecar, {
    startMicros: window.startMicros,
    durationMicros,
  }, "exact-release profile attribution window");
  return {
    id: `run-${runIndex + 1}`,
    binding: "exact-release",
    evidence: {
      file: basename(resolvedEvidence),
      byteLength: evidenceBytes.length,
      sha256: sha256(evidenceBytes),
    },
    rawProfile: {
      file: basename(rawPath),
      byteLength: rawBytes.length,
      sha256: sha256(rawBytes),
    },
    workload: evidence.workload,
    runtime: evidence.runtime,
    observations: evidence.observations,
    window: summary.window,
    wasmSelfSamples: summary.resolvedWasmSamples,
    wasmSelfMicros: summary.resolvedWasmMicros,
    hostSamples: summary.hostSamples,
    hostMicros: summary.hostMicros,
    callerAttribution: summary.callerAttribution,
    functions,
    ranks,
    callerEdges,
  };
}

function loadUnboundRun(profilePath, runIndex, sidecar) {
  const resolvedProfile = resolve(profilePath);
  const rawBytes = readFileSync(resolvedProfile);
  const profile = json(rawBytes, `raw CPU profile ${resolvedProfile}`);
  const { summary, functions, ranks, callerEdges } = summarizeRun(
    profile, sidecar, {}, "raw profile");
  return {
    id: `run-${runIndex + 1}`,
    binding: "unbound-raw-profile",
    evidence: null,
    rawProfile: {
      file: basename(resolvedProfile),
      byteLength: rawBytes.length,
      sha256: sha256(rawBytes),
    },
    workload: null,
    runtime: null,
    observations: null,
    window: summary.window,
    wasmSelfSamples: summary.resolvedWasmSamples,
    wasmSelfMicros: summary.resolvedWasmMicros,
    hostSamples: summary.hostSamples,
    hostMicros: summary.hostMicros,
    callerAttribution: summary.callerAttribution,
    functions,
    ranks,
    callerEdges,
  };
}

export function aggregateProfileEvidence({
  wasmPath,
  sidecarPath,
  evidencePaths = [],
  profilePaths = [],
}) {
  assert(Array.isArray(evidencePaths), "evidence paths must be an array");
  assert(Array.isArray(profilePaths), "raw profile paths must be an array");
  assert(evidencePaths.length + profilePaths.length !== 0,
    "at least one sampled-profile evidence file or raw profile is required");
  const resolvedEvidence = evidencePaths.map((path) => resolve(path));
  const resolvedProfiles = profilePaths.map((path) => resolve(path));
  const allInputs = [...resolvedEvidence, ...resolvedProfiles];
  assert.equal(new Set(allInputs).size, allInputs.length,
    "sampled-profile input paths must be unique");
  const resolvedWasm = resolve(wasmPath);
  const resolvedSidecar = resolve(sidecarPath);
  const wasmBytes = readFileSync(resolvedWasm);
  const sidecarBytes = readFileSync(resolvedSidecar);
  const sidecar = json(sidecarBytes, `function sidecar ${resolvedSidecar}`);
  validateSidecar(wasmBytes, sidecar);
  const artifact = {
    file: basename(resolvedWasm),
    byteLength: wasmBytes.length,
    sha256: sha256(wasmBytes),
  };
  const functionSidecar = {
    file: basename(resolvedSidecar),
    byteLength: sidecarBytes.length,
    sha256: sha256(sidecarBytes),
    schemaVersion: sidecar.schemaVersion,
    artifactSha256: sidecar.artifact.sha256,
  };
  const runs = [
    ...resolvedEvidence.map((path, index) =>
      loadRun(path, index, artifact, functionSidecar, sidecar)),
    ...resolvedProfiles.map((path, index) =>
      loadUnboundRun(path, index + resolvedEvidence.length, sidecar)),
  ];
  const sampledIndices = new Set(runs.flatMap(({ functions }) =>
    [...functions.keys()]));
  const functions = [...sampledIndices].map((index) => {
    const function_ = sidecar.functions[index];
    const perRun = runs.map((run) => {
      const sample = run.functions.get(index);
      const selfSamples = sample?.selfSamples ?? 0;
      return {
        run: run.id,
        selfSamples,
        selfMicros: sample?.selfMicros ?? 0,
        wasmSelfShare: selfSamples / run.wasmSelfSamples,
        rank: run.ranks.get(index) ?? null,
      };
    });
    const ranks = perRun.flatMap(({ rank }) => rank === null ? [] : [rank]);
    const rank = statistics(ranks);
    const callerIdentities = new Set(runs.flatMap((run) =>
      [...(run.callerEdges.get(index)?.keys() ?? [])]));
    const callers = [...callerIdentities].map((identity) => {
      const descriptor = runs.map((run) =>
        run.callerEdges.get(index)?.get(identity)?.caller).find(Boolean);
      assert(descriptor !== undefined,
        "caller identity has no descriptor in any input run");
      const callerPerRun = runs.map((run) => {
        const edge = run.callerEdges.get(index)?.get(identity);
        const targetSelfSamples = run.functions.get(index)?.selfSamples ?? 0;
        return {
          run: run.id,
          selfSamples: edge?.selfSamples ?? 0,
          selfMicros: edge?.selfMicros ?? 0,
          wasmSelfShare: (edge?.selfSamples ?? 0) / run.wasmSelfSamples,
          targetSelfShare: targetSelfSamples === 0 ? null :
            (edge?.selfSamples ?? 0) / targetSelfSamples,
        };
      });
      const targetShares = callerPerRun.flatMap(({ targetSelfShare }) =>
        targetSelfShare === null ? [] : [targetSelfShare]);
      return {
        ...descriptor,
        perRun: callerPerRun,
        aggregate: {
          selfSamples: statistics(callerPerRun.map(({ selfSamples }) =>
            selfSamples)),
          selfMicros: statistics(callerPerRun.map(({ selfMicros }) =>
            selfMicros)),
          wasmSelfShare: statistics(callerPerRun.map(({ wasmSelfShare }) =>
            wasmSelfShare)),
          targetSelfShare: {
            ...statistics(targetShares),
            targetSampledRuns: targetShares.length,
            edgePresentRuns: callerPerRun.filter(({ selfSamples }) =>
              selfSamples !== 0).length,
          },
        },
      };
    }).sort((left, right) =>
      right.aggregate.wasmSelfShare.median -
        left.aggregate.wasmSelfShare.median ||
      right.aggregate.wasmSelfShare.max - left.aggregate.wasmSelfShare.max ||
      right.aggregate.targetSelfShare.median -
        left.aggregate.targetSelfShare.median ||
      left.kind.localeCompare(right.kind) ||
      (left.index ?? Number.MAX_SAFE_INTEGER) -
        (right.index ?? Number.MAX_SAFE_INTEGER) ||
      String(left.name).localeCompare(String(right.name)));
    return {
      index,
      name: function_.name,
      optimizerName: function_.optimizerName,
      origin: function_.origin,
      family: profileFunctionFamily(function_),
      bodyBytes: function_.bodyBytes,
      perRun,
      callers,
      aggregate: {
        selfSamples: statistics(perRun.map(({ selfSamples }) => selfSamples)),
        selfMicros: statistics(perRun.map(({ selfMicros }) => selfMicros)),
        wasmSelfShare: statistics(perRun.map(({ wasmSelfShare }) =>
          wasmSelfShare)),
        rank: {
          ...rank,
          presentRuns: ranks.length,
        },
      },
    };
  }).sort((left, right) =>
    right.aggregate.wasmSelfShare.median -
      left.aggregate.wasmSelfShare.median ||
    right.aggregate.wasmSelfShare.max - left.aggregate.wasmSelfShare.max ||
    left.index - right.index);
  return {
    schemaVersion: profileAggregateSchema,
    evidenceClass: "sampled-profile-aggregate",
    binding: resolvedProfiles.length === 0 ? "exact-release" :
      "contains-unbound-raw-profiles",
    artifact,
    functionSidecar,
    runCount: runs.length,
    callerAttribution: {
      method: "v8-cpu-profile-parent-edge/v1",
      unit: "sampled-target-self-time",
      caller: "immediate-parent-profile-node",
      coverage: "all-wasm-self-samples",
    },
    runs: runs.map(({ functions: _functions, ranks: _ranks,
      callerEdges: _callerEdges, ...run }) => run),
    functions,
  };
}

export function writeAggregateReport(outputPath, report) {
  const resolvedOutput = resolve(outputPath);
  assert.equal(existsSync(resolvedOutput), false,
    `profile aggregate output already exists: ${resolvedOutput}`);
  mkdirSync(dirname(resolvedOutput), { recursive: true });
  const staging = `${resolvedOutput}.tmp-${process.pid}-${Date.now()}`;
  const bytes = Buffer.from(`${JSON.stringify(report, null, 2)}\n`);
  try {
    writeFileSync(staging, bytes, { flag: "wx" });
    renameSync(staging, resolvedOutput);
  } catch (error) {
    rmSync(staging, { force: true });
    throw error;
  }
  return {
    path: resolvedOutput,
    byteLength: bytes.length,
    sha256: sha256(bytes),
  };
}
