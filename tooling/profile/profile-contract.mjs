import assert from "node:assert/strict";

import {
  makeProfileComparability,
  makeProfileQuality,
  profileEvidenceSchema,
  workloadReceiptSchema,
} from "./node-profile-lib.mjs";
import { profileAggregateSchema } from "./profile-aggregate-lib.mjs";
import { sidecarSchema } from "../wasm/function-index-lib.mjs";

export const profileClaimsSchema = "fir.sampled-profile-claims/v1";

const SHA256 = /^[0-9a-f]{64}$/;

function requireObject(value, label) {
  assert(value !== null && typeof value === "object" && !Array.isArray(value),
    `${label} must be an object`);
  return value;
}

function requireString(value, label) {
  assert.equal(typeof value, "string", `${label} must be a string`);
  assert(value.length !== 0, `${label} must not be empty`);
  return value;
}

function requireInteger(value, label, minimum = 0) {
  assert(Number.isSafeInteger(value) && value >= minimum,
    `${label} must be an integer >= ${minimum}`);
  return value;
}

function requireNumber(value, label) {
  assert(Number.isFinite(value) && value >= 0,
    `${label} must be a nonnegative finite number`);
  return value;
}

function requireSha256(value, label) {
  assert.match(value ?? "", SHA256, `${label} must be a lowercase SHA-256`);
  return value;
}

function descriptor(value, label, { positive = false } = {}) {
  const result = requireObject(value, label);
  requireString(result.file, `${label}.file`);
  requireInteger(result.byteLength, `${label}.byteLength`, positive ? 1 : 0);
  requireSha256(result.sha256, `${label}.sha256`);
  return result;
}

function descriptorList(value, label) {
  assert(Array.isArray(value), `${label} must be an array`);
  const roles = new Set();
  for (const item of value) {
    descriptor(item, `${label} entry`);
    requireString(item.role, `${label} role`);
    assert.equal(roles.has(item.role), false,
      `${label} repeats role ${item.role}`);
    roles.add(item.role);
  }
}

function validateWorkload(workload, label) {
  descriptor(workload, label, { positive: true });
  const receipt = descriptor(workload.receipt, `${label}.receipt`, {
    positive: true,
  });
  assert.equal(receipt.schemaVersion, workloadReceiptSchema,
    `${label}.receipt has an unsupported schema`);
  requireString(receipt.id, `${label}.receipt.id`);
  requireString(receipt.semanticEndpoint,
    `${label}.receipt.semanticEndpoint`);
  requireString(receipt.instancePolicy, `${label}.receipt.instancePolicy`);
  requireObject(receipt.parameters, `${label}.receipt.parameters`);
  descriptorList(workload.dependencies, `${label}.dependencies`);
  descriptorList(workload.inputs, `${label}.inputs`);
  return receipt;
}

function validateRuntime(runtime, label) {
  requireObject(runtime, label);
  for (const field of ["node", "v8", "platform", "arch"]) {
    requireString(runtime[field], `${label}.${field}`);
  }
  requireInteger(runtime.samplingIntervalMicros,
    `${label}.samplingIntervalMicros`, 1);
}

function validateWindow(window, label) {
  requireObject(window, label);
  assert.equal(window.method, "phase-overlap-time-deltas/v1",
    `${label} is not an exact sampled window`);
  requireNumber(window.startMicros, `${label}.startMicros`);
  assert(window.durationMicros === null ||
    (Number.isFinite(window.durationMicros) && window.durationMicros >= 0),
  `${label}.durationMicros must be null or a nonnegative finite number`);
}

function validateProfilePhases(phases, summary) {
  requireObject(phases, "FIR profile phases");
  for (const field of [
    "acquireMs", "setupMs", "firstCallMs", "warmupMs", "profilerStartMs",
    "steadyProfiledMs", "profilerStopMs", "teardownMs", "totalMs",
  ]) {
    requireNumber(phases[field], `FIR profile phases.${field}`);
  }
  assert.equal(summary.window.startMicros, phases.profilerStartMs * 1000,
    "FIR profile window does not start at profiler activation");
  assert.equal(summary.window.durationMicros, phases.steadyProfiledMs * 1000,
    "FIR profile window is not the steady profiled phase");
}

function validateSummary(summary, label) {
  requireObject(summary, label);
  validateWindow(summary.window, `${label}.window`);
  const sampleCount = requireInteger(summary.sampleCount,
    `${label}.sampleCount`);
  const resolved = requireInteger(summary.resolvedWasmSamples,
    `${label}.resolvedWasmSamples`);
  const unresolved = requireInteger(summary.unresolvedWasmSamples,
    `${label}.unresolvedWasmSamples`);
  const host = requireInteger(summary.hostSamples, `${label}.hostSamples`);
  assert.equal(sampleCount, resolved + unresolved + host,
    `${label} sample counts are inconsistent`);
  const resolvedMicros = requireNumber(summary.resolvedWasmMicros,
    `${label}.resolvedWasmMicros`);
  const unresolvedMicros = requireNumber(summary.unresolvedWasmMicros,
    `${label}.unresolvedWasmMicros`);
  const hostMicros = requireNumber(summary.hostMicros, `${label}.hostMicros`);
  assert.equal(unresolved, 0,
    `${label} contains unresolved Wasm samples`);
  assert.equal(unresolvedMicros, 0,
    `${label} contains unresolved Wasm self time`);
  assert.equal(requireNumber(summary.totalSampleMicros,
    `${label}.totalSampleMicros`),
  resolvedMicros + unresolvedMicros + hostMicros,
  `${label} sampled microseconds are inconsistent`);
  assert(resolved > 0, `${label} contains no Wasm self samples`);
  const callers = requireObject(summary.callerAttribution,
    `${label}.callerAttribution`);
  assert.equal(callers.method, "v8-cpu-profile-parent-edge/v1",
    `${label} has unsupported caller attribution`);
  assert.equal(callers.resolvedWasmSelfSamples, resolved,
    `${label} resolved caller count is inconsistent`);
  assert.equal(callers.unresolvedWasmSelfSamples, unresolved,
    `${label} unresolved caller count is inconsistent`);
  assert.equal(callers.attributedWasmSelfSamples, resolved + unresolved,
    `${label} caller attribution is incomplete`);
  return { resolved, host, resolvedMicros, hostMicros };
}

function commonClaims(packet, receipt) {
  return {
    schemaVersion: profileClaimsSchema,
    sourceContract: {
      kind: "source-report-contract",
      id: packet.schemaVersion,
    },
    artifactSha256: packet.artifact.sha256,
    symbolMapSha256: packet.functionSidecar.sha256,
    comparabilityKey: packet.comparability.key,
    qualityClassification: packet.quality.classification,
    workloadReceipt: {
      kind: workloadReceiptSchema,
      id: receipt.id,
      sha256: receipt.sha256,
    },
    instancePolicy: receipt.instancePolicy,
    timeBasis: "sampled-self-time",
    unit: "microseconds",
    window: "steady-only",
    symbolization: {
      kind: "final-wasm-function-index",
      coverage: "all-wasm-self-samples",
    },
  };
}

export function validateProfileEvidenceContract(packet) {
  requireObject(packet, "FIR sampled profile");
  assert.equal(packet.schemaVersion, profileEvidenceSchema,
    "unsupported FIR sampled-profile schema");
  assert.equal(packet.evidenceClass, "sampled-profile",
    "FIR sampled-profile evidence class is invalid");
  const artifact = descriptor(packet.artifact, "FIR profile artifact", {
    positive: true,
  });
  const functionSidecar = descriptor(packet.functionSidecar,
    "FIR profile function sidecar", { positive: true });
  assert.equal(functionSidecar.schemaVersion, sidecarSchema,
    "FIR profile function sidecar has an unsupported schema");
  assert.equal(functionSidecar.artifactSha256, artifact.sha256,
    "FIR profile function sidecar is bound to another artifact");
  const receipt = validateWorkload(packet.workload, "FIR profile workload");
  validateRuntime(packet.runtime, "FIR profile runtime");
  requireObject(packet.observations, "FIR profile observations");
  descriptor(packet.rawProfile, "FIR raw profile", { positive: true });
  const expectedComparability = makeProfileComparability({
    schemaVersion: packet.schemaVersion,
    workload: packet.workload,
    runtime: packet.runtime,
    observations: packet.observations,
  });
  assert.deepEqual(packet.comparability, expectedComparability,
    "FIR profile comparability does not match its packet contents");
  assert.equal(packet.comparability.eligible, true,
    "FIR profile is not comparability-eligible");
  requireSha256(packet.comparability.key,
    "FIR profile comparability key");
  const summary = validateSummary(packet.summary, "FIR profile summary");
  validateProfilePhases(packet.phases, packet.summary);
  assert.deepEqual(packet.quality,
    makeProfileQuality(packet.summary, packet.comparability),
  "FIR profile quality does not match its packet contents");
  assert.equal(packet.quality.metrics.wasmSelfSamples, summary.resolved,
    "FIR profile quality sample count is inconsistent");
  return commonClaims(packet, receipt);
}

function validateAggregateRun(run, label, comparabilityKey) {
  requireObject(run, label);
  requireString(run.id, `${label}.id`);
  assert.equal(run.binding, "exact-release",
    `${label} is not bound to exact-release evidence`);
  descriptor(run.evidence, `${label}.evidence`, { positive: true });
  descriptor(run.rawProfile, `${label}.rawProfile`, { positive: true });
  const receipt = validateWorkload(run.workload, `${label}.workload`);
  validateRuntime(run.runtime, `${label}.runtime`);
  requireObject(run.observations, `${label}.observations`);
  const expectedComparability = makeProfileComparability({
    schemaVersion: profileEvidenceSchema,
    workload: run.workload,
    runtime: run.runtime,
    observations: run.observations,
  });
  assert.deepEqual(run.comparability, expectedComparability,
    `${label} comparability does not match its contents`);
  assert.equal(run.comparability.eligible, true,
    `${label} is not comparability-eligible`);
  assert.equal(run.comparability.key, comparabilityKey,
    `${label} comparability key differs from the aggregate`);
  validateWindow(run.window, `${label}.window`);
  const wasmSelfSamples = requireInteger(run.wasmSelfSamples,
    `${label}.wasmSelfSamples`, 1);
  const hostSamples = requireInteger(run.hostSamples,
    `${label}.hostSamples`);
  const wasmSelfMicros = requireNumber(run.wasmSelfMicros,
    `${label}.wasmSelfMicros`);
  const hostMicros = requireNumber(run.hostMicros, `${label}.hostMicros`);
  const callers = requireObject(run.callerAttribution,
    `${label}.callerAttribution`);
  assert.equal(callers.unresolvedWasmSelfSamples, 0,
    `${label} contains unresolved Wasm samples`);
  assert.equal(callers.attributedWasmSelfSamples, wasmSelfSamples,
    `${label} caller attribution is incomplete`);
  const reconstructedSummary = {
    window: run.window,
    sampleCount: wasmSelfSamples + hostSamples,
    resolvedWasmSamples: wasmSelfSamples,
    unresolvedWasmSamples: 0,
    hostSamples,
    totalSampleMicros: wasmSelfMicros + hostMicros,
    resolvedWasmMicros: wasmSelfMicros,
    unresolvedWasmMicros: 0,
    hostMicros,
  };
  assert.deepEqual(run.quality,
    makeProfileQuality(reconstructedSummary, run.comparability),
  `${label} quality does not match its contents`);
  assert.equal(run.quality.classification, "checked-diagnostic",
    `${label} is not checked diagnostic evidence`);
  return { receipt, wasmSelfSamples, hostSamples };
}

function equalReceipt(left, right) {
  return left.schemaVersion === right.schemaVersion &&
    left.id === right.id && left.sha256 === right.sha256 &&
    left.instancePolicy === right.instancePolicy;
}

function validateFunctionCoverage(functions, runs) {
  assert(Array.isArray(functions) && functions.length !== 0,
    "FIR profile aggregate must retain sampled functions");
  const runIds = runs.map(({ id }) => id);
  const indices = new Set();
  const totals = new Map(runIds.map((id) => [id, 0]));
  for (const function_ of functions) {
    requireObject(function_, "FIR aggregate function");
    const index = requireInteger(function_.index,
      "FIR aggregate function index");
    assert.equal(indices.has(index), false,
      `FIR aggregate repeats function index ${index}`);
    indices.add(index);
    const perRun = validatePerRun(function_.perRun, runIds,
      `FIR aggregate function ${index}`);
    for (const sample of perRun.values()) {
      totals.set(sample.run, totals.get(sample.run) + sample.selfSamples);
    }
    assert(Array.isArray(function_.callers),
      `FIR aggregate function ${index} callers must be an array`);
    const callerTotals = new Map(runIds.map((id) => [id, 0]));
    for (const caller of function_.callers) {
      const callerRuns = validatePerRun(caller.perRun, runIds,
        `FIR aggregate function ${index} caller`);
      for (const sample of callerRuns.values()) {
        callerTotals.set(sample.run,
          callerTotals.get(sample.run) + sample.selfSamples);
      }
    }
    for (const id of runIds) {
      assert.equal(callerTotals.get(id), perRun.get(id).selfSamples,
        `FIR aggregate function ${index} caller coverage is incomplete for ${id}`);
    }
  }
  for (const run of runs) {
    assert.equal(totals.get(run.id), run.wasmSelfSamples,
      `FIR aggregate function coverage is incomplete for ${run.id}`);
  }
}

function validatePerRun(value, runIds, label) {
  assert(Array.isArray(value) && value.length === runIds.length,
    `${label} must retain every run`);
  const result = new Map();
  for (const item of value) {
    requireObject(item, `${label} run`);
    requireString(item.run, `${label} run id`);
    assert(runIds.includes(item.run), `${label} names unknown run ${item.run}`);
    assert.equal(result.has(item.run), false,
      `${label} repeats run ${item.run}`);
    requireInteger(item.selfSamples, `${label} ${item.run} selfSamples`);
    requireNumber(item.selfMicros, `${label} ${item.run} selfMicros`);
    result.set(item.run, item);
  }
  return result;
}

export function validateProfileAggregateContract(packet) {
  requireObject(packet, "FIR sampled-profile aggregate");
  assert.equal(packet.schemaVersion, profileAggregateSchema,
    "unsupported FIR sampled-profile aggregate schema");
  assert.equal(packet.evidenceClass, "sampled-profile-aggregate",
    "FIR sampled-profile aggregate evidence class is invalid");
  assert.equal(packet.binding, "exact-release",
    "FIR profile aggregate is not exact-release evidence");
  const artifact = descriptor(packet.artifact, "FIR aggregate artifact", {
    positive: true,
  });
  const functionSidecar = descriptor(packet.functionSidecar,
    "FIR aggregate function sidecar", { positive: true });
  assert.equal(functionSidecar.schemaVersion, sidecarSchema,
    "FIR aggregate function sidecar has an unsupported schema");
  assert.equal(functionSidecar.artifactSha256, artifact.sha256,
    "FIR aggregate function sidecar is bound to another artifact");
  requireInteger(packet.runCount, "FIR aggregate runCount", 2);
  assert(Array.isArray(packet.runs) && packet.runs.length === packet.runCount,
    "FIR aggregate runCount differs from its runs");
  requireObject(packet.comparability, "FIR aggregate comparability");
  assert.equal(packet.comparability.status, "comparable",
    "FIR profile aggregate is not comparable");
  assert.equal(packet.comparability.override, false,
    "FIR profile aggregate uses an incomparable override");
  assert.deepEqual(packet.comparability.limitations, [],
    "FIR profile aggregate retains comparability limitations");
  requireSha256(packet.comparability.key,
    "FIR aggregate comparability key");
  const runIds = new Set();
  const validatedRuns = packet.runs.map((run, index) => {
    const result = validateAggregateRun(run, `FIR aggregate run ${index + 1}`,
      packet.comparability.key);
    assert.equal(runIds.has(run.id), false,
      `FIR aggregate repeats run id ${run.id}`);
    runIds.add(run.id);
    return { ...result, id: run.id };
  });
  const receipt = validatedRuns[0].receipt;
  for (const run of validatedRuns.slice(1)) {
    assert(equalReceipt(run.receipt, receipt),
      "FIR profile aggregate runs disagree on workload receipt or instance policy");
  }
  const wasmSamples = validatedRuns.map(({ wasmSelfSamples }) =>
    wasmSelfSamples);
  const hostShares = validatedRuns.map(({ wasmSelfSamples, hostSamples }) =>
    hostSamples / (wasmSelfSamples + hostSamples));
  assert.deepEqual(packet.quality, {
    classification: "comparable-diagnostic",
    limitations: [],
    metrics: {
      runCount: packet.runCount,
      wasmSelfSamples: {
        min: Math.min(...wasmSamples),
        max: Math.max(...wasmSamples),
      },
      hostSampleShare: {
        min: Math.min(...hostShares),
        max: Math.max(...hostShares),
      },
    },
  }, "FIR profile aggregate quality does not match its runs");
  assert.deepEqual(packet.callerAttribution, {
    method: "v8-cpu-profile-parent-edge/v1",
    unit: "sampled-target-self-time",
    caller: "immediate-parent-profile-node",
    coverage: "all-wasm-self-samples",
  }, "FIR profile aggregate caller-attribution contract is incomplete");
  validateFunctionCoverage(packet.functions, packet.runs);
  return commonClaims(packet, receipt);
}

export function validateSampledProfileContract(packet) {
  if (packet?.schemaVersion === profileEvidenceSchema) {
    return validateProfileEvidenceContract(packet);
  }
  if (packet?.schemaVersion === profileAggregateSchema) {
    return validateProfileAggregateContract(packet);
  }
  throw new Error(`unsupported FIR sampled-profile contract ${
    packet?.schemaVersion ?? "(missing)"}`);
}

export function validateProfileLifecycle(claims, lifecycle) {
  requireObject(claims, "FIR profile claims");
  assert.equal(claims.schemaVersion, profileClaimsSchema,
    "unsupported FIR profile claims schema");
  requireObject(lifecycle, "profile collection lifecycle");
  requireString(lifecycle.moduleInstance,
    "profile collection lifecycle.moduleInstance");
  assert.equal(lifecycle.moduleInstance, claims.instancePolicy,
    "profile collection lifecycle contradicts the FIR workload receipt");
  return lifecycle.moduleInstance;
}
