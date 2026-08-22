import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import inspector from "node:inspector";
import {
  existsSync,
  mkdirSync,
  readFileSync,
  renameSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { basename, dirname, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { performance } from "node:perf_hooks";

import { residentHelperFamily } from "../runtime-classification.mjs";
import { validateSidecar } from "../wasm/function-index-lib.mjs";

export { residentHelperFamily } from "../runtime-classification.mjs";

export const profileEvidenceSchema = "fir.sampled-profile/v1";

function sha256(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

function frameIndex(callFrame) {
  const text = `${callFrame.functionName ?? ""} ${callFrame.url ?? ""}`;
  const match = /wasm-function\[(\d+)\]/.exec(text);
  return match === null ? null : Number(match[1]);
}

export function profileFunctionFamily(function_) {
  if (function_ === undefined) return "wasm/unattributed";
  if (function_.origin === "lean-source") {
    return function_.compilerShape === "closed-declaration" ?
      "lean-source/closed-declaration" : "lean-source/function";
  }
  if (function_.origin === "resident-helper" && function_.name !== null) {
    return residentHelperFamily(function_.name);
  }
  return "wasm/linked-or-optimizer";
}

function sampleDeltas(profile) {
  assert(Array.isArray(profile.samples) && profile.samples.length !== 0,
    "CPU profile contains no samples");
  if (Array.isArray(profile.timeDeltas) &&
      profile.timeDeltas.length === profile.samples.length) {
    assert(profile.timeDeltas.every((delta) =>
      Number.isFinite(delta) && delta >= 0),
    "CPU profile contains an invalid sample delta");
    return profile.timeDeltas;
  }
  const total = profile.endTime - profile.startTime;
  assert(Number.isFinite(total) && total >= 0,
    "CPU profile has no usable time interval");
  return Array.from({ length: profile.samples.length }, () =>
    total / profile.samples.length);
}

function add(map, key, delta) {
  map.set(key, (map.get(key) ?? 0) + delta);
}

function profileNodeParents(profile, nodes) {
  assert.equal(nodes.size, profile.nodes.length,
    "CPU profile contains duplicate node ids");
  const parents = new Map();
  for (const node of profile.nodes) {
    const children = node.children ?? [];
    assert(Array.isArray(children),
      `CPU profile node ${node.id} has invalid children`);
    const localChildren = new Set();
    for (const child of children) {
      assert(nodes.has(child),
        `CPU profile node ${node.id} refers to missing child ${child}`);
      assert.notEqual(child, node.id,
        `CPU profile node ${node.id} is its own child`);
      assert.equal(localChildren.has(child), false,
        `CPU profile node ${node.id} repeats child ${child}`);
      localChildren.add(child);
      assert.equal(parents.has(child), false,
        `CPU profile node ${child} has multiple parents`);
      parents.set(child, node.id);
    }
  }

  const states = new Map();
  for (const id of nodes.keys()) {
    if (states.get(id) === 2) continue;
    const path = [];
    let current = id;
    while (current !== undefined && states.get(current) !== 2) {
      assert.notEqual(states.get(current), 1,
        `CPU profile parent graph contains a cycle at node ${current}`);
      states.set(current, 1);
      path.push(current);
      current = parents.get(current);
    }
    for (const item of path) states.set(item, 2);
  }
  return parents;
}

function frameLabel(callFrame) {
  return callFrame?.functionName || callFrame?.url || "(anonymous)";
}

function rootCallerDescriptor() {
  return {
    kind: "root",
    index: null,
    name: null,
    url: null,
    origin: null,
    family: "profile/root",
  };
}

function callerDescriptor(node, sidecar, strictFunctionIndices) {
  if (node === undefined || node.callFrame?.functionName === "(root)") {
    return rootCallerDescriptor();
  }
  const index = frameIndex(node.callFrame ?? {});
  if (index === null) {
    return {
      kind: "host-or-runtime",
      index: null,
      name: frameLabel(node.callFrame),
      url: node.callFrame?.url || null,
      origin: null,
      family: "host-or-runtime/unattributed",
    };
  }
  const function_ = sidecar.functions[index];
  if (strictFunctionIndices) {
    assert(function_ !== undefined,
      `CPU profile caller refers to Wasm function ${index} outside the sidecar`);
  }
  return {
    kind: "wasm",
    index,
    name: function_?.name ?? null,
    url: null,
    origin: function_?.origin ?? "unattributed",
    family: profileFunctionFamily(function_),
  };
}

function callerKey(targetIndex, caller) {
  return JSON.stringify([
    targetIndex,
    caller.kind,
    caller.index,
    caller.name,
    caller.url,
  ]);
}

function addCallerEdge(edges, targetIndex, target, caller, delta) {
  const key = callerKey(targetIndex, caller);
  const edge = edges.get(key) ?? {
    targetIndex,
    targetName: target?.name ?? null,
    targetOrigin: target?.origin ?? "unattributed",
    targetFamily: profileFunctionFamily(target),
    caller,
    selfMicros: 0,
    selfSamples: 0,
  };
  edge.selfMicros += delta;
  edge.selfSamples += 1;
  edges.set(key, edge);
}

export function summarizeCpuProfile(profile, sidecar, {
  startMicros = 0,
  durationMicros = Number.POSITIVE_INFINITY,
  strictFunctionIndices = false,
} = {}) {
  assert(profile !== null && typeof profile === "object",
    "CPU profile must be an object");
  assert(sidecar !== null && Array.isArray(sidecar.functions),
    "function sidecar must contain a function array");
  assert(Number.isFinite(startMicros) && startMicros >= 0,
    "profile summary start must be a nonnegative finite offset");
  assert((Number.isFinite(durationMicros) && durationMicros >= 0) ||
    durationMicros === Number.POSITIVE_INFINITY,
  "profile summary duration must be nonnegative");
  assert(Array.isArray(profile.nodes), "CPU profile contains no node array");
  const nodes = new Map(profile.nodes.map((node) => [node.id, node]));
  const parents = profileNodeParents(profile, nodes);
  const deltas = sampleDeltas(profile);
  const groups = new Map();
  const functions = new Map();
  const functionSamples = new Map();
  const frames = new Map();
  const callerEdges = new Map();
  let resolvedWasmMicros = 0;
  let unresolvedWasmMicros = 0;
  let hostMicros = 0;
  let resolvedWasmSamples = 0;
  let unresolvedWasmSamples = 0;
  let hostSamples = 0;
  let includedSampleCount = 0;
  let cursorMicros = 0;
  const endMicros = startMicros + durationMicros;
  for (const [sampleIndex, nodeId] of profile.samples.entries()) {
    const node = nodes.get(nodeId);
    assert(node !== undefined, `CPU sample refers to missing node ${nodeId}`);
    const rawDelta = deltas[sampleIndex];
    const intervalStart = cursorMicros;
    cursorMicros += rawDelta;
    const delta = Math.max(0, Math.min(cursorMicros, endMicros) -
      Math.max(intervalStart, startMicros));
    if (delta === 0) continue;
    includedSampleCount += 1;
    const index = frameIndex(node.callFrame ?? {});
    if (index === null) {
      hostMicros += delta;
      hostSamples += 1;
      add(groups, "host-or-runtime/unattributed", delta);
      add(frames, frameLabel(node.callFrame), delta);
      continue;
    }
    const function_ = sidecar.functions[index];
    if (strictFunctionIndices) {
      assert(function_ !== undefined,
        `CPU profile refers to Wasm function ${index} outside the sidecar`);
    }
    if (function_ === undefined) {
      unresolvedWasmMicros += delta;
      unresolvedWasmSamples += 1;
    } else {
      resolvedWasmMicros += delta;
      resolvedWasmSamples += 1;
    }
    add(groups, profileFunctionFamily(function_), delta);
    add(functions, index, delta);
    add(functionSamples, index, 1);
    const parentId = parents.get(nodeId);
    const caller = callerDescriptor(parentId === undefined ? undefined :
      nodes.get(parentId), sidecar, strictFunctionIndices);
    addCallerEdge(callerEdges, index, function_, caller, delta);
  }
  const descending = (left, right) => right.selfMicros - left.selfMicros ||
    String(left.name ?? left.index).localeCompare(
      String(right.name ?? right.index));
  return {
    window: {
      method: "phase-overlap-time-deltas/v1",
      startMicros,
      durationMicros: Number.isFinite(durationMicros) ? durationMicros : null,
      rawProfileMicros: deltas.reduce((sum, item) => sum + item, 0),
    },
    totalSampleMicros: resolvedWasmMicros + unresolvedWasmMicros + hostMicros,
    sampleCount: includedSampleCount,
    rawSampleCount: profile.samples.length,
    resolvedWasmMicros,
    unresolvedWasmMicros,
    hostMicros,
    resolvedWasmSamples,
    unresolvedWasmSamples,
    hostSamples,
    callerAttribution: {
      method: "v8-cpu-profile-parent-edge/v1",
      resolvedWasmSelfSamples: resolvedWasmSamples,
      unresolvedWasmSelfSamples: unresolvedWasmSamples,
      attributedWasmSelfSamples: [...callerEdges.values()].reduce(
        (sum, edge) => sum + edge.selfSamples, 0),
    },
    groups: [...groups].map(([name, selfMicros]) => ({ name, selfMicros }))
      .sort(descending),
    functions: [...functions].map(([index, selfMicros]) => ({
      index,
      name: sidecar.functions[index]?.name ?? null,
      origin: sidecar.functions[index]?.origin ?? "unattributed",
      family: profileFunctionFamily(sidecar.functions[index]),
      selfMicros,
      selfSamples: functionSamples.get(index),
    })).sort(descending),
    callerEdges: [...callerEdges.values()].sort((left, right) =>
      left.targetIndex - right.targetIndex ||
      right.selfMicros - left.selfMicros ||
      left.caller.kind.localeCompare(right.caller.kind) ||
      (left.caller.index ?? Number.MAX_SAFE_INTEGER) -
        (right.caller.index ?? Number.MAX_SAFE_INTEGER) ||
      String(left.caller.name).localeCompare(String(right.caller.name))),
    hostFrames: [...frames].map(([name, selfMicros]) => ({ name, selfMicros }))
      .sort(descending),
  };
}

function post(session, method, params = {}) {
  return new Promise((resolve_, reject) => session.post(method, params,
    (error, result) => error === null ? resolve_(result) : reject(error)));
}

async function measured(run) {
  const start = performance.now();
  const value = await run();
  return { value, elapsedMs: performance.now() - start };
}

function observation(value, phase) {
  assert(value !== null && typeof value === "object" && value.ok === true,
    `${phase} must return an object with ok: true after checking its result`);
  return value.observation ?? null;
}

function stableFile(path, before, label) {
  const after = readFileSync(path);
  assert.equal(sha256(after), sha256(before), `${label} changed during profiling`);
}

export async function runNodeProfile({
  wasmPath,
  sidecarPath,
  workloadPath,
  outputDirectory,
  metadata = {},
  samplingIntervalMicros = 1000,
}) {
  assert(Number.isSafeInteger(samplingIntervalMicros) &&
    samplingIntervalMicros > 0,
  "sampling interval must be a positive integer number of microseconds");
  const resolvedOutput = resolve(outputDirectory);
  assert.equal(existsSync(resolvedOutput), false,
    `profile output directory already exists: ${resolvedOutput}`);
  const totalStart = performance.now();
  const acquire = await measured(async () => {
    const resolvedWasm = resolve(wasmPath);
    const resolvedSidecar = resolve(sidecarPath);
    const resolvedWorkload = resolve(workloadPath);
    const wasmBytes = readFileSync(resolvedWasm);
    const sidecarBytes = readFileSync(resolvedSidecar);
    const workloadBytes = readFileSync(resolvedWorkload);
    const sidecar = JSON.parse(sidecarBytes);
    validateSidecar(wasmBytes, sidecar);
    const workload = await import(
      `${pathToFileURL(resolvedWorkload).href}?profile=${Date.now()}`);
    for (const name of ["setup", "firstCall", "steady"]) {
      assert.equal(typeof workload[name], "function",
        `profile workload must export ${name}`);
    }
    return {
      resolvedWasm,
      resolvedSidecar,
      resolvedWorkload,
      wasmBytes,
      sidecarBytes,
      workloadBytes,
      sidecar,
      workload,
    };
  });
  const context = {
    wasmPath: acquire.value.resolvedWasm,
    wasmBytes: Buffer.from(acquire.value.wasmBytes),
    sidecar: acquire.value.sidecar,
    artifactSha256: sha256(acquire.value.wasmBytes),
  };
  let state;
  let setup;
  let firstCall;
  let warmup = { value: null, elapsedMs: 0 };
  let steady;
  let startProfileMs = 0;
  let stopProfileMs = 0;
  let teardownMs = 0;
  let profile;
  let firstObservation;
  let warmupObservation = null;
  let steadyObservation;
  const session = new inspector.Session();
  try {
    setup = await measured(async () => acquire.value.workload.setup(context));
    state = setup.value;
    firstCall = await measured(async () =>
      acquire.value.workload.firstCall(state, context));
    firstObservation = observation(firstCall.value, "firstCall");
    if (typeof acquire.value.workload.warmup === "function") {
      warmup = await measured(async () =>
        acquire.value.workload.warmup(state, context));
      warmupObservation = observation(warmup.value, "warmup");
    }
    session.connect();
    await post(session, "Profiler.enable");
    await post(session, "Profiler.setSamplingInterval", {
      interval: samplingIntervalMicros,
    });
    const start = await measured(async () => post(session, "Profiler.start"));
    startProfileMs = start.elapsedMs;
    steady = await measured(async () =>
      acquire.value.workload.steady(state, context));
    steadyObservation = observation(steady.value, "steady");
    const stop = await measured(async () => post(session, "Profiler.stop"));
    stopProfileMs = stop.elapsedMs;
    profile = stop.value.profile;
    await post(session, "Profiler.disable");
  } finally {
    try {
      session.disconnect();
    } catch {
      // The session may not have connected if setup failed.
    }
    if (state !== undefined &&
        typeof acquire.value.workload.teardown === "function") {
      const teardown = await measured(async () =>
        acquire.value.workload.teardown(state, context));
      teardownMs = teardown.elapsedMs;
    }
    stableFile(acquire.value.resolvedWasm, acquire.value.wasmBytes,
      "Wasm artifact");
    stableFile(acquire.value.resolvedSidecar, acquire.value.sidecarBytes,
      "function sidecar");
    stableFile(acquire.value.resolvedWorkload, acquire.value.workloadBytes,
      "profile workload");
  }
  const summary = summarizeCpuProfile(profile, acquire.value.sidecar, {
    startMicros: startProfileMs * 1000,
    durationMicros: steady.elapsedMs * 1000,
  });
  const staging = `${resolvedOutput}.tmp-${process.pid}-${Date.now()}`;
  assert.equal(existsSync(staging), false,
    `profile staging directory already exists: ${staging}`);
  mkdirSync(dirname(resolvedOutput), { recursive: true });
  mkdirSync(staging);
  const rawProfilePath = join(resolvedOutput, "profile.cpuprofile");
  const rawProfileBytes = Buffer.from(`${JSON.stringify(profile)}\n`);
  const evidence = {
    schemaVersion: profileEvidenceSchema,
    evidenceClass: "sampled-profile",
    artifact: {
      file: basename(acquire.value.resolvedWasm),
      byteLength: acquire.value.wasmBytes.length,
      sha256: sha256(acquire.value.wasmBytes),
    },
    functionSidecar: {
      file: basename(acquire.value.resolvedSidecar),
      byteLength: acquire.value.sidecarBytes.length,
      sha256: sha256(acquire.value.sidecarBytes),
      schemaVersion: acquire.value.sidecar.schemaVersion,
      artifactSha256: acquire.value.sidecar.artifact.sha256,
    },
    workload: {
      file: basename(acquire.value.resolvedWorkload),
      byteLength: acquire.value.workloadBytes.length,
      sha256: sha256(acquire.value.workloadBytes),
      metadata: { ...metadata, ...(acquire.value.workload.metadata ?? {}) },
    },
    runtime: {
      node: process.version,
      v8: process.versions.v8,
      platform: process.platform,
      arch: process.arch,
      samplingIntervalMicros,
    },
    phases: {
      acquireMs: acquire.elapsedMs,
      setupMs: setup.elapsedMs,
      firstCallMs: firstCall.elapsedMs,
      warmupMs: warmup.elapsedMs,
      profilerStartMs: startProfileMs,
      steadyProfiledMs: steady.elapsedMs,
      profilerStopMs: stopProfileMs,
      teardownMs,
      totalMs: performance.now() - totalStart,
    },
    observations: {
      firstCall: firstObservation,
      warmup: warmupObservation,
      steady: steadyObservation,
    },
    rawProfile: {
      file: basename(rawProfilePath),
      byteLength: rawProfileBytes.length,
      sha256: sha256(rawProfileBytes),
    },
    summary,
  };
  const evidencePath = join(resolvedOutput, "evidence.json");
  try {
    writeFileSync(join(staging, basename(rawProfilePath)), rawProfileBytes);
    writeFileSync(join(staging, basename(evidencePath)),
      Buffer.from(`${JSON.stringify(evidence, null, 2)}\n`));
    renameSync(staging, resolvedOutput);
  } catch (error) {
    rmSync(staging, { recursive: true, force: true });
    throw error;
  }
  return { evidence, evidencePath, rawProfilePath };
}
