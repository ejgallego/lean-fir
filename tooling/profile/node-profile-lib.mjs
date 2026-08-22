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
import { basename, dirname, isAbsolute, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { performance } from "node:perf_hooks";

import { residentHelperFamily } from "../runtime-classification.mjs";
import { validateSidecar } from "../wasm/function-index-lib.mjs";

export { residentHelperFamily } from "../runtime-classification.mjs";

export const legacyProfileEvidenceSchema = "fir.sampled-profile/v1";
export const profileEvidenceSchema = "fir.sampled-profile/v2";
export const profileComparabilitySchema = "fir.profile-comparability/v1";
export const workloadReceiptSchema = "fir.profile-workload-receipt/v1";
export const profileQualityPolicy = Object.freeze({
  minimumWasmSelfSamples: 100,
});

function sha256(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

function jsonValue(value, label) {
  let encoded;
  try {
    encoded = JSON.stringify(value);
  } catch (error) {
    throw new Error(`${label} is not JSON-compatible: ${error.message}`);
  }
  assert.notEqual(encoded, undefined, `${label} is not a JSON value`);
  const decoded = JSON.parse(encoded);
  assert.deepEqual(decoded, value,
    `${label} must contain only stable JSON values`);
  return decoded;
}

function jsonObject(value, label) {
  const result = jsonValue(value, label);
  assert(result !== null && typeof result === "object" &&
    !Array.isArray(result), `${label} must be a JSON object`);
  return result;
}

function canonicalJson(value) {
  if (Array.isArray(value)) {
    return `[${value.map(canonicalJson).join(",")}]`;
  }
  if (value !== null && typeof value === "object") {
    return `{${Object.keys(value).sort().map((key) =>
      `${JSON.stringify(key)}:${canonicalJson(value[key])}`).join(",")}}`;
  }
  return JSON.stringify(value);
}

function deepFreeze(value) {
  if (value !== null && typeof value === "object" && !Object.isFrozen(value)) {
    for (const child of Object.values(value)) deepFreeze(child);
    Object.freeze(value);
  }
  return value;
}

function identity(descriptor, label) {
  if (descriptor === null || typeof descriptor !== "object") return null;
  assert(Number.isSafeInteger(descriptor.byteLength) &&
    descriptor.byteLength >= 0, `${label} has an invalid byte length`);
  assert.equal(typeof descriptor.sha256, "string",
    `${label} has no SHA-256 identity`);
  assert.match(descriptor.sha256, /^[0-9a-f]{64}$/,
    `${label} has an invalid SHA-256 identity`);
  return {
    byteLength: descriptor.byteLength,
    sha256: descriptor.sha256,
  };
}

function receiptEntries(receiptDirectory, entries, kind) {
  assert(Array.isArray(entries), `workload receipt ${kind} must be an array`);
  const roles = new Set();
  return entries.map((entry) => {
    assert(entry !== null && typeof entry === "object" &&
      !Array.isArray(entry), `workload receipt ${kind} entry must be an object`);
    assert.equal(typeof entry.role, "string",
      `workload receipt ${kind} entry has no role`);
    assert(entry.role.length !== 0,
      `workload receipt ${kind} role must not be empty`);
    assert.equal(roles.has(entry.role), false,
      `workload receipt repeats ${kind} role ${entry.role}`);
    roles.add(entry.role);
    assert.equal(typeof entry.path, "string",
      `workload receipt ${kind} ${entry.role} has no path`);
    assert(entry.path.length !== 0 && !isAbsolute(entry.path),
      `workload receipt ${kind} ${entry.role} path must be relative`);
    const resolvedPath = resolve(receiptDirectory, entry.path);
    const bytes = readFileSync(resolvedPath);
    return {
      resolvedPath,
      bytes,
      descriptor: {
        role: entry.role,
        file: basename(resolvedPath),
        byteLength: bytes.length,
        sha256: sha256(bytes),
      },
    };
  }).sort((left, right) =>
    left.descriptor.role.localeCompare(right.descriptor.role));
}

function loadWorkloadReceipt(path) {
  if (path === undefined) return null;
  const resolvedPath = resolve(path);
  const bytes = readFileSync(resolvedPath);
  const receipt = jsonValue(JSON.parse(bytes), "workload receipt");
  assert.equal(receipt.schemaVersion, workloadReceiptSchema,
    `unsupported workload receipt schema ${receipt.schemaVersion}`);
  for (const name of ["id", "semanticEndpoint", "instancePolicy"]) {
    assert.equal(typeof receipt[name], "string",
      `workload receipt ${name} must be a string`);
    assert(receipt[name].length !== 0,
      `workload receipt ${name} must not be empty`);
  }
  const parameters = jsonObject(receipt.parameters ?? {},
    "workload receipt parameters");
  const directory = dirname(resolvedPath);
  const dependencies = receiptEntries(directory,
    receipt.dependencies ?? [], "dependencies");
  const inputs = receiptEntries(directory, receipt.inputs ?? [], "inputs");
  const paths = [...dependencies, ...inputs].map(({ resolvedPath: item }) =>
    item);
  assert.equal(new Set(paths).size, paths.length,
    "workload receipt repeats a dependency or input path");
  return {
    resolvedPath,
    bytes,
    dependencies,
    inputs,
    descriptor: {
      schemaVersion: receipt.schemaVersion,
      file: basename(resolvedPath),
      byteLength: bytes.length,
      sha256: sha256(bytes),
      id: receipt.id,
      semanticEndpoint: receipt.semanticEndpoint,
      instancePolicy: receipt.instancePolicy,
      parameters,
    },
  };
}

function descriptorDimensions(items) {
  if (!Array.isArray(items)) return null;
  const roles = new Set();
  return items.map((descriptor) => {
    assert.equal(typeof descriptor?.role, "string",
      "profile workload artifact has no role");
    assert(descriptor.role.length !== 0,
      "profile workload artifact role must not be empty");
    assert.equal(roles.has(descriptor.role), false,
      `profile workload repeats artifact role ${descriptor.role}`);
    roles.add(descriptor.role);
    return {
      role: descriptor.role,
      ...identity(descriptor,
        `profile workload artifact ${descriptor.role}`),
    };
  }).sort((left, right) => left.role.localeCompare(right.role));
}

export function makeProfileComparability({
  schemaVersion,
  workload,
  runtime,
  observations,
}) {
  const limitations = [];
  if (schemaVersion !== profileEvidenceSchema) {
    limitations.push("legacy-profile-evidence-schema");
  }
  if (workload?.receipt?.schemaVersion !== workloadReceiptSchema) {
    limitations.push("workload-receipt-missing");
  }
  const runtimeFields = ["node", "v8", "platform", "arch",
    "samplingIntervalMicros"];
  for (const field of runtimeFields) {
    if (runtime?.[field] === undefined || runtime?.[field] === null) {
      limitations.push(`runtime-${field}-missing`);
    }
  }
  const dimensions = {
    workload: {
      module: identity(workload, "profile workload module"),
      receipt: identity(workload?.receipt, "profile workload receipt"),
      metadata: jsonValue(workload?.metadata ?? null,
        "profile workload metadata"),
      dependencies: descriptorDimensions(workload?.dependencies),
      inputs: descriptorDimensions(workload?.inputs),
    },
    runtime: Object.fromEntries(runtimeFields.map((field) =>
      [field, runtime?.[field] ?? null])),
    observations: jsonValue(observations ?? null, "profile observations"),
  };
  if (dimensions.workload.module === null) {
    limitations.push("workload-module-identity-missing");
  }
  if (dimensions.workload.dependencies === null) {
    limitations.push("workload-dependencies-missing");
  }
  if (dimensions.workload.inputs === null) {
    limitations.push("workload-inputs-missing");
  }
  const uniqueLimitations = [...new Set(limitations)].sort();
  const eligible = uniqueLimitations.length === 0;
  return {
    schemaVersion: profileComparabilitySchema,
    eligible,
    key: eligible ? sha256(Buffer.from(canonicalJson(dimensions))) : null,
    limitations: uniqueLimitations,
    dimensions,
  };
}

export function makeProfileQuality(summary, comparability) {
  const totalSamples = summary.resolvedWasmSamples +
    summary.unresolvedWasmSamples + summary.hostSamples;
  const wasmSamples = summary.resolvedWasmSamples +
    summary.unresolvedWasmSamples;
  const limitations = [...comparability.limitations];
  if (summary.window?.method !== "phase-overlap-time-deltas/v1") {
    limitations.push("approximate-temporal-attribution");
  }
  if (summary.unresolvedWasmSamples !== 0) {
    limitations.push("unresolved-wasm-samples");
  }
  if (wasmSamples === 0) limitations.push("no-wasm-self-samples");
  if (wasmSamples < profileQualityPolicy.minimumWasmSelfSamples) {
    limitations.push("low-wasm-self-sample-count");
  }
  return {
    classification: limitations.length === 0 ? "checked-diagnostic" :
      "screening",
    limitations: [...new Set(limitations)].sort(),
    policy: profileQualityPolicy,
    metrics: {
      includedSamples: summary.sampleCount,
      wasmSelfSamples: wasmSamples,
      hostSamples: summary.hostSamples,
      wasmSelfSampleShare: totalSamples === 0 ? null : wasmSamples / totalSamples,
      sampledMicros: summary.totalSampleMicros,
    },
  };
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

function sampleDeltas(profile, requireTimeDeltas) {
  assert(Array.isArray(profile.samples) && profile.samples.length !== 0,
    "CPU profile contains no samples");
  if (profile.timeDeltas !== undefined) {
    assert(Array.isArray(profile.timeDeltas) &&
      profile.timeDeltas.length === profile.samples.length,
    "CPU profile time deltas do not match its samples");
    assert(profile.timeDeltas.every((delta) =>
      Number.isFinite(delta) && delta >= 0),
    "CPU profile contains an invalid sample delta");
    return {
      values: profile.timeDeltas,
      method: "phase-overlap-time-deltas/v1",
    };
  }
  assert.equal(requireTimeDeltas, false,
    "exact CPU profile evidence requires sample time deltas");
  const total = profile.endTime - profile.startTime;
  assert(Number.isFinite(total) && total >= 0,
    "CPU profile has no usable time interval");
  return {
    values: Array.from({ length: profile.samples.length }, () =>
      total / profile.samples.length),
    method: "uniform-profile-interval/v1",
  };
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
  requireTimeDeltas = false,
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
  const temporal = sampleDeltas(profile, requireTimeDeltas);
  const deltas = temporal.values;
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
      method: temporal.method,
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
  workloadReceiptPath,
  outputDirectory,
  metadata = {},
  metadataPath,
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
    const workloadReceipt = loadWorkloadReceipt(workloadReceiptPath);
    const resolvedMetadata = metadataPath === undefined ? undefined :
      resolve(metadataPath);
    const metadataBytes = resolvedMetadata === undefined ? undefined :
      readFileSync(resolvedMetadata);
    const fileMetadata = metadataBytes === undefined ? {} :
      JSON.parse(metadataBytes);
    const workload = await import(
      `${pathToFileURL(resolvedWorkload).href}?profile=${Date.now()}`);
    for (const name of ["setup", "firstCall", "steady"]) {
      assert.equal(typeof workload[name], "function",
        `profile workload must export ${name}`);
    }
    const workloadMetadata = jsonValue({
      ...jsonObject(metadata, "profile metadata"),
      ...jsonObject(fileMetadata, "profile metadata file"),
      ...jsonObject(workload.metadata ?? {}, "workload module metadata"),
    }, "merged profile workload metadata");
    return {
      resolvedWasm,
      resolvedSidecar,
      resolvedWorkload,
      wasmBytes,
      sidecarBytes,
      workloadBytes,
      sidecar,
      workload,
      workloadMetadata,
      workloadReceipt,
      resolvedMetadata,
      metadataBytes,
    };
  });
  const context = {
    wasmPath: acquire.value.resolvedWasm,
    wasmBytes: Buffer.from(acquire.value.wasmBytes),
    sidecar: deepFreeze(jsonValue(acquire.value.sidecar,
      "function sidecar context")),
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
    if (acquire.value.resolvedMetadata !== undefined) {
      stableFile(acquire.value.resolvedMetadata, acquire.value.metadataBytes,
        "profile metadata");
    }
    if (acquire.value.workloadReceipt !== null) {
      stableFile(acquire.value.workloadReceipt.resolvedPath,
        acquire.value.workloadReceipt.bytes, "profile workload receipt");
      for (const item of [
        ...acquire.value.workloadReceipt.dependencies,
        ...acquire.value.workloadReceipt.inputs,
      ]) {
        stableFile(item.resolvedPath, item.bytes,
          `profile workload artifact ${item.descriptor.role}`);
      }
    }
  }
  const authoritativeSidecar = JSON.parse(acquire.value.sidecarBytes);
  validateSidecar(acquire.value.wasmBytes, authoritativeSidecar);
  const summary = summarizeCpuProfile(profile, authoritativeSidecar, {
    startMicros: startProfileMs * 1000,
    durationMicros: steady.elapsedMs * 1000,
    requireTimeDeltas: true,
  });
  const staging = `${resolvedOutput}.tmp-${process.pid}-${Date.now()}`;
  assert.equal(existsSync(staging), false,
    `profile staging directory already exists: ${staging}`);
  mkdirSync(dirname(resolvedOutput), { recursive: true });
  mkdirSync(staging);
  const rawProfilePath = join(resolvedOutput, "profile.cpuprofile");
  const rawProfileBytes = Buffer.from(`${JSON.stringify(profile)}\n`);
  const workloadEvidence = {
    file: basename(acquire.value.resolvedWorkload),
    byteLength: acquire.value.workloadBytes.length,
    sha256: sha256(acquire.value.workloadBytes),
    metadata: acquire.value.workloadMetadata,
    metadataSource: acquire.value.metadataBytes === undefined ? null : {
      file: basename(acquire.value.resolvedMetadata),
      byteLength: acquire.value.metadataBytes.length,
      sha256: sha256(acquire.value.metadataBytes),
    },
    receipt: acquire.value.workloadReceipt?.descriptor ?? null,
    dependencies: acquire.value.workloadReceipt?.dependencies.map(
      ({ descriptor }) => descriptor) ?? null,
    inputs: acquire.value.workloadReceipt?.inputs.map(
      ({ descriptor }) => descriptor) ?? null,
  };
  const runtime = {
    node: process.version,
    v8: process.versions.v8,
    platform: process.platform,
    arch: process.arch,
    samplingIntervalMicros,
  };
  const observations = {
    firstCall: firstObservation,
    warmup: warmupObservation,
    steady: steadyObservation,
  };
  const comparability = makeProfileComparability({
    schemaVersion: profileEvidenceSchema,
    workload: workloadEvidence,
    runtime,
    observations,
  });
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
      schemaVersion: authoritativeSidecar.schemaVersion,
      artifactSha256: authoritativeSidecar.artifact.sha256,
    },
    workload: workloadEvidence,
    runtime,
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
    observations,
    rawProfile: {
      file: basename(rawProfilePath),
      byteLength: rawProfileBytes.length,
      sha256: sha256(rawProfileBytes),
    },
    comparability,
    quality: makeProfileQuality(summary, comparability),
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
