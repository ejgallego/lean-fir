import {
  makeProfileComparability,
  makeProfileQuality,
  profileEvidenceSchema,
  workloadReceiptSchema,
} from "../node-profile-lib.mjs";
import { profileAggregateSchema } from "../profile-aggregate-lib.mjs";
import { sidecarSchema } from "../../wasm/function-index-lib.mjs";

const digest = (character) => character.repeat(64);

function profileSummary() {
  return {
    window: {
      method: "phase-overlap-time-deltas/v1",
      startMicros: 0,
      durationMicros: 50_000,
      rawProfileMicros: 50_000,
    },
    totalSampleMicros: 50_000,
    sampleCount: 100,
    rawSampleCount: 100,
    resolvedWasmMicros: 50_000,
    unresolvedWasmMicros: 0,
    hostMicros: 0,
    resolvedWasmSamples: 100,
    unresolvedWasmSamples: 0,
    hostSamples: 0,
    callerAttribution: {
      method: "v8-cpu-profile-parent-edge/v1",
      resolvedWasmSelfSamples: 100,
      unresolvedWasmSelfSamples: 0,
      attributedWasmSelfSamples: 100,
    },
    groups: [{ name: "lean-source/function", selfMicros: 50_000 }],
    functions: [{
      index: 0,
      name: "Fixture.steady",
      origin: "lean-source",
      family: "lean-source/function",
      selfMicros: 50_000,
      selfSamples: 100,
    }],
    callerEdges: [{
      targetIndex: 0,
      targetName: "Fixture.steady",
      targetOrigin: "lean-source",
      targetFamily: "lean-source/function",
      caller: {
        kind: "root",
        index: null,
        name: null,
        url: null,
        origin: null,
        family: "profile/root",
      },
      selfMicros: 50_000,
      selfSamples: 100,
    }],
    hostFrames: [],
  };
}

export function makeProfileContractFixture() {
  const workload = {
    file: "profile-workload.mjs",
    byteLength: 1,
    sha256: digest("c"),
    metadata: { id: "fir/profile-contract-fixture" },
    metadataSource: null,
    receipt: {
      schemaVersion: workloadReceiptSchema,
      file: "workload-receipt.json",
      byteLength: 1,
      sha256: digest("d"),
      id: "fir/profile-contract-fixture",
      semanticEndpoint: "checked fixture result",
      instancePolicy: "fresh-instance-per-profile",
      parameters: { rounds: 100 },
    },
    dependencies: [],
    inputs: [],
  };
  const runtime = {
    node: "v24.19.0",
    v8: "fixture-v8",
    platform: "linux",
    arch: "x64",
    samplingIntervalMicros: 500,
  };
  const observations = {
    firstCall: { digest: "checked" },
    warmup: null,
    steady: { digest: "checked" },
  };
  const summary = profileSummary();
  const comparability = makeProfileComparability({
    schemaVersion: profileEvidenceSchema,
    workload,
    runtime,
    observations,
  });
  return {
    schemaVersion: profileEvidenceSchema,
    evidenceClass: "sampled-profile",
    artifact: {
      file: "fixture.wasm",
      byteLength: 1,
      sha256: digest("a"),
    },
    functionSidecar: {
      file: "fixture.wasm.functions.json",
      byteLength: 1,
      sha256: digest("b"),
      schemaVersion: sidecarSchema,
      artifactSha256: digest("a"),
    },
    workload,
    runtime,
    phases: {
      acquireMs: 0,
      setupMs: 0,
      firstCallMs: 0,
      warmupMs: 0,
      profilerStartMs: 0,
      steadyProfiledMs: 50,
      profilerStopMs: 0,
      teardownMs: 0,
      totalMs: 50,
    },
    observations,
    rawProfile: {
      file: "profile.cpuprofile",
      byteLength: 1,
      sha256: digest("e"),
    },
    comparability,
    quality: makeProfileQuality(summary, comparability),
    summary,
  };
}

function aggregateRun(profile, id, evidenceDigest, rawDigest) {
  return {
    id,
    binding: "exact-release",
    evidence: {
      file: `${id}.evidence.json`,
      byteLength: 1,
      sha256: evidenceDigest,
    },
    rawProfile: {
      file: `${id}.cpuprofile`,
      byteLength: 1,
      sha256: rawDigest,
    },
    workload: structuredClone(profile.workload),
    runtime: structuredClone(profile.runtime),
    observations: structuredClone(profile.observations),
    window: structuredClone(profile.summary.window),
    wasmSelfSamples: profile.summary.resolvedWasmSamples,
    wasmSelfMicros: profile.summary.resolvedWasmMicros,
    hostSamples: profile.summary.hostSamples,
    hostMicros: profile.summary.hostMicros,
    callerAttribution: structuredClone(profile.summary.callerAttribution),
    comparability: structuredClone(profile.comparability),
    quality: structuredClone(profile.quality),
  };
}

function zeroStatistics(value) {
  return { median: value, mad: 0, min: value, max: value, span: 0 };
}

export function makeProfileAggregateContractFixture() {
  const profile = makeProfileContractFixture();
  const runs = [
    aggregateRun(profile, "run-1", digest("f"), digest("1")),
    aggregateRun(profile, "run-2", digest("9"), digest("2")),
  ];
  const selfSamples = zeroStatistics(100);
  const selfMicros = zeroStatistics(50_000);
  const share = zeroStatistics(1);
  return {
    schemaVersion: profileAggregateSchema,
    evidenceClass: "sampled-profile-aggregate",
    binding: "exact-release",
    artifact: structuredClone(profile.artifact),
    functionSidecar: structuredClone(profile.functionSidecar),
    runCount: runs.length,
    comparability: {
      status: "comparable",
      key: profile.comparability.key,
      limitations: [],
      override: false,
    },
    quality: {
      classification: "comparable-diagnostic",
      limitations: [],
      metrics: {
        runCount: runs.length,
        wasmSelfSamples: { min: 100, max: 100 },
        hostSampleShare: { min: 0, max: 0 },
      },
    },
    callerAttribution: {
      method: "v8-cpu-profile-parent-edge/v1",
      unit: "sampled-target-self-time",
      caller: "immediate-parent-profile-node",
      coverage: "all-wasm-self-samples",
    },
    runs,
    functions: [{
      index: 0,
      name: "Fixture.steady",
      optimizerName: "0",
      origin: "lean-source",
      family: "lean-source/function",
      bodyBytes: 1,
      perRun: runs.map(({ id }) => ({
        run: id,
        selfSamples: 100,
        selfMicros: 50_000,
        wasmSelfShare: 1,
        rank: 1,
      })),
      callers: [{
        kind: "root",
        index: null,
        name: null,
        url: null,
        origin: null,
        family: "profile/root",
        perRun: runs.map(({ id }) => ({
          run: id,
          selfSamples: 100,
          selfMicros: 50_000,
          wasmSelfShare: 1,
          targetSelfShare: 1,
        })),
        aggregate: {
          selfSamples,
          selfMicros,
          wasmSelfShare: share,
          targetSelfShare: {
            ...share,
            targetSampledRuns: runs.length,
            edgePresentRuns: runs.length,
          },
        },
      }],
      aggregate: {
        selfSamples,
        selfMicros,
        wasmSelfShare: share,
        rank: { ...zeroStatistics(1), presentRuns: runs.length },
      },
    }],
  };
}
