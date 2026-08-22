import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  mkdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { join, resolve } from "node:path";
import test from "node:test";

import { makeToolingTemporaryDirectory } from "../worktree-temp.mjs";
import {
  moduleShape,
  sha256,
  sidecarSchema,
} from "../wasm/function-index-lib.mjs";
import { profileEvidenceSchema } from "./node-profile-lib.mjs";
import {
  aggregateProfileEvidence,
  profileAggregateSchema,
} from "./profile-aggregate-lib.mjs";

const aggregateTool = resolve(import.meta.dirname, "profile-aggregate.mjs");

function fixtureWasm() {
  return Buffer.from([
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
    0x01, 0x04, 0x01, 0x60, 0x00, 0x00,
    0x03, 0x03, 0x02, 0x00, 0x00,
    0x0a, 0x07, 0x02, 0x02, 0x00, 0x0b, 0x02, 0x00, 0x0b,
  ]);
}

function fixtureSidecar(wasm) {
  const shape = moduleShape(wasm);
  return {
    schemaVersion: sidecarSchema,
    artifact: shape,
    capture: {
      schemaVersion: "fixture",
      inputArtifact: { byteLength: wasm.length, sha256: sha256(wasm) },
      identityProtocol: "fixture",
      producer: "profile-aggregate-unit-test",
    },
    functions: ["Fixture.hot", "fir_heap_alloc"].map((name, index) => ({
      index,
      name,
      optimizerName: String(index),
      origin: index === 0 ? "lean-source" : "resident-helper",
      compilerShape: "ordinary",
      imported: false,
      bodyBytes: shape.functionBodyBytes[index],
      exportedAs: [],
      directCallees: [],
      unresolvedCallTargets: [],
    })),
  };
}

function frame(id, index, children = undefined) {
  const result = {
    id,
    callFrame: {
      functionName: index === null ? "host" : `wasm-function[${index}]`,
      url: index === null ? "file:///driver.mjs" : "wasm://fixture",
    },
  };
  if (children !== undefined) result.children = children;
  return result;
}

function writeEvidence(directory, name, profile, wasm, sidecarBytes, {
  artifactSha256 = sha256(wasm),
} = {}) {
  const runDirectory = join(directory, name);
  mkdirSync(runDirectory);
  const rawBytes = Buffer.from(`${JSON.stringify(profile)}\n`);
  const rawPath = join(runDirectory, "profile.cpuprofile");
  writeFileSync(rawPath, rawBytes);
  const evidence = {
    schemaVersion: profileEvidenceSchema,
    evidenceClass: "sampled-profile",
    artifact: {
      file: "fixture.wasm",
      byteLength: wasm.length,
      sha256: artifactSha256,
    },
    functionSidecar: {
      file: "fixture.wasm.functions.json",
      byteLength: sidecarBytes.length,
      sha256: sha256(sidecarBytes),
      schemaVersion: sidecarSchema,
      artifactSha256,
    },
    workload: {
      file: "fixture-workload.mjs",
      byteLength: 1,
      sha256: "fixture",
      metadata: { id: name },
    },
    runtime: { node: process.version, v8: process.versions.v8 },
    phases: { steadyProfiledMs: 1 },
    observations: { steady: { digest: "checked" } },
    rawProfile: {
      file: "profile.cpuprofile",
      byteLength: rawBytes.length,
      sha256: sha256(rawBytes),
    },
    summary: {
      window: {
        method: "phase-overlap-time-deltas/v1",
        startMicros: 0,
        durationMicros: null,
      },
    },
  };
  const evidencePath = join(runDirectory, "evidence.json");
  writeFileSync(evidencePath, `${JSON.stringify(evidence, null, 2)}\n`);
  return evidencePath;
}

function fixture(directory) {
  const wasm = fixtureWasm();
  const sidecar = fixtureSidecar(wasm);
  const sidecarBytes = Buffer.from(`${JSON.stringify(sidecar, null, 2)}\n`);
  const wasmPath = join(directory, "fixture.wasm");
  const sidecarPath = join(directory, "fixture.wasm.functions.json");
  writeFileSync(wasmPath, wasm);
  writeFileSync(sidecarPath, sidecarBytes);
  const first = writeEvidence(directory, "first", {
    startTime: 0,
    endTime: 40,
    nodes: [
      frame(1, 0, [2]),
      frame(2, 0),
      frame(3, 1),
      frame(4, null, [1, 3]),
    ],
    samples: [1, 2, 3, 4],
    timeDeltas: [10, 10, 10, 10],
  }, wasm, sidecarBytes);
  const second = writeEvidence(directory, "second", {
    startTime: 0,
    endTime: 50,
    nodes: [frame(1, 0), frame(2, 1), frame(3, null, [1, 2])],
    samples: [1, 2, 2, 2, 3],
    timeDeltas: [10, 10, 10, 10, 10],
  }, wasm, sidecarBytes);
  return { wasm, sidecarBytes, wasmPath, sidecarPath, first, second };
}

test("aggregates duplicate V8 nodes by exact final function identity", () => {
  const directory = makeToolingTemporaryDirectory("fir-profile-aggregate-");
  try {
    const paths = fixture(directory);
    const report = aggregateProfileEvidence({
      wasmPath: paths.wasmPath,
      sidecarPath: paths.sidecarPath,
      evidencePaths: [paths.first, paths.second],
    });
    assert.equal(report.schemaVersion, profileAggregateSchema);
    assert.equal(report.binding, "exact-release");
    assert.equal(report.runCount, 2);
    assert.equal(report.binding, "exact-release");
    assert.equal(report.runs[0].wasmSelfSamples, 3);
    assert.equal(report.runs[1].wasmSelfSamples, 4);
    const hot = report.functions.find(({ index }) => index === 0);
    const allocation = report.functions.find(({ index }) => index === 1);
    assert.deepEqual(hot.perRun.map(({ selfSamples, rank }) =>
      ({ selfSamples, rank })), [
      { selfSamples: 2, rank: 1 },
      { selfSamples: 1, rank: 2 },
    ]);
    assert.equal(hot.aggregate.wasmSelfShare.median, 11 / 24);
    assert.equal(hot.aggregate.rank.span, 1);
    assert.equal(hot.bodyBytes, 2);
    assert.equal(report.callerAttribution.method,
      "v8-cpu-profile-parent-edge/v1");
    assert.equal(report.runs[0].callerAttribution.attributedWasmSelfSamples, 3);
    const hostCaller = hot.callers.find(({ kind }) =>
      kind === "host-or-runtime");
    const recursiveCaller = hot.callers.find(({ kind, index }) =>
      kind === "wasm" && index === 0);
    assert.deepEqual(hostCaller.perRun.map(({ selfSamples,
      targetSelfShare }) => ({ selfSamples, targetSelfShare })), [
      { selfSamples: 1, targetSelfShare: 0.5 },
      { selfSamples: 1, targetSelfShare: 1 },
    ]);
    assert.equal(hostCaller.aggregate.targetSelfShare.median, 0.75);
    assert.equal(recursiveCaller.aggregate.wasmSelfShare.median, 1 / 6);
    assert.equal(recursiveCaller.aggregate.targetSelfShare.median, 0.25);
    assert.equal(allocation.family, "resident/allocation");
    assert.equal(allocation.aggregate.wasmSelfShare.median, 13 / 24);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

test("rejects mixed artifacts, malformed indices, and output reuse", () => {
  const directory = makeToolingTemporaryDirectory(
    "fir-profile-aggregate-fail-");
  try {
    const paths = fixture(directory);
    const mixed = writeEvidence(directory, "mixed", {
      startTime: 0,
      endTime: 10,
      nodes: [frame(1, 0)],
      samples: [1],
      timeDeltas: [10],
    }, paths.wasm, paths.sidecarBytes, { artifactSha256: "0".repeat(64) });
    assert.throws(() => aggregateProfileEvidence({
      wasmPath: paths.wasmPath,
      sidecarPath: paths.sidecarPath,
      evidencePaths: [mixed],
    }), /different Wasm artifact/);

    const malformed = writeEvidence(directory, "malformed", {
      startTime: 0,
      endTime: 10,
      nodes: [frame(1, 9)],
      samples: [1],
      timeDeltas: [10],
    }, paths.wasm, paths.sidecarBytes);
    assert.throws(() => aggregateProfileEvidence({
      wasmPath: paths.wasmPath,
      sidecarPath: paths.sidecarPath,
      evidencePaths: [malformed],
    }), /function 9 outside the sidecar/);

    const malformedCaller = writeEvidence(directory, "malformed-caller", {
      startTime: 0,
      endTime: 10,
      nodes: [frame(1, 9, [2]), frame(2, 0)],
      samples: [2],
      timeDeltas: [10],
    }, paths.wasm, paths.sidecarBytes);
    assert.throws(() => aggregateProfileEvidence({
      wasmPath: paths.wasmPath,
      sidecarPath: paths.sidecarPath,
      evidencePaths: [malformedCaller],
    }), /caller refers to Wasm function 9 outside the sidecar/);

    const output = join(directory, "aggregate.json");
    const result = execFileSync(process.execPath, [
      aggregateTool,
      "--wasm", paths.wasmPath,
      "--sidecar", paths.sidecarPath,
      "--evidence", paths.first,
      "--evidence", paths.second,
      "--out", output,
    ], { encoding: "utf8" }).trim();
    assert.equal(result, output);
    const report = JSON.parse(readFileSync(output, "utf8"));
    assert.equal(report.runCount, 2);
    const before = sha256(readFileSync(output));
    assert.throws(() => execFileSync(process.execPath, [
      aggregateTool,
      "--wasm", paths.wasmPath,
      "--sidecar", paths.sidecarPath,
      "--evidence", paths.first,
      "--out", output,
    ], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }),
    (error) => error.stderr.includes("profile aggregate output already exists"));
    assert.equal(sha256(readFileSync(output)), before);

    const rawOutput = join(directory, "raw-aggregate.json");
    const rawProfile = join(directory, "first", "profile.cpuprofile");
    execFileSync(process.execPath, [
      aggregateTool,
      "--wasm", paths.wasmPath,
      "--sidecar", paths.sidecarPath,
      "--profile", rawProfile,
      "--out", rawOutput,
    ]);
    const rawReport = JSON.parse(readFileSync(rawOutput, "utf8"));
    assert.equal(rawReport.binding, "contains-unbound-raw-profiles");
    assert.equal(rawReport.runs[0].binding, "unbound-raw-profile");
    assert.equal(rawReport.runs[0].evidence, null);
    assert.equal(rawReport.runs[0].rawProfile.sha256,
      sha256(readFileSync(rawProfile)));
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
