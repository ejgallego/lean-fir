import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  existsSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { join, resolve } from "node:path";
import test from "node:test";

import { makeToolingTemporaryDirectory } from "../worktree-temp.mjs";
import { makeCapture, makeSidecar } from "../wasm/function-index-lib.mjs";
import {
  profileEvidenceSchema,
  runNodeProfile,
} from "./node-profile-lib.mjs";

const binaryen = process.env.FIR_BINARYEN_DIR;
assert.equal(typeof binaryen, "string",
  "FIR_BINARYEN_DIR must name the pinned Binaryen bin directory");
const fixture = resolve(import.meta.dirname, "test/profile-fixture.wat");
const workload = resolve(import.meta.dirname, "test/fixture-workload.mjs");
const profileTool = resolve(import.meta.dirname, "node-profile.mjs");

function sha256(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

function buildFixture(directory) {
  const wasmPath = join(directory, "fixture.wasm");
  const sidecarPath = join(directory, "fixture.wasm.functions.json");
  execFileSync(join(binaryen, "wasm-as"), [fixture, "-o", wasmPath]);
  const bytes = readFileSync(wasmPath);
  const capture = makeCapture(bytes, {
    functions: ["Fixture.leaf", "Fixture.entry"],
    sourceFunctions: ["Fixture.leaf", "Fixture.entry"],
  });
  const map = capture.identities.map(({ index, token }) =>
    `${index}:${token}`).join("\n");
  const sidecar = makeSidecar(bytes, capture, map,
    "digraph call {\n  \"1\" -> \"0\";\n}\n", {
      artifactFile: "fixture.wasm",
    });
  writeFileSync(sidecarPath, `${JSON.stringify(sidecar)}\n`);
  return { wasmPath, sidecarPath };
}

test("CLI profiles only checked steady work and binds immutable evidence",
  () => {
    const directory = makeToolingTemporaryDirectory("fir-node-profile-");
    try {
      const { wasmPath, sidecarPath } = buildFixture(directory);
      const outputDirectory = join(directory, "profile");
      const wasmBefore = readFileSync(wasmPath);
      const sidecarBefore = readFileSync(sidecarPath);
      const workloadBefore = readFileSync(workload);
      const evidencePath = execFileSync(process.execPath, [
        profileTool,
        "--wasm", wasmPath,
        "--sidecar", sidecarPath,
        "--workload", workload,
        "--out-dir", outputDirectory,
        "--sampling-interval-micros", "100",
      ], { encoding: "utf8" }).trim();
      const evidence = JSON.parse(readFileSync(evidencePath, "utf8"));
      const rawPath = join(outputDirectory, evidence.rawProfile.file);
      const rawBytes = readFileSync(rawPath);
      assert.equal(evidence.schemaVersion, profileEvidenceSchema);
      assert.deepEqual(evidence.observations, {
        firstCall: { result: 0 },
        warmup: { result: 0, rounds: 1000 },
        steady: { result: 0, rounds: 50_000_000 },
      });
      for (const value of Object.values(evidence.phases)) {
        assert(Number.isFinite(value) && value >= 0);
      }
      assert(evidence.phases.steadyProfiledMs > 0);
      assert(evidence.phases.totalMs >= evidence.phases.steadyProfiledMs);
      assert.equal(evidence.summary.window.method,
        "phase-overlap-time-deltas/v1");
      assert(evidence.summary.resolvedWasmMicros > 0,
        "expected at least one steady Wasm sample");
      assert.equal(evidence.summary.unresolvedWasmMicros, 0);
      assert.equal(evidence.rawProfile.sha256, sha256(rawBytes));
      assert.equal(rawBytes.at(-1), 10);
      assert.deepEqual(readFileSync(wasmPath), wasmBefore);
      assert.deepEqual(readFileSync(sidecarPath), sidecarBefore);
      assert.deepEqual(readFileSync(workload), workloadBefore);
      assert.throws(() => execFileSync(process.execPath, [
        profileTool,
        "--wasm", wasmPath,
        "--sidecar", sidecarPath,
        "--workload", workload,
        "--out-dir", outputDirectory,
      ], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }),
      (error) => error.stderr.includes("profile output directory already exists"));
      assert.equal(sha256(readFileSync(evidencePath)),
        sha256(Buffer.from(`${JSON.stringify(evidence, null, 2)}\n`)),
      "rejected reuse must preserve existing evidence");
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  });

test("unchecked steady failure produces no partial evidence", async () => {
  const directory = makeToolingTemporaryDirectory(
    "fir-node-profile-fail-");
  try {
    const { wasmPath, sidecarPath } = buildFixture(directory);
    const badWorkload = join(directory, "bad-workload.mjs");
    const outputDirectory = join(directory, "profile");
    writeFileSync(badWorkload, [
      "export async function setup({ wasmBytes }) {",
      "  const { instance } = await WebAssembly.instantiate(wasmBytes);",
      "  return instance.exports['fixture.entry'];",
      "}",
      "export async function firstCall(entry) {",
      "  return { ok: entry(1) === 0 };",
      "}",
      "export async function steady(entry) {",
      "  entry(1);",
      "  return { ok: false };",
      "}",
      "",
    ].join("\n"));
    await assert.rejects(() => runNodeProfile({
      wasmPath,
      sidecarPath,
      workloadPath: badWorkload,
      outputDirectory,
      samplingIntervalMicros: 100,
    }), /steady must return an object with ok: true/);
    assert.equal(existsSync(outputDirectory), false,
      "failed profiles must not publish partial evidence");
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
