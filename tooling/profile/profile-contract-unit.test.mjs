import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";

import {
  profileClaimsSchema,
  validateProfileAggregateContract,
  validateProfileEvidenceContract,
  validateProfileLifecycle,
  validateSampledProfileContract,
} from "./profile-contract.mjs";
import {
  makeProfileAggregateContractFixture,
  makeProfileContractFixture,
} from "./test/profile-contract-fixture.mjs";

const cases = JSON.parse(readFileSync(new URL(
  "./test/profile-contract-cases.json", import.meta.url)));

function setPath(value, path, replacement) {
  let cursor = value;
  for (const component of path.slice(0, -1)) cursor = cursor[component];
  cursor[path.at(-1)] = replacement;
}

function profileLifecycle() {
  return { moduleInstance: "fresh-instance-per-profile" };
}

function fixture(kind) {
  if (kind === "profile") return makeProfileContractFixture();
  if (kind === "aggregate") return makeProfileAggregateContractFixture();
  if (kind === "profile-lifecycle") return profileLifecycle();
  throw new Error(`unknown profile-contract fixture ${kind}`);
}

test("derives fail-closed v2 profile claims from the intact FIR packet", () => {
  const packet = makeProfileContractFixture();
  const claims = validateProfileEvidenceContract(packet);
  assert.deepEqual(claims, {
    schemaVersion: profileClaimsSchema,
    sourceContract: {
      kind: "source-report-contract",
      id: "fir.sampled-profile/v2",
    },
    artifactSha256: "a".repeat(64),
    symbolMapSha256: "b".repeat(64),
    comparabilityKey: packet.comparability.key,
    qualityClassification: "checked-diagnostic",
    workloadReceipt: {
      kind: "fir.profile-workload-receipt/v1",
      id: "fir/profile-contract-fixture",
      sha256: "d".repeat(64),
    },
    instancePolicy: "fresh-instance-per-profile",
    timeBasis: "sampled-self-time",
    unit: "microseconds",
    window: "steady-only",
    symbolization: {
      kind: "final-wasm-function-index",
      coverage: "all-wasm-self-samples",
    },
  });
  assert.equal(validateSampledProfileContract(packet).artifactSha256,
    claims.artifactSha256);
  assert.equal(validateProfileLifecycle(claims, profileLifecycle()),
    "fresh-instance-per-profile");
});

test("derives the same binding surface from a comparable v3 aggregate", () => {
  const packet = makeProfileAggregateContractFixture();
  const claims = validateProfileAggregateContract(packet);
  assert.equal(claims.sourceContract.id,
    "fir.sampled-profile-aggregate/v3");
  assert.equal(claims.artifactSha256, "a".repeat(64));
  assert.equal(claims.symbolMapSha256, "b".repeat(64));
  assert.equal(claims.comparabilityKey, packet.comparability.key);
  assert.equal(claims.qualityClassification, "comparable-diagnostic");
  assert.equal(claims.instancePolicy, "fresh-instance-per-profile");
  assert.equal(validateSampledProfileContract(packet).workloadReceipt.sha256,
    "d".repeat(64));
});

test("portable negative cases reject semantic claim contradictions", () => {
  assert.equal(cases.schemaVersion,
    "fir.sampled-profile-contract-cases/v1");
  for (const case_ of cases.cases) {
    if (case_.fixture === "profile-lifecycle") {
      const claims = validateProfileEvidenceContract(
        makeProfileContractFixture());
      const lifecycle = fixture(case_.fixture);
      setPath(lifecycle, case_.operation.path, case_.operation.value);
      assert.throws(() => validateProfileLifecycle(claims, lifecycle),
        new RegExp(case_.expectError));
      continue;
    }
    const packet = fixture(case_.fixture);
    setPath(packet, case_.operation.path, case_.operation.value);
    assert.throws(() => validateSampledProfileContract(packet),
      new RegExp(case_.expectError));
  }
});

test("rejects recomputed comparability and aggregate receipt drift", () => {
  const profile = makeProfileContractFixture();
  profile.workload.metadata.id = "changed-profile-contract-fixture";
  assert.throws(() => validateProfileEvidenceContract(profile),
    /comparability does not match its packet contents/);

  const aggregate = makeProfileAggregateContractFixture();
  aggregate.runs[1].workload.receipt.instancePolicy =
    "fresh-instance-per-other-profile";
  assert.throws(() => validateProfileAggregateContract(aggregate),
    /runs disagree on workload receipt or instance policy/);
});
