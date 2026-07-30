import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const reportPath = process.argv[2];
if (!reportPath) {
  throw new Error("usage: node test-concrete-readiness.mjs REPORT_JSON");
}

const report = JSON.parse(await readFile(reportPath, "utf8"));
assert.equal(report.version, 1);
assert.equal(report.summary.artifactFixtures, 44);
assert.equal(report.summary.artifactSuccessFixtures, 43);
assert.equal(report.summary.artifactExpectedFaultFixtures, 1);
assert.equal(report.summary.artifactRejectedFixtures, 0);
assert.equal(report.summary.readyArtifactFixtures, 44);
assert.equal(report.summary.artifactSwitchReady, true);
assert.equal(report.summary.sourceProbes, 15);
assert.equal(report.summary.readySourceProbes, 15);
assert.equal(report.summary.blockedSourceProbes, 0);
assert.equal(report.summary.sourceProbeSwitchReady, true);
assert.equal(report.summary.proofCoverageComplete, false);
assert.ok(!report.notClaimed.some((claim) => claim.includes("source probe")));
assert.ok(report.notClaimed.includes(
  "concrete execution of 30 ByteArray-backed shared validation products"));
for (const id of ["delete-fault", "reference-counting"]) {
  const fixture = report.artifactFixtures.find((item) => item.id === id);
  assert.equal(fixture?.status, "success");
  assert.equal(fixture?.ready, true);
}

const blocked = report.sourceProbes.filter((probe) => !probe.ready);
assert.deepStrictEqual(blocked, []);
assert.ok(report.sourceProbes.every((probe) => probe.blockers.length === 0));

assert.ok(report.imports.length > 0);
assert.equal(report.summary.importIdentities, report.imports.length);
assert.ok(report.imports.every((entry) => entry.coverage));
assert.ok(report.operations.some((operation) => operation.operationKind === "external" &&
  operation.coverage.domain === "external"));
assert.ok(report.operations.some((operation) => operation.operationKind === "stringLiteral" &&
  operation.coverage.runtimeOp === "literal"));
console.log("PASS fail-closed concrete artifact readiness report");
