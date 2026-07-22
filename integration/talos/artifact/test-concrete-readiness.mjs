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
assert.equal(report.summary.sourceProbes, 13);
assert.equal(report.summary.readySourceProbes, 10);
assert.equal(report.summary.blockedSourceProbes, 3);
assert.equal(report.summary.sourceProbeSwitchReady, false);
assert.equal(report.summary.proofCoverageComplete, false);
for (const id of ["delete-fault", "reference-counting"]) {
  const fixture = report.artifactFixtures.find((item) => item.id === id);
  assert.equal(fixture?.status, "success");
  assert.equal(fixture?.ready, true);
}

const blocked = report.sourceProbes.filter((probe) => !probe.ready);
assert.deepStrictEqual(blocked.map((probe) => probe.id), [
  "source-pretty-format",
  "source-pretty-format-coverage",
  "source-pretty-format-module",
]);
const expectedMissingExternals = [
  "Int.add",
  "Int.decLt",
  "Int.natAbs",
  "Int.ofNat",
  "Int.sub",
  "Nat.add",
  "Nat.decEq",
  "Nat.decLe",
  "Nat.decLt",
  "Nat.sub",
  "String.Internal.append",
  "String.Internal.extract",
  "String.Internal.length",
  "String.Internal.next",
  "String.Internal.offsetOfPos",
  "String.Internal.posOf",
  "String.Internal.pushn",
  "String.utf8ByteSize",
  "instInhabitedOfMonad._redArg",
  "panicCore",
];
for (const probe of blocked) {
  const externalBlocker = probe.blockers.find((item) =>
    item.kind === "external-implementations");
  assert.deepStrictEqual(externalBlocker?.declarations, expectedMissingExternals,
    `${probe.id} concrete external blocker drifted`);
}
assert.deepStrictEqual(
  blocked.find((probe) => probe.id === "source-pretty-format-coverage")
    .blockers.map((item) => item.kind),
  ["initial-runtime", "external-implementations"],
);
for (const probe of blocked.filter((item) => item.id !== "source-pretty-format-coverage")) {
  assert.deepStrictEqual(probe.blockers.map((item) => item.kind),
    ["external-implementations"]);
}

assert.ok(report.imports.length > 0);
assert.equal(report.summary.importIdentities, report.imports.length);
assert.ok(report.imports.every((entry) => entry.coverage));
assert.ok(report.operations.some((operation) => operation.operationKind === "external" &&
  operation.coverage.domain === "external"));
assert.ok(report.operations.some((operation) => operation.operationKind === "stringLiteral" &&
  operation.coverage.runtimeOp === "literal"));
console.log("PASS fail-closed concrete artifact readiness report");
