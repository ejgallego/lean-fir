import assert from "node:assert/strict";
import { test } from "node:test";

import { checkComparatorBuild } from "./check-current-prettyM-comparator.mjs";

const expected = { sourceCommit: "a".repeat(40), sourceDirty: false };
const build = {
  format: "fir-prettyM-package-metadata-v2",
  ...expected,
  functionImports: 0,
  memoryImports: 0,
  capabilities: { memoryOwner: "module" },
};

test("current self-contained comparator is accepted", () => {
  checkComparatorBuild(build, expected);
});

test("old commit and dirty-state mismatch are rejected", () => {
  assert.throws(() => checkComparatorBuild(
    { ...build, sourceCommit: "b".repeat(40) }, expected),
    /another FIR commit/);
  assert.throws(() => checkComparatorBuild(
    { ...build, sourceDirty: true }, expected),
    /worktree state/);
});

test("comparator import and memory contract cannot silently change", () => {
  assert.throws(() => checkComparatorBuild(
    { ...build, functionImports: 1 }, expected));
  assert.throws(() => checkComparatorBuild(
    { ...build, memoryImports: 1 }, expected));
  assert.throws(() => checkComparatorBuild(
    { ...build, capabilities: { memoryOwner: "host" } }, expected));
});
