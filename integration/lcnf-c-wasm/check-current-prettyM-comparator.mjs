import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";

export function checkComparatorBuild(build, expected) {
  assert.equal(build?.format, "fir-prettyM-package-metadata-v2");
  assert.equal(build.sourceCommit, expected.sourceCommit,
    "FIR-native comparator comes from another FIR commit");
  assert.equal(build.sourceDirty, expected.sourceDirty,
    "FIR-native comparator does not describe this FIR worktree state");
  assert.equal(build.functionImports, 0);
  assert.equal(build.memoryImports, 0);
  assert.equal(build.capabilities?.memoryOwner, "module");
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const [buildPath, repoRoot] = process.argv.slice(2);
  if (buildPath === undefined || repoRoot === undefined || process.argv.length !== 4) {
    throw new Error("usage: node check-current-prettyM-comparator.mjs <BUILD.json> <FIR-root>");
  }
  const build = JSON.parse(await readFile(buildPath, "utf8"));
  const sourceCommit = execFileSync("git", ["-C", repoRoot, "rev-parse", "HEAD"],
    { encoding: "utf8" }).trim();
  const sourceDirty = execFileSync("git", ["-C", repoRoot, "status", "--porcelain"],
    { encoding: "utf8" }).trim() !== "";
  checkComparatorBuild(build, { sourceCommit, sourceDirty });
}
