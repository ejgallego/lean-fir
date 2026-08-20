import assert from "node:assert/strict";
import { rmSync, statSync } from "node:fs";
import { isAbsolute, relative, resolve } from "node:path";
import test from "node:test";

import {
  makeToolingTemporaryDirectory,
  toolingTemporaryRoot,
} from "./worktree-temp.mjs";

test("tooling scratch stays in the active worktree dependency root", () => {
  const root = toolingTemporaryRoot();
  const dependencyRoot = resolve(import.meta.dirname, "..", ".deps");
  const rootRelative = relative(dependencyRoot, root);
  assert(rootRelative !== "" && !rootRelative.startsWith("..") &&
    !isAbsolute(rootRelative));
  assert.equal(statSync(root).mode & 0o777, 0o700);

  const directory = makeToolingTemporaryDirectory("fir-tooling-test-");
  try {
    const temporaryRelative = relative(root, directory);
    assert(temporaryRelative !== "" && !temporaryRelative.startsWith("..") &&
      !isAbsolute(temporaryRelative));
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

test("tooling scratch rejects roots outside the worktree dependency root",
  () => {
    assert.throws(() => toolingTemporaryRoot("/tmp/fir-tooling"),
      /must be below/);
  });
