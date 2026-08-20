import assert from "node:assert/strict";
import {
  chmodSync,
  mkdirSync,
  mkdtempSync,
} from "node:fs";
import { dirname, isAbsolute, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const toolingDirectory = dirname(fileURLToPath(import.meta.url));
const repositoryRoot = resolve(toolingDirectory, "..");
const dependencyRoot = join(repositoryRoot, ".deps");

function isDescendant(parent, child) {
  const path = relative(parent, child);
  return path !== "" && !path.startsWith("..") && !isAbsolute(path);
}

export function toolingTemporaryRoot(
  configured = process.env.FIR_TOOLING_TMPDIR,
) {
  const root = resolve(configured ?? join(dependencyRoot, "tooling-tmp"));
  assert(isDescendant(dependencyRoot, root),
    `FIR_TOOLING_TMPDIR must be below ${dependencyRoot}`);
  mkdirSync(root, { recursive: true, mode: 0o700 });
  chmodSync(root, 0o700);
  return root;
}

export function makeToolingTemporaryDirectory(prefix) {
  assert.match(prefix, /^[A-Za-z0-9][A-Za-z0-9._-]*-$/,
    "tooling temporary prefix must be a filename ending in '-'");
  return mkdtempSync(join(toolingTemporaryRoot(), prefix));
}
