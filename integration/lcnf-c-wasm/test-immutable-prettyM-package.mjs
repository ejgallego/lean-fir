import assert from "node:assert/strict";
import {
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { join } from "node:path";

import { publishPreparedPrettyM } from "./publish-prettyM-emscripten.mjs";

const [builtDirectory, repoRoot] = process.argv.slice(2);
if (builtDirectory === undefined || repoRoot === undefined || process.argv.length !== 4) {
  throw new Error("usage: node test-immutable-prettyM-package.mjs <build-dir> <FIR-root>");
}

const scratch = mkdtempSync(join(repoRoot, ".deps/lcnf-c-wasm/prettyM-publish-test-"));
try {
  const current = join(scratch, "prettyM-current");
  const first = publishPreparedPrettyM({ builtDirectory, currentLink: current });
  const firstInode = statSync(first).ino;
  const firstChecksums = readFileSync(join(first, "SHA256SUMS"), "utf8");
  assert.equal(lstatSync(current).isSymbolicLink(), true);
  assert.equal(realpathSync(current), first);

  const repeated = publishPreparedPrettyM({ builtDirectory, currentLink: current });
  assert.equal(repeated, first, "same bytes must reuse the same release");
  assert.equal(statSync(first).ino, firstInode,
    "repeat publication must not rewrite the existing release");
  assert.equal(readFileSync(join(first, "SHA256SUMS"), "utf8"), firstChecksums);

  writeFileSync(join(first, "README.md"), "tampered release\n");
  assert.throws(() => publishPreparedPrettyM({ builtDirectory, currentLink: current }),
    /immutable package .* differs at README.md/,
  "same-identity different bytes must fail closed");
  assert.equal(realpathSync(current), first,
    "failed collision must not move the current pointer");

  const legacy = join(scratch, "legacy-current");
  mkdirSync(legacy);
  assert.throws(() => publishPreparedPrettyM({ builtDirectory, currentLink: legacy }),
    /refusing to replace a legacy package directory/);
  assert.equal(lstatSync(legacy).isDirectory(), true);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}

console.log("PASS immutable C prettyM repeat, collision, and legacy preservation");
