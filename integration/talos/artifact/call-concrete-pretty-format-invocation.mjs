import assert from "node:assert/strict";
import fs from "node:fs";

import {
  checkConcretePrettyFormatInvocation,
} from "./check-concrete-pretty-format-invocation.mjs";

const artifactPath = process.argv[2];
assert.ok(artifactPath,
  "usage: node call-concrete-pretty-format-invocation.mjs ARTIFACT.wasm");

const manifest = JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8"));
console.log(await checkConcretePrettyFormatInvocation({
  bytes: fs.readFileSync(artifactPath),
  manifest,
}));
