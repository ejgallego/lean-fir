import assert from "node:assert/strict";
import fs from "node:fs";

import {
  checkResidentFallbacks,
} from "./resident-fallback-client.mjs";

const artifactPath = process.argv[2];
assert.ok(artifactPath,
  "usage: node run-resident-fallbacks.mjs ARTIFACT.wasm");

console.log(await checkResidentFallbacks({
  bytes: fs.readFileSync(artifactPath),
  manifest: JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8")),
}));
