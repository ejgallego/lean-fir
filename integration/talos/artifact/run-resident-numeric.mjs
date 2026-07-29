import assert from "node:assert/strict";
import fs from "node:fs";

import { checkResidentNumeric } from "./resident-numeric-client.mjs";

const artifactPath = process.argv[2];
assert.ok(artifactPath,
  "usage: node run-resident-numeric.mjs ARTIFACT.wasm");

console.log(await checkResidentNumeric({
  bytes: fs.readFileSync(artifactPath),
  manifest: JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8")),
}));
