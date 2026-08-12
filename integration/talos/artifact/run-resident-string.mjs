import assert from "node:assert/strict";
import fs from "node:fs";

import { checkResidentString } from "./resident-string-client.mjs";

const artifactPath = process.argv[2];
assert.ok(artifactPath,
  "usage: node run-resident-string.mjs ARTIFACT.wasm [--require-usize-repr] [--require-of-list]");
const options = new Set(process.argv.slice(3));
const requireUSizeRepr = options.has("--require-usize-repr");
const requireOfList = options.has("--require-of-list");

console.log(await checkResidentString({
  bytes: fs.readFileSync(artifactPath),
  manifest: JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8")),
  requireUSizeRepr,
  requireOfList,
}));
