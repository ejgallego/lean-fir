import fs from "node:fs";

import {
  checkResidentClosureMatches,
} from "./resident-closure-matches-client.mjs";

const artifactPath = process.argv[2];
if (!artifactPath) {
  throw new Error("usage: node run-resident-closure-matches.mjs ARTIFACT.wasm");
}

console.log(await checkResidentClosureMatches({
  bytes: fs.readFileSync(artifactPath),
  manifest: JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8")),
}));
