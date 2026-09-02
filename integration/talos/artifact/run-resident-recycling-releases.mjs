import fs from "node:fs";
import { checkResidentRecyclingReleases } from
  "./resident-recycling-release-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error(
    "usage: node run-resident-recycling-releases.mjs PATH.wasm");
}

console.log(await checkResidentRecyclingReleases(fs.readFileSync(path)));
