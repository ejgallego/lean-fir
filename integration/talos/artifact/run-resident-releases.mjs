import fs from "node:fs";
import { checkResidentReleases } from "./resident-release-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-releases.mjs PATH.wasm");
}

await checkResidentReleases(fs.readFileSync(path));
console.log("PASS resident releases");
