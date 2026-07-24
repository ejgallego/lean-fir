import fs from "node:fs";
import {
  checkResidentClosureProjections,
} from "./resident-closure-projections-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-closure-projections.mjs PATH.wasm");
}

const result = await checkResidentClosureProjections(
  fs.readFileSync(path),
  JSON.parse(fs.readFileSync(`${path}.json`, "utf8")),
);
console.log(result);
