import fs from "node:fs";
import { checkResidentReadProjections } from "./resident-read-projections-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-read-projections.mjs PATH.wasm");
}

const result = await checkResidentReadProjections(
  fs.readFileSync(path),
  JSON.parse(fs.readFileSync(`${path}.json`, "utf8")),
);
console.log(result);
