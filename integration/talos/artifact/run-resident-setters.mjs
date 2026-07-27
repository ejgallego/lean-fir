import fs from "node:fs";
import { checkResidentSetters } from "./resident-setter-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-setters.mjs PATH.wasm");
}

await checkResidentSetters(fs.readFileSync(path));
console.log("PASS resident setters");
