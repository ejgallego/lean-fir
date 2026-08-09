import fs from "node:fs";
import { checkResidentArrays } from "./resident-array-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-arrays.mjs PATH.wasm");
}

await checkResidentArrays(fs.readFileSync(path));
console.log("PASS resident arrays");
