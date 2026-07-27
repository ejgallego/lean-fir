import fs from "node:fs";
import { checkResidentIncrements } from "./resident-increment-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-increments.mjs PATH.wasm");
}

await checkResidentIncrements(fs.readFileSync(path));
console.log("PASS resident increments");
