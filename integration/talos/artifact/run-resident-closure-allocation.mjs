import fs from "node:fs";
import {
  checkResidentClosureAllocation,
} from "./resident-closure-allocation-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error(
    "usage: node run-resident-closure-allocation.mjs PATH.wasm",
  );
}

await checkResidentClosureAllocation(fs.readFileSync(path));
console.log("PASS resident closure allocation");
