import fs from "node:fs";
import {
  checkResidentClosureAllocation,
} from "./resident-closure-allocation-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error(
    "usage: node run-resident-closure-allocation.mjs PATH.wasm [REFERENCE.wasm]",
  );
}

await checkResidentClosureAllocation(fs.readFileSync(path),
  process.argv[3] === undefined ? undefined : fs.readFileSync(process.argv[3]));
console.log("PASS resident closure allocation");
