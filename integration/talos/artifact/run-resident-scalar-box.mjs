import fs from "node:fs";
import { checkResidentScalarBox } from "./resident-scalar-box-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-scalar-box.mjs PATH.wasm");
}

await checkResidentScalarBox(fs.readFileSync(path));
console.log("PASS resident scalar boxing");
