import fs from "node:fs";
import { checkResidentLiterals } from "./resident-literal-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-literals.mjs PATH.wasm");
}

console.log(await checkResidentLiterals(fs.readFileSync(path)));
