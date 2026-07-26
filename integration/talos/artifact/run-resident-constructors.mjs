import fs from "node:fs";
import { checkResidentConstructors } from "./resident-constructor-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-constructors.mjs PATH.wasm");
}

await checkResidentConstructors(fs.readFileSync(path));
console.log("PASS resident constructor allocation");
