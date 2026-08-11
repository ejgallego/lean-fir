import fs from "node:fs";
import { checkResidentFixedWidth } from "./resident-fixed-width-client.mjs";

const path = process.argv[2];
if (!path) {
  throw new Error("usage: node run-resident-fixed-width.mjs <module.wasm>");
}

await checkResidentFixedWidth(fs.readFileSync(path));
console.log("PASS resident fixed-width operations");
