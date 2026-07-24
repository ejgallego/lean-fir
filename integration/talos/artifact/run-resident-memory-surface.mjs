import fs from "node:fs";
import {
  checkResidentMemorySurface,
} from "./resident-memory-surface-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-memory-surface.mjs PATH.wasm");
}

console.log(await checkResidentMemorySurface(fs.readFileSync(path)));
