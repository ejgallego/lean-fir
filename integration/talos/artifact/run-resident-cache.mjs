import fs from "node:fs";
import { checkResidentCache } from "./resident-cache-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-cache.mjs PATH.wasm");
}

await checkResidentCache(fs.readFileSync(path));
console.log("PASS resident cache");
