import fs from "node:fs";
import { checkResidentAllocator } from "./resident-allocator-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-allocator.mjs PATH.wasm");
}

console.log(await checkResidentAllocator(fs.readFileSync(path)));
