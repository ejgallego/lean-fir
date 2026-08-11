import fs from "node:fs";
import { checkResidentByteArray } from "./resident-byte-array-client.mjs";

const path = process.argv[2];
if (!path) {
  throw new Error("usage: node run-resident-byte-array.mjs <module.wasm>");
}

await checkResidentByteArray(fs.readFileSync(path));
console.log("PASS resident packed ByteArrays");
