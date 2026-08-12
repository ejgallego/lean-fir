import fs from "node:fs";
import { checkResidentPlatform } from "./resident-platform-client.mjs";

const path = process.argv[2];
if (!path) {
  throw new Error("usage: node run-resident-platform.mjs <module.wasm>");
}

await checkResidentPlatform(fs.readFileSync(path));
console.log("PASS resident platform operations");
