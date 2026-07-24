import fs from "node:fs";
import { checkResidentGlobal } from "./resident-global-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-global.mjs PATH.wasm");
}

console.log(await checkResidentGlobal(fs.readFileSync(path)));
