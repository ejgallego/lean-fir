import fs from "node:fs";

import { checkResidentTrustedArraySet } from "./resident-array-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-trusted-array-set.mjs PATH.wasm");
}

console.log(await checkResidentTrustedArraySet(fs.readFileSync(path)));
