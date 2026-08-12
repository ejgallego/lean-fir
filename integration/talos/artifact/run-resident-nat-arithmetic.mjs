import fs from "node:fs/promises";

import { checkResidentNatArithmetic } from "./resident-nat-arithmetic-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-nat-arithmetic.mjs <artifact.wasm>");
}

const [bytes, manifestText] = await Promise.all([
  fs.readFile(path),
  fs.readFile(`${path}.json`, "utf8"),
]);

console.log(await checkResidentNatArithmetic({
  bytes,
  manifest: JSON.parse(manifestText),
}));
