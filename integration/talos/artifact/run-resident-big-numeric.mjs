import fs from "node:fs/promises";

import { checkResidentBigNumeric } from "./resident-big-numeric-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-big-numeric.mjs <artifact.wasm>");
}

const [bytes, manifestText] = await Promise.all([
  fs.readFile(path),
  fs.readFile(`${path}.json`, "utf8"),
]);

console.log(await checkResidentBigNumeric({
  bytes,
  manifest: JSON.parse(manifestText),
}));
