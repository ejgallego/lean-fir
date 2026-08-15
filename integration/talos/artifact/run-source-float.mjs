import fs from "node:fs/promises";

import { checkSourceFloatConversions } from "./source-float-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-source-float.mjs <artifact.wasm>");
}

const [bytes, oracleText] = await Promise.all([
  fs.readFile(path),
  fs.readFile(`${path}.oracle.json`, "utf8"),
]);

console.log(await checkSourceFloatConversions(bytes, JSON.parse(oracleText)));
