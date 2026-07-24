import fs from "node:fs";
import { checkResidentIsShared } from "./resident-is-shared-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-is-shared.mjs PATH.wasm");
}

const result = await checkResidentIsShared(
  fs.readFileSync(path),
  JSON.parse(fs.readFileSync(`${path}.json`, "utf8")),
);
console.log(result);
