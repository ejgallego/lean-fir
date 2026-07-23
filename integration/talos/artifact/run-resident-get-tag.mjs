import fs from "node:fs";
import { checkResidentGetTag } from "./resident-get-tag-client.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-get-tag.mjs PATH.wasm");
}

const result = await checkResidentGetTag(
  fs.readFileSync(path),
  JSON.parse(fs.readFileSync(`${path}.json`, "utf8")),
);
console.log(result);
