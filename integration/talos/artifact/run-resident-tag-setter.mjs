import fs from "node:fs";
import { checkResidentTagSetter } from "./resident-tag-setter-client.mjs";

const path = process.argv[2];
if (!path) {
  throw new Error(
    "usage: node run-resident-tag-setter.mjs RESIDENT-TAG-SETTER.wasm",
  );
}

console.log(await checkResidentTagSetter(fs.readFileSync(path)));
