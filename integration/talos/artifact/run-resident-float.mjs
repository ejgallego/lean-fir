import { readFile } from "node:fs/promises";
import { checkResidentFloat } from "./resident-float-client.mjs";

const [path] = process.argv.slice(2);
if (!path) throw new Error("usage: node run-resident-float.mjs <module.wasm>");

await checkResidentFloat(await readFile(path));
console.log("resident Float checks passed");
