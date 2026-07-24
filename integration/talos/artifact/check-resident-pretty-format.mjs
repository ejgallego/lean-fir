import assert from "node:assert/strict";
import fs from "node:fs";

const baselinePath = process.argv[2];
const residentPath = process.argv[3];
assert.ok(baselinePath && residentPath,
  "usage: node check-resident-pretty-format.mjs BASELINE.wasm RESIDENT.wasm");

function readArtifact(path) {
  const bytes = fs.readFileSync(path);
  const manifest = JSON.parse(fs.readFileSync(`${path}.json`, "utf8"));
  assert.ok(WebAssembly.validate(bytes), `${path} failed WebAssembly validation`);
  const module = new WebAssembly.Module(bytes);
  return {
    bytes,
    manifest,
    imports: WebAssembly.Module.imports(module),
    exports: WebAssembly.Module.exports(module),
  };
}

const baseline = readArtifact(baselinePath);
const resident = readArtifact(residentPath);
const getTagCount = ({ manifest }) =>
  manifest.imports.filter(({ operation }) => operation?.kind === "getTag").length;
const functionImportCount = ({ imports }) =>
  imports.filter(({ kind }) => kind === "function").length;

assert.equal(getTagCount(baseline), 1,
  "baseline prettyM must expose exactly one semantic getTag import");
assert.equal(getTagCount(resident), 0,
  "resident prettyM retained a semantic getTag import");
assert.equal(functionImportCount(resident) + 1, functionImportCount(baseline),
  "resident prettyM did not remove exactly one function import");
assert.equal(resident.manifest.imports.length, functionImportCount(resident),
  "resident prettyM descriptor and Wasm imports disagree");
assert.equal(resident.imports.filter(({ kind }) => kind === "memory").length, 0,
  "resident prettyM imports memory");
assert.ok(resident.exports.some(({ name, kind }) =>
  name === resident.manifest.entry && kind === "function"),
"resident prettyM entry export is missing");
assert.ok(resident.exports.some(({ name, kind }) =>
  name === "fir_getTag" && kind === "function"),
"resident prettyM getTag helper export is missing");
assert.ok(resident.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident prettyM memory export is missing");

console.log(
  `PASS resident prettyM internalized getTag ` +
  `(${functionImportCount(baseline)} → ${functionImportCount(resident)} function imports)`,
);
