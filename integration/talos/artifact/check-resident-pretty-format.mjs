import assert from "node:assert/strict";
import fs from "node:fs";

const baselinePath = process.argv[2];
const getTagPath = process.argv[3];
const residentRuntimePath = process.argv[4];
assert.ok(baselinePath && getTagPath && residentRuntimePath,
  "usage: node check-resident-pretty-format.mjs " +
  "BASELINE.wasm GET_TAG.wasm RESIDENT_RUNTIME.wasm");

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
const getTagResident = readArtifact(getTagPath);
const residentRuntime = readArtifact(residentRuntimePath);
const operationCount = ({ manifest }, kind) =>
  manifest.imports.filter(({ operation }) => operation?.kind === kind).length;
const functionImportCount = ({ imports }) =>
  imports.filter(({ kind }) => kind === "function").length;

assert.equal(operationCount(baseline, "getTag"), 1,
  "baseline prettyM must expose exactly one semantic getTag import");
assert.equal(operationCount(baseline, "isShared"), 1,
  "baseline prettyM must expose exactly one semantic isShared import");
assert.equal(operationCount(getTagResident, "getTag"), 0,
  "resident prettyM retained a semantic getTag import");
assert.equal(operationCount(getTagResident, "isShared"), 1,
  "getTag-only prettyM unexpectedly removed isShared");
assert.equal(operationCount(residentRuntime, "getTag"), 0,
  "resident-runtime prettyM retained a semantic getTag import");
assert.equal(operationCount(residentRuntime, "isShared"), 0,
  "resident-runtime prettyM retained a semantic isShared import");
assert.equal(functionImportCount(getTagResident) + 1, functionImportCount(baseline),
  "getTag-only prettyM did not remove exactly one function import");
assert.equal(
  functionImportCount(residentRuntime) + 1,
  functionImportCount(getTagResident),
  "resident-runtime prettyM did not remove exactly one additional function import",
);
assert.equal(
  residentRuntime.manifest.imports.length,
  functionImportCount(residentRuntime),
  "resident-runtime prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  residentRuntime.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident-runtime prettyM imports memory",
);
assert.ok(residentRuntime.exports.some(({ name, kind }) =>
  name === residentRuntime.manifest.entry && kind === "function"),
"resident-runtime prettyM entry export is missing");
assert.ok(residentRuntime.exports.some(({ name, kind }) =>
  name === "fir_getTag" && kind === "function"),
"resident-runtime prettyM getTag helper export is missing");
assert.ok(residentRuntime.exports.some(({ name, kind }) =>
  name === "fir_isShared" && kind === "function"),
"resident-runtime prettyM isShared helper export is missing");
assert.ok(residentRuntime.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident-runtime prettyM memory export is missing");

console.log(
  `PASS resident prettyM internalized getTag and isShared ` +
  `(${functionImportCount(baseline)} → ${functionImportCount(getTagResident)} → ` +
  `${functionImportCount(residentRuntime)} function imports)`,
);
