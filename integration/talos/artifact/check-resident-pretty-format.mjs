import assert from "node:assert/strict";
import fs from "node:fs";

const baselinePath = process.argv[2];
const getTagPath = process.argv[3];
const residentRuntimePath = process.argv[4];
const residentProjectionPath = process.argv[5];
assert.ok(baselinePath && getTagPath && residentRuntimePath && residentProjectionPath,
  "usage: node check-resident-pretty-format.mjs " +
  "BASELINE.wasm GET_TAG.wasm RESIDENT_RUNTIME.wasm RESIDENT_PROJECTIONS.wasm");

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
const residentProjections = readArtifact(residentProjectionPath);
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
assert.equal(operationCount(residentRuntime, "objectProj"), 4,
  "resident-runtime prettyM object-projection inventory changed");
assert.equal(operationCount(residentRuntime, "scalarProj"), 4,
  "resident-runtime prettyM scalar-projection inventory changed");
assert.equal(operationCount(residentProjections, "getTag"), 0,
  "resident-projection prettyM retained a semantic getTag import");
assert.equal(operationCount(residentProjections, "isShared"), 0,
  "resident-projection prettyM retained a semantic isShared import");
assert.equal(operationCount(residentProjections, "objectProj"), 0,
  "resident-projection prettyM retained semantic object projections");
assert.equal(operationCount(residentProjections, "scalarProj"), 0,
  "resident-projection prettyM retained semantic scalar projections");
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
  functionImportCount(residentProjections) + 8,
  functionImportCount(residentRuntime),
  "resident-projection prettyM did not remove exactly eight function imports",
);
assert.equal(
  residentProjections.manifest.imports.length,
  functionImportCount(residentProjections),
  "resident-projection prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  residentRuntime.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident-runtime prettyM imports memory",
);
assert.equal(
  residentProjections.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident-projection prettyM imports memory",
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
assert.ok(residentProjections.exports.some(({ name, kind }) =>
  name === residentProjections.manifest.entry && kind === "function"),
"resident-projection prettyM entry export is missing");
for (const name of [
  "fir_getTag",
  "fir_isShared",
  "fir_oproj_0_object",
  "fir_oproj_0_tobject",
  "fir_oproj_1_tobject",
  "fir_oproj_2_tobject",
  "fir_sproj_u8_0_0",
  "fir_sproj_u8_1_0",
  "fir_sproj_u8_1_1",
  "fir_sproj_u8_2_0",
]) {
  assert.ok(residentProjections.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident-projection prettyM helper export ${name} is missing`);
}
assert.ok(residentProjections.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident-projection prettyM memory export is missing");

console.log(
  `PASS resident prettyM internalized getTag, isShared, and read projections ` +
  `(${functionImportCount(baseline)} → ${functionImportCount(getTagResident)} → ` +
  `${functionImportCount(residentRuntime)} → ` +
  `${functionImportCount(residentProjections)} function imports)`,
);
