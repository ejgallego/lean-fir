import assert from "node:assert/strict";
import fs from "node:fs";

const baselinePath = process.argv[2];
const getTagPath = process.argv[3];
const residentRuntimePath = process.argv[4];
const residentProjectionPath = process.argv[5];
const residentClosurePath = process.argv[6];
const residentMatchPath = process.argv[7];
const residentAllocatorPath = process.argv[8];
assert.ok(baselinePath && getTagPath && residentRuntimePath &&
  residentProjectionPath && residentClosurePath && residentMatchPath &&
  residentAllocatorPath,
  "usage: node check-resident-pretty-format.mjs " +
  "BASELINE.wasm GET_TAG.wasm RESIDENT_RUNTIME.wasm RESIDENT_PROJECTIONS.wasm " +
  "RESIDENT_CLOSURES.wasm RESIDENT_MATCHES.wasm RESIDENT_ALLOCATOR.wasm");

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
const residentClosures = readArtifact(residentClosurePath);
const residentMatches = readArtifact(residentMatchPath);
const residentAllocator = readArtifact(residentAllocatorPath);
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
assert.equal(operationCount(residentProjections, "closureProj"), 87,
  "resident-projection prettyM closure-projection inventory changed");
assert.equal(operationCount(residentClosures, "closureProj"), 0,
  "resident-closure prettyM retained semantic closure projections");
assert.equal(operationCount(residentClosures, "closureMatches"), 77,
  "resident-closure prettyM closure-match inventory changed");
assert.equal(operationCount(residentMatches, "closureMatches"), 0,
  "resident-match prettyM retained semantic closure matches");
assert.equal(operationCount(residentAllocator, "closureMatches"), 0,
  "resident-allocator prettyM regained semantic closure matches");
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
  functionImportCount(residentClosures) + 87,
  functionImportCount(residentProjections),
  "resident-closure prettyM did not remove exactly 87 function imports",
);
assert.equal(
  residentClosures.manifest.imports.length,
  functionImportCount(residentClosures),
  "resident-closure prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentMatches) + 77,
  functionImportCount(residentClosures),
  "resident-match prettyM did not remove exactly 77 function imports",
);
assert.equal(
  residentMatches.manifest.imports.length,
  functionImportCount(residentMatches),
  "resident-match prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentAllocator),
  functionImportCount(residentMatches),
  "resident allocator changed the semantic function-import frontier",
);
assert.equal(
  residentAllocator.manifest.imports.length,
  functionImportCount(residentAllocator),
  "resident-allocator prettyM descriptor and Wasm imports disagree",
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
assert.equal(
  residentClosures.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident-closure prettyM imports memory",
);
assert.equal(
  residentMatches.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident-match prettyM imports memory",
);
assert.equal(
  residentAllocator.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident-allocator prettyM imports memory",
);
for (const artifact of [
  getTagResident,
  residentRuntime,
  residentProjections,
  residentClosures,
  residentMatches,
  residentAllocator,
]) {
  assert.deepStrictEqual(
    artifact.manifest.closureDispatch,
    baseline.manifest.closureDispatch,
    "resident linking changed the stable closure-dispatch table",
  );
}
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
assert.ok(residentClosures.exports.some(({ name, kind }) =>
  name === residentClosures.manifest.entry && kind === "function"),
"resident-closure prettyM entry export is missing");
for (const name of [
  "fir_cproj_0_object",
  "fir_cproj_0_tobject",
  "fir_cproj_0_uint8",
  "fir_cproj_1_object",
  "fir_cproj_1_tobject",
  "fir_cproj_1_uint8",
  "fir_cproj_1_uint32",
  "fir_cproj_2_object",
  "fir_cproj_2_tobject",
  "fir_cproj_3_object",
  "fir_cproj_3_tobject",
  "fir_cproj_4_object",
]) {
  assert.ok(residentClosures.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident-closure prettyM helper export ${name} is missing`);
}
assert.ok(residentClosures.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident-closure prettyM memory export is missing");
assert.ok(residentMatches.exports.some(({ name, kind }) =>
  name === residentMatches.manifest.entry && kind === "function"),
"resident-match prettyM entry export is missing");
for (const descriptor of residentClosures.manifest.imports.filter(
  ({ operation }) => operation.kind === "closureMatches")) {
  const { function: target, arity, fixed } = descriptor.operation;
  const targetId = residentMatches.manifest.closureDispatch.indexOf(target);
  assert.ok(targetId >= 0, `resident-match target ${target} is absent from dispatch`);
  const name = `fir_cmatch_${targetId}_${arity}_${fixed}`;
  assert.ok(residentMatches.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident-match prettyM helper export ${name} is missing`);
}
assert.ok(residentMatches.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident-match prettyM memory export is missing");
for (const name of [
  "fir_heap_frontier",
  "fir_heap_set_frontier",
  "fir_heap_alloc",
  "fir_heap_store8",
  "fir_heap_store16",
  "fir_heap_store32",
  "fir_heap_store64",
]) {
  assert.ok(residentAllocator.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident-allocator prettyM helper export ${name} is missing`);
}
assert.ok(residentAllocator.exports.some(({ name, kind }) =>
  name === residentAllocator.manifest.entry && kind === "function"),
"resident-allocator prettyM entry export is missing");
assert.ok(residentAllocator.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident-allocator prettyM memory export is missing");

console.log(
  `PASS resident prettyM internalized getTag, isShared, projection, and match families, ` +
  `then installed its allocator ` +
  `(${functionImportCount(baseline)} → ${functionImportCount(getTagResident)} → ` +
  `${functionImportCount(residentRuntime)} → ` +
  `${functionImportCount(residentProjections)} → ` +
  `${functionImportCount(residentClosures)} → ` +
  `${functionImportCount(residentMatches)} → ` +
  `${functionImportCount(residentAllocator)} function imports)`,
);
