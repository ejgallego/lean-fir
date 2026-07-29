import assert from "node:assert/strict";
import fs from "node:fs";

const baselinePath = process.argv[2];
const getTagPath = process.argv[3];
const residentRuntimePath = process.argv[4];
const residentProjectionPath = process.argv[5];
const residentClosurePath = process.argv[6];
const residentMatchPath = process.argv[7];
const residentAllocatorPath = process.argv[8];
const residentConstructorPath = process.argv[9];
const residentNaturalPath = process.argv[10];
const residentPartialApplicationPath = process.argv[11];
const residentSetterPath = process.argv[12];
const residentIncrementPath = process.argv[13];
const residentReleasePath = process.argv[14];
const styledReleasePath = process.argv[15];
const styledTagSetterPath = process.argv[16];
const residentCachePath = process.argv[17];
const styledCachePath = process.argv[18];
const residentNumericPath = process.argv[19];
const styledNumericPath = process.argv[20];
const residentStringPath = process.argv[21];
const styledStringPath = process.argv[22];
const residentClosedPath = process.argv[23];
const styledClosedPath = process.argv[24];
assert.ok(baselinePath && getTagPath && residentRuntimePath &&
  residentProjectionPath && residentClosurePath && residentMatchPath &&
  residentAllocatorPath && residentConstructorPath && residentNaturalPath &&
  residentPartialApplicationPath && residentSetterPath &&
  residentIncrementPath && residentReleasePath && styledReleasePath &&
  styledTagSetterPath && residentCachePath && styledCachePath &&
  residentNumericPath && styledNumericPath &&
  residentStringPath && styledStringPath &&
  residentClosedPath && styledClosedPath,
  "usage: node check-resident-pretty-format.mjs " +
  "BASELINE.wasm GET_TAG.wasm RESIDENT_RUNTIME.wasm RESIDENT_PROJECTIONS.wasm " +
  "RESIDENT_CLOSURES.wasm RESIDENT_MATCHES.wasm RESIDENT_ALLOCATOR.wasm " +
  "RESIDENT_CONSTRUCTORS.wasm RESIDENT_NATURALS.wasm " +
  "RESIDENT_PARTIAL_APPLICATIONS.wasm RESIDENT_SETTERS.wasm " +
  "RESIDENT_INCREMENTS.wasm RESIDENT_RELEASES.wasm " +
  "STYLED_RELEASES.wasm STYLED_TAG_SETTERS.wasm " +
  "RESIDENT_CACHE.wasm STYLED_CACHE.wasm " +
  "RESIDENT_NUMERIC.wasm STYLED_NUMERIC.wasm " +
  "RESIDENT_STRING.wasm STYLED_STRING.wasm " +
  "RESIDENT_CLOSED.wasm STYLED_CLOSED.wasm");

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
const residentConstructors = readArtifact(residentConstructorPath);
const residentNaturals = readArtifact(residentNaturalPath);
const residentPartialApplications =
  readArtifact(residentPartialApplicationPath);
const residentSetters = readArtifact(residentSetterPath);
const residentIncrements = readArtifact(residentIncrementPath);
const residentReleases = readArtifact(residentReleasePath);
const styledReleases = readArtifact(styledReleasePath);
const styledTagSetters = readArtifact(styledTagSetterPath);
const residentCache = readArtifact(residentCachePath);
const styledCache = readArtifact(styledCachePath);
const residentNumeric = readArtifact(residentNumericPath);
const styledNumeric = readArtifact(styledNumericPath);
const residentString = readArtifact(residentStringPath);
const styledString = readArtifact(styledStringPath);
const residentClosed = readArtifact(residentClosedPath);
const styledClosed = readArtifact(styledClosedPath);
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
assert.equal(operationCount(residentAllocator, "allocCtor"), 23,
  "resident-allocator prettyM constructor inventory changed");
assert.equal(operationCount(residentConstructors, "allocCtor"), 0,
  "resident-constructor prettyM retained constructor imports");
assert.equal(operationCount(residentConstructors, "naturalLiteral"), 2,
  "resident-constructor prettyM natural-literal inventory changed");
assert.equal(operationCount(residentConstructors, "stringLiteral"), 4,
  "resident-constructor prettyM string-literal inventory changed");
assert.equal(operationCount(residentNaturals, "naturalLiteral"), 0,
  "resident-Natural prettyM retained supported natural literals");
assert.equal(operationCount(residentNaturals, "stringLiteral"), 4,
  "resident-Natural prettyM moved strings across the host boundary");
assert.equal(operationCount(residentNaturals, "partialApply"), 87,
  "resident-Natural prettyM partial-application inventory changed");
assert.equal(operationCount(residentPartialApplications, "partialApply"), 0,
  "resident partial-application prettyM retained closure allocations");
assert.equal(operationCount(residentPartialApplications, "stringLiteral"), 4,
  "resident partial-application prettyM moved strings across the host boundary");
assert.equal(operationCount(residentPartialApplications, "objectSet"), 7,
  "resident partial-application prettyM object-set inventory changed");
assert.equal(operationCount(residentPartialApplications, "scalarSet"), 4,
  "resident partial-application prettyM scalar-set inventory changed");
assert.equal(operationCount(residentSetters, "objectSet"), 0,
  "resident setter prettyM retained object setters");
assert.equal(operationCount(residentSetters, "scalarSet"), 0,
  "resident setter prettyM retained scalar setters");
assert.equal(operationCount(residentSetters, "inc"), 4,
  "resident setter prettyM increment inventory changed");
assert.equal(operationCount(residentIncrements, "inc"), 0,
  "resident increment prettyM retained increments");
assert.equal(operationCount(residentIncrements, "dec"), 5,
  "resident increment prettyM decrement inventory changed");
assert.equal(operationCount(residentIncrements, "delete"), 1,
  "resident increment prettyM delete inventory changed");
assert.equal(operationCount(residentReleases, "dec"), 0,
  "resident release prettyM retained decrements");
assert.equal(operationCount(residentReleases, "delete"), 0,
  "resident release prettyM retained delete");
assert.equal(operationCount(styledReleases, "setTag"), 1,
  "resident styled release prettyM tag-setter inventory changed");
assert.equal(operationCount(styledTagSetters, "setTag"), 0,
  "resident styled tag-setter prettyM retained setTag");
assert.equal(operationCount(residentReleases, "cacheSet"), 20,
  "resident release prettyM lazy-cache inventory changed");
assert.equal(operationCount(styledTagSetters, "cacheSet"), 21,
  "resident styled tag-setter prettyM lazy-cache inventory changed");
assert.equal(operationCount(residentCache, "cacheSet"), 0,
  "resident cache prettyM retained cacheSet");
assert.equal(operationCount(styledCache, "cacheSet"), 0,
  "resident styled cache prettyM retained cacheSet");
assert.equal(operationCount(residentString, "stringLiteral"), 0,
  "resident String prettyM retained String literal imports");
assert.equal(operationCount(styledString, "stringLiteral"), 0,
  "resident styled String prettyM retained String literal imports");
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
  functionImportCount(residentConstructors) + 23,
  functionImportCount(residentAllocator),
  "resident constructors did not remove exactly 23 function imports",
);
assert.equal(
  residentConstructors.manifest.imports.length,
  functionImportCount(residentConstructors),
  "resident-constructor prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentNaturals) + 2,
  functionImportCount(residentConstructors),
  "resident Naturals did not remove exactly two function imports",
);
assert.equal(
  residentNaturals.manifest.imports.length,
  functionImportCount(residentNaturals),
  "resident-Natural prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentPartialApplications) + 87,
  functionImportCount(residentNaturals),
  "resident closure allocation did not remove exactly 87 function imports",
);
assert.equal(functionImportCount(residentPartialApplications), 65,
  "resident partial-application prettyM frontier changed");
assert.equal(
  residentPartialApplications.manifest.imports.length,
  functionImportCount(residentPartialApplications),
  "resident partial-application prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentSetters) + 11,
  functionImportCount(residentPartialApplications),
  "resident setters did not remove exactly 11 function imports",
);
assert.equal(functionImportCount(residentSetters), 54,
  "resident setter prettyM frontier changed");
assert.equal(
  residentSetters.manifest.imports.length,
  functionImportCount(residentSetters),
  "resident setter prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentIncrements) + 4,
  functionImportCount(residentSetters),
  "resident increments did not remove exactly four function imports",
);
assert.equal(functionImportCount(residentIncrements), 50,
  "resident increment prettyM frontier changed");
assert.equal(
  residentIncrements.manifest.imports.length,
  functionImportCount(residentIncrements),
  "resident increment prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentReleases) + 6,
  functionImportCount(residentIncrements),
  "resident releases did not remove exactly six function imports",
);
assert.equal(functionImportCount(residentReleases), 44,
  "resident release prettyM frontier changed");
assert.equal(
  residentReleases.manifest.imports.length,
  functionImportCount(residentReleases),
  "resident release prettyM descriptor and Wasm imports disagree",
);
assert.equal(functionImportCount(styledReleases), 46,
  "resident styled release prettyM frontier changed");
assert.equal(
  functionImportCount(styledTagSetters) + 1,
  functionImportCount(styledReleases),
  "resident styled tag setters did not remove exactly one function import",
);
assert.equal(functionImportCount(styledTagSetters), 45,
  "resident styled tag-setter prettyM frontier changed");
assert.equal(
  styledTagSetters.manifest.imports.length,
  functionImportCount(styledTagSetters),
  "resident styled tag-setter descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentCache) + 20,
  functionImportCount(residentReleases),
  "resident cache did not remove exactly 20 function imports",
);
assert.equal(functionImportCount(residentCache), 24,
  "resident cache prettyM frontier changed");
assert.equal(
  residentCache.manifest.imports.length,
  functionImportCount(residentCache),
  "resident cache prettyM descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(styledCache) + 21,
  functionImportCount(styledTagSetters),
  "resident styled cache did not remove exactly 21 function imports",
);
assert.equal(functionImportCount(styledCache), 24,
  "resident styled cache prettyM frontier changed");
assert.equal(
  styledCache.manifest.imports.length,
  functionImportCount(styledCache),
  "resident styled cache descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentNumeric) + 10,
  functionImportCount(residentCache),
  "resident numeric helpers did not remove exactly ten function imports",
);
assert.equal(functionImportCount(residentNumeric), 14,
  "resident numeric prettyM frontier changed");
assert.equal(
  residentNumeric.manifest.imports.length,
  functionImportCount(residentNumeric),
  "resident numeric descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(styledNumeric) + 10,
  functionImportCount(styledCache),
  "resident styled numeric helpers did not remove exactly ten function imports",
);
assert.equal(functionImportCount(styledNumeric), 14,
  "resident styled numeric prettyM frontier changed");
assert.equal(
  styledNumeric.manifest.imports.length,
  functionImportCount(styledNumeric),
  "resident styled numeric descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentString) + 12,
  functionImportCount(residentNumeric),
  "resident String closure did not remove exactly twelve function imports",
);
assert.equal(functionImportCount(residentString), 2,
  "resident String prettyM frontier changed");
assert.equal(
  residentString.manifest.imports.length,
  functionImportCount(residentString),
  "resident String descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(styledString) + 12,
  functionImportCount(styledNumeric),
  "resident styled String closure did not remove exactly twelve function imports",
);
assert.equal(functionImportCount(styledString), 2,
  "resident styled String prettyM frontier changed");
assert.equal(
  styledString.manifest.imports.length,
  functionImportCount(styledString),
  "resident styled String descriptor and Wasm imports disagree",
);
assert.equal(
  functionImportCount(residentClosed) + 2,
  functionImportCount(residentString),
  "resident fallback closure did not remove exactly two function imports",
);
assert.equal(functionImportCount(residentClosed), 0,
  "closed resident prettyM retained function imports");
assert.equal(residentClosed.manifest.imports.length, 0,
  "closed resident prettyM descriptor retained imports");
assert.equal(
  functionImportCount(styledClosed) + 2,
  functionImportCount(styledString),
  "resident styled fallback closure did not remove exactly two function imports",
);
assert.equal(functionImportCount(styledClosed), 0,
  "closed resident styled prettyM retained function imports");
assert.equal(styledClosed.manifest.imports.length, 0,
  "closed resident styled prettyM descriptor retained imports");
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
assert.equal(
  residentConstructors.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident-constructor prettyM imports memory",
);
assert.equal(
  residentNaturals.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident-Natural prettyM imports memory",
);
assert.equal(
  residentPartialApplications.imports.filter(
    ({ kind }) => kind === "memory",
  ).length,
  0,
  "resident partial-application prettyM imports memory",
);
assert.equal(
  residentSetters.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident setter prettyM imports memory",
);
assert.equal(
  residentIncrements.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident increment prettyM imports memory",
);
assert.equal(
  residentReleases.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident release prettyM imports memory",
);
assert.equal(
  styledTagSetters.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident styled tag-setter prettyM imports memory",
);
assert.equal(
  residentCache.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident cache prettyM imports memory",
);
assert.equal(
  styledCache.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident styled cache prettyM imports memory",
);
assert.equal(
  residentNumeric.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident numeric prettyM imports memory",
);
assert.equal(
  styledNumeric.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident styled numeric prettyM imports memory",
);
assert.equal(
  residentString.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident String prettyM imports memory",
);
assert.equal(
  styledString.imports.filter(({ kind }) => kind === "memory").length,
  0,
  "resident styled String prettyM imports memory",
);
assert.equal(residentClosed.imports.length, 0,
  "closed resident prettyM retained Wasm imports");
assert.equal(styledClosed.imports.length, 0,
  "closed resident styled prettyM retained Wasm imports");
for (const artifact of [
  getTagResident,
  residentRuntime,
  residentProjections,
  residentClosures,
  residentMatches,
  residentAllocator,
  residentConstructors,
  residentNaturals,
  residentPartialApplications,
  residentSetters,
  residentIncrements,
  residentReleases,
  residentCache,
  residentNumeric,
  residentString,
]) {
  assert.deepStrictEqual(
    artifact.manifest.closureDispatch,
    baseline.manifest.closureDispatch,
    "resident linking changed the stable closure-dispatch table",
  );
  assert.deepStrictEqual(
    artifact.manifest.closureDescriptors,
    baseline.manifest.closureDescriptors,
    "resident linking changed the stable closure-descriptor table",
  );
}
assert.deepStrictEqual(
  styledTagSetters.manifest.closureDispatch,
  styledReleases.manifest.closureDispatch,
  "resident styled tag linking changed the closure-dispatch table",
);
assert.deepStrictEqual(
  styledTagSetters.manifest.closureDescriptors,
  styledReleases.manifest.closureDescriptors,
  "resident styled tag linking changed the closure-descriptor table",
);
assert.deepStrictEqual(
  styledCache.manifest.closureDispatch,
  styledTagSetters.manifest.closureDispatch,
  "resident styled cache linking changed the closure-dispatch table",
);
assert.deepStrictEqual(
  styledCache.manifest.closureDescriptors,
  styledTagSetters.manifest.closureDescriptors,
  "resident styled cache linking changed the closure-descriptor table",
);
assert.deepStrictEqual(
  residentNumeric.manifest.closureDispatch,
  residentCache.manifest.closureDispatch,
  "resident numeric linking changed the closure-dispatch table",
);
assert.deepStrictEqual(
  residentNumeric.manifest.closureDescriptors,
  residentCache.manifest.closureDescriptors,
  "resident numeric linking changed the closure-descriptor table",
);
assert.deepStrictEqual(
  styledNumeric.manifest.closureDispatch,
  styledCache.manifest.closureDispatch,
  "resident styled numeric linking changed the closure-dispatch table",
);
assert.deepStrictEqual(
  styledNumeric.manifest.closureDescriptors,
  styledCache.manifest.closureDescriptors,
  "resident styled numeric linking changed the closure-descriptor table",
);
assert.deepStrictEqual(
  residentString.manifest.closureDispatch,
  residentNumeric.manifest.closureDispatch,
  "resident String linking changed the closure-dispatch table",
);
assert.deepStrictEqual(
  residentString.manifest.closureDescriptors,
  residentNumeric.manifest.closureDescriptors,
  "resident String linking changed the closure-descriptor table",
);
assert.deepStrictEqual(
  styledString.manifest.closureDispatch,
  styledNumeric.manifest.closureDispatch,
  "resident styled String linking changed the closure-dispatch table",
);
assert.deepStrictEqual(
  styledString.manifest.closureDescriptors,
  styledNumeric.manifest.closureDescriptors,
  "resident styled String linking changed the closure-descriptor table",
);
assert.deepStrictEqual(
  residentClosed.manifest.closureDispatch,
  residentString.manifest.closureDispatch,
  "resident fallback linking changed the closure-dispatch table",
);
assert.deepStrictEqual(
  residentClosed.manifest.closureDescriptors,
  residentString.manifest.closureDescriptors,
  "resident fallback linking changed the closure-descriptor table",
);
assert.deepStrictEqual(
  styledClosed.manifest.closureDispatch,
  styledString.manifest.closureDispatch,
  "resident styled fallback linking changed the closure-dispatch table",
);
assert.deepStrictEqual(
  styledClosed.manifest.closureDescriptors,
  styledString.manifest.closureDescriptors,
  "resident styled fallback linking changed the closure-descriptor table",
);
for (const [artifact, count, label] of [
  [residentCache, 20, "resident cache"],
  [styledCache, 21, "resident styled cache"],
]) {
  for (let ordinal = 0; ordinal < count; ++ordinal) {
    assert.ok(artifact.exports.some(({ name, kind }) =>
      name === `fir_cache_set_${ordinal}` && kind === "function"),
    `${label} helper export fir_cache_set_${ordinal} is missing`);
  }
  assert.ok(artifact.exports.some(({ name, kind }) =>
    name === artifact.manifest.entry && kind === "function"),
  `${label} entry export is missing`);
  assert.ok(artifact.exports.some(({ name, kind }) =>
    name === "memory" && kind === "memory"),
  `${label} memory export is missing`);
}
for (const [artifact, label] of [
  [residentNumeric, "resident numeric"],
  [styledNumeric, "resident styled numeric"],
]) {
  for (const name of [
    "fir_ext_Int_ofNat",
    "fir_ext_Int_decLt",
    "fir_ext_Int_natAbs",
    "fir_ext_Int_sub",
    "fir_ext_Int_add",
    "fir_ext_Nat_add",
    "fir_ext_Nat_decEq",
    "fir_ext_Nat_sub",
    "fir_ext_Nat_decLt",
    "fir_ext_Nat_decLe",
  ]) {
    assert.ok(artifact.exports.some((entry) =>
      entry.name === name && entry.kind === "function"),
    `${label} helper export ${name} is missing`);
  }
  assert.ok(artifact.exports.some(({ name, kind }) =>
    name === artifact.manifest.entry && kind === "function"),
  `${label} entry export is missing`);
  assert.ok(artifact.exports.some(({ name, kind }) =>
    name === "memory" && kind === "memory"),
  `${label} memory export is missing`);
}
for (const [artifact, label] of [
  [residentClosed, "closed resident"],
  [styledClosed, "closed resident styled"],
]) {
  for (const name of [
    "fir_ext_panicCore",
    "fir_ext_instInhabitedOfMonad__redArg",
  ]) {
    assert.ok(artifact.exports.some((entry) =>
      entry.name === name && entry.kind === "function"),
    `${label} fallback export ${name} is missing`);
  }
  assert.ok(artifact.exports.some(({ name, kind }) =>
    name === artifact.manifest.entry && kind === "function"),
  `${label} entry export is missing`);
  assert.ok(artifact.exports.some(({ name, kind }) =>
    name === "memory" && kind === "memory"),
  `${label} memory export is missing`);
}
for (const [artifact, label] of [
  [residentString, "resident String"],
  [styledString, "resident styled String"],
]) {
  for (const name of [
    "fir_ext_String_Internal_pushn",
    "fir_ext_String_Internal_append",
    "fir_ext_String_Internal_length",
    "fir_ext_String_Internal_posOf",
    "fir_ext_String_Internal_offsetOfPos",
    "fir_ext_String_utf8ByteSize",
    "fir_ext_String_Internal_extract",
    "fir_ext_String_Internal_next",
  ]) {
    assert.ok(artifact.exports.some((entry) =>
      entry.name === name && entry.kind === "function"),
    `${label} helper export ${name} is missing`);
  }
  assert.ok(artifact.exports.some(({ name, kind }) =>
    name === artifact.manifest.entry && kind === "function"),
  `${label} entry export is missing`);
  assert.ok(artifact.exports.some(({ name, kind }) =>
    name === "memory" && kind === "memory"),
  `${label} memory export is missing`);
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
assert.ok(residentConstructors.exports.some(({ name, kind }) =>
  name === residentConstructors.manifest.entry && kind === "function"),
"resident-constructor prettyM entry export is missing");
assert.ok(residentConstructors.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident-constructor prettyM memory export is missing");
for (let ordinal = 0; ordinal < 23; ordinal += 1) {
  const name = `fir_alloc_ctor_${ordinal}`;
  assert.ok(residentConstructors.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident-constructor prettyM helper export ${name} is missing`);
}
assert.ok(residentNaturals.exports.some(({ name, kind }) =>
  name === residentNaturals.manifest.entry && kind === "function"),
"resident-Natural prettyM entry export is missing");
assert.ok(residentNaturals.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident-Natural prettyM memory export is missing");
for (let ordinal = 0; ordinal < 2; ordinal += 1) {
  const name = `fir_nat_literal_${ordinal}`;
  assert.ok(residentNaturals.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident-Natural prettyM helper export ${name} is missing`);
}
assert.ok(residentPartialApplications.exports.some(({ name, kind }) =>
  name === residentPartialApplications.manifest.entry && kind === "function"),
"resident partial-application prettyM entry export is missing");
assert.ok(residentPartialApplications.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident partial-application prettyM memory export is missing");
for (let ordinal = 0; ordinal < 87; ordinal += 1) {
  const name = `fir_alloc_closure_${ordinal}`;
  assert.ok(residentPartialApplications.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident partial-application prettyM helper export ${name} is missing`);
}
assert.ok(residentSetters.exports.some(({ name, kind }) =>
  name === residentSetters.manifest.entry && kind === "function"),
"resident setter prettyM entry export is missing");
assert.ok(residentSetters.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident setter prettyM memory export is missing");
for (let ordinal = 0; ordinal < 11; ordinal += 1) {
  const name = `fir_setter_${ordinal}`;
  assert.ok(residentSetters.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident setter prettyM helper export ${name} is missing`);
}
assert.ok(residentIncrements.exports.some(({ name, kind }) =>
  name === residentIncrements.manifest.entry && kind === "function"),
"resident increment prettyM entry export is missing");
assert.ok(residentIncrements.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident increment prettyM memory export is missing");
for (let ordinal = 0; ordinal < 4; ordinal += 1) {
  const name = `fir_inc_${ordinal}`;
  assert.ok(residentIncrements.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident increment prettyM helper export ${name} is missing`);
}
assert.ok(residentReleases.exports.some(({ name, kind }) =>
  name === residentReleases.manifest.entry && kind === "function"),
"resident release prettyM entry export is missing");
assert.ok(residentReleases.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident release prettyM memory export is missing");
for (let ordinal = 0; ordinal < 6; ordinal += 1) {
  const name = `fir_release_${ordinal}`;
  assert.ok(residentReleases.exports.some((entry) =>
    entry.name === name && entry.kind === "function"),
  `resident release prettyM helper export ${name} is missing`);
}
assert.ok(styledTagSetters.exports.some(({ name, kind }) =>
  name === styledTagSetters.manifest.entry && kind === "function"),
"resident styled tag-setter prettyM entry export is missing");
assert.ok(styledTagSetters.exports.some(({ name, kind }) =>
  name === "memory" && kind === "memory"),
"resident styled tag-setter prettyM memory export is missing");
assert.ok(styledTagSetters.exports.some(({ name, kind }) =>
  name === "fir_set_tag_0" && kind === "function"),
"resident styled tag-setter helper export is missing");

console.log(
  `PASS resident prettyM internalized getTag, isShared, projection, and match families, ` +
  `then installed its allocator and internalized constructors, immediate Naturals, ` +
  `closure allocations, setters, increments, recursive releases, and the ` +
  `styled constructor-tag write, lazy-cache publication, and one-limb ` +
  `resident Nat/Int operations, then UTF-8 String operations/literals and ` +
  `fail-closed fallback traps ` +
  `(${functionImportCount(baseline)} → ${functionImportCount(getTagResident)} → ` +
  `${functionImportCount(residentRuntime)} → ` +
  `${functionImportCount(residentProjections)} → ` +
  `${functionImportCount(residentClosures)} → ` +
  `${functionImportCount(residentMatches)} → ` +
  `${functionImportCount(residentAllocator)} → ` +
  `${functionImportCount(residentConstructors)} → ` +
  `${functionImportCount(residentNaturals)} → ` +
  `${functionImportCount(residentPartialApplications)} → ` +
  `${functionImportCount(residentSetters)} → ` +
  `${functionImportCount(residentIncrements)} → ` +
  `${functionImportCount(residentReleases)} → ` +
  `${functionImportCount(residentCache)} → ` +
  `${functionImportCount(residentNumeric)} → ` +
  `${functionImportCount(residentString)} → ` +
  `${functionImportCount(residentClosed)} function imports; styled ` +
  `${functionImportCount(styledReleases)} → ` +
  `${functionImportCount(styledTagSetters)} → ` +
  `${functionImportCount(styledCache)} → ` +
  `${functionImportCount(styledNumeric)} → ` +
  `${functionImportCount(styledString)} → ` +
  `${functionImportCount(styledClosed)})`,
);
