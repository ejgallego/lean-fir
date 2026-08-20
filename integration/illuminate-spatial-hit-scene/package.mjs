import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import {
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  renameSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import {
  ILLUMINATE_SPATIAL_HIT_SCENE_ADAPTER_API_VERSION,
  ILLUMINATE_SPATIAL_HIT_SCENE_INPUT_LAYOUT_VERSION,
  ILLUMINATE_SPATIAL_HIT_SCENE_OWNERSHIP_VERSION,
} from "./illuminate-spatial-hit-scene-browser-adapter.mjs";
import { standardLibmRuntimeCapability } from
  "../wasm-runtime/contract.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const illuminateRoot = realpathSync(process.env.ILLUMINATE_ROOT ??
  join(directory, ".illuminate"));
const fixturePath = resolve(process.env.ILLUMINATE_SPATIAL_HIT_SCENE_FIXTURE ??
  join(illuminateRoot, "test_output/hit-scene-benchmark.json"));
const suitePath = resolve(process.env.ILLUMINATE_SPATIAL_HIT_SCENE_SUITE ??
  join(illuminateRoot, "test_output/hit-scene-benchmark-suite.json"));
const buildDirectory = join(directory, "_build");
const baseStem = join(buildDirectory, "illuminate-spatial-hit-scene-base.wasm");
const frontierStem = join(buildDirectory, "illuminate-spatial-hit-scene-frontier.wasm");
const libmStem = join(buildDirectory,
  "illuminate-spatial-hit-scene-libm.wasm");
const completeStem = join(buildDirectory, "illuminate-spatial-hit-scene-complete.wasm");
const sourcePin = JSON.parse(readFileSync(join(directory,
  "illuminate-source.json"), "utf8"));
const expectedClosure = JSON.parse(readFileSync(join(directory,
  "closure-contract.json"), "utf8"));
const outputNames = [
  "BUILD.json",
  "browser-smoke.html",
  "hit-scene-benchmark.json",
  "hit-scene-benchmark-suite.json",
  "illuminate-spatial-hit-scene-browser-adapter.mjs",
  "illuminate-spatial-hit-scene.wasm",
  "illuminate-spatial-hit-scene.wasm.json",
  "smoke.mjs",
];

function run(command, args, options = {}) {
  return execFileSync(command, args, {
    cwd: options.cwd ?? directory,
    encoding: options.encoding ?? "utf8",
    stdio: options.capture === false ? "inherit" : ["ignore", "pipe", "inherit"],
    maxBuffer: 64 * 1024 * 1024,
  });
}

function capture(command, args, cwd = directory) {
  return run(command, args, { cwd }).trim();
}

function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

function gitState(root) {
  return {
    commit: capture("git", ["rev-parse", "HEAD"], root),
    dirty: capture("git", ["status", "--porcelain"], root) !== "",
  };
}

function assertPinnedSource() {
  const state = gitState(illuminateRoot);
  run("git", ["merge-base", "--is-ancestor", sourcePin.revision, state.commit],
    { cwd: illuminateRoot });
  assert.equal(state.dirty, false, "Illuminate source checkout must be clean");
  for (const [path, expected] of Object.entries(sourcePin.files)) {
    assert.equal(sha256(readFileSync(join(illuminateRoot, path))), expected,
      `Illuminate source digest changed for ${path}`);
  }
  for (const [path, expected] of Object.entries(sourcePin.fixtures)) {
    assert.equal(sha256(readFileSync(join(illuminateRoot, path))), expected,
      `Illuminate fixture digest changed for ${path}`);
  }
  return { ...state, pinnedRevision: sourcePin.revision };
}

function assertOptional(actual, expected, label) {
  if (expected !== null) assert.equal(actual, expected, `${label} changed`);
}

function publishCurrent(destination) {
  const current = join(buildDirectory, "illuminate-spatial-hit-scene-current");
  const temporary = join(buildDirectory,
    `.illuminate-spatial-hit-scene-current-${process.pid}`);
  rmSync(temporary, { force: true });
  symlinkSync(relative(buildDirectory, destination), temporary);
  renameSync(temporary, current);
  assert.equal(lstatSync(current).isSymbolicLink(), true);
  assert.equal(realpathSync(current), realpathSync(destination));
}

const illuminate = assertPinnedSource();
const fir = gitState(firRoot);
if (fir.dirty && process.env.FIR_ALLOW_DIRTY_PACKAGE !== "1") {
  throw new Error("FIR checkout must be clean for immutable publication");
}
assert(existsSync(fixturePath),
  `HitScene fixture not found: ${fixturePath}`);
assert(existsSync(suitePath),
  `HitScene fixture suite not found: ${suitePath}`);
mkdirSync(buildDirectory, { recursive: true });

const priorFrontierHash = existsSync(frontierStem)
  ? sha256(readFileSync(frontierStem)) : null;
if (process.env.FIR_SPATIAL_HIT_SCENE_REUSE_FRONTIER !== "1") {
  run("lake", ["--keep-toolchain", "--reconfigure",
    `-KilluminateRoot=${illuminateRoot}`, "build",
    "IlluminateFirSpatialHitScene.Compile"], { capture: false });
  run("lake", ["--keep-toolchain", "--reconfigure",
    `-KilluminateRoot=${illuminateRoot}`, "env", "lean",
    "-DmaxHeartbeats=0", "Emit.lean"], { capture: false });
}
const frontierHash = sha256(readFileSync(frontierStem));
if (process.env.FIR_SPATIAL_HIT_SCENE_REQUIRE_REPEAT === "1") {
  assert(priorFrontierHash !== null, "repeat gate requires a prior frontier");
  assert.equal(frontierHash, priorFrontierHash,
    "repeated resident generation was not deterministic");
}

const expectedFrontierImports = Object.freeze([
  { module: "lean.extern", name: "Float.acos", kind: "function" },
  { module: "lean.extern", name: "Float.cos", kind: "function" },
  { module: "lean.extern", name: "Float.cbrt", kind: "function" },
  { module: "lean.extern", name: "Float.sin", kind: "function" },
  { module: "lean.extern", name: "Float.atan2", kind: "function" },
]);
const frontierImports = WebAssembly.Module.imports(new WebAssembly.Module(
  readFileSync(frontierStem)));
assert.deepEqual(frontierImports, expectedFrontierImports,
  "SpatialHitScene frontier libm import inventory changed");

const emsdk = join(firRoot, ".deps/lcnf-c-wasm/emsdk");
const emcc = join(emsdk, "upstream/emscripten/emcc");
const externalRuntimeDirectory = join(firRoot, "integration/wasm-runtime");
const externalLibmSource = join(externalRuntimeDirectory, "libm-runtime.c");
const externalRuntimeLinker = join(externalRuntimeDirectory, "link-runtime.mjs");
const externalRuntimeContract = join(externalRuntimeDirectory, "contract.mjs");
run(emcc, [externalLibmSource, "-O3", "-flto",
  "--no-entry", "-sSTANDALONE_WASM=1", "-sIMPORTED_MEMORY=1",
  "-sALLOW_MEMORY_GROWTH=1", "-sINITIAL_MEMORY=65536",
  "-sSTACK_SIZE=16384", "-Wl,--gc-sections", "-Wl,--strip-all",
  "-o", libmStem], { capture: false });
run(process.execPath, [externalRuntimeLinker, frontierStem,
  libmStem, completeStem], { capture: false });
const firstCompleteHash = sha256(readFileSync(completeStem));
if (process.env.FIR_SPATIAL_HIT_SCENE_REQUIRE_REPEAT === "1") {
  const repeatedLibm = join(buildDirectory,
    "illuminate-spatial-hit-scene-libm-repeat.wasm");
  const repeatedComplete = join(buildDirectory,
    "illuminate-spatial-hit-scene-complete-repeat.wasm");
  run(emcc, [externalLibmSource, "-O3", "-flto",
    "--no-entry", "-sSTANDALONE_WASM=1", "-sIMPORTED_MEMORY=1",
    "-sALLOW_MEMORY_GROWTH=1", "-sINITIAL_MEMORY=65536",
    "-sSTACK_SIZE=16384", "-Wl,--gc-sections", "-Wl,--strip-all",
    "-o", repeatedLibm], { capture: false });
  run(process.execPath, [externalRuntimeLinker, frontierStem,
    repeatedLibm, repeatedComplete], { capture: false });
  assert.equal(sha256(readFileSync(repeatedComplete)), firstCompleteHash,
    "repeated complete-runtime link was not deterministic");
  rmSync(repeatedLibm, { force: true });
  rmSync(repeatedComplete, { force: true });
}

const wasm = readFileSync(completeStem);
const baseWasm = readFileSync(baseStem);
const frontierWasm = readFileSync(frontierStem);
const frontierInventory = JSON.parse(readFileSync(
  `${frontierStem.slice(0, -5)}.inventory.json`, "utf8"));
const descriptor = JSON.parse(readFileSync(`${frontierStem}.json`, "utf8"));
descriptor.imports = [];
descriptor.completeRuntime = true;
descriptor.externalRuntime = standardLibmRuntimeCapability(
  frontierInventory.imports.map(({ name }) => name));
const module = new WebAssembly.Module(wasm);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
assert.deepEqual(imports, []);
assert.deepEqual(exports, [
  { name: "Illuminate.SpatialHitScene.ofHitScene", kind: "function" },
  { name: "IlluminateFirSpatialHitScene.queryBorrowed._fir_bit_exact", kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);
assertOptional(frontierInventory.capturedDeclarations,
  expectedClosure.capturedDeclarations, "captured declaration count");
assertOptional(frontierInventory.reviewedExternalsBeforeLink,
  expectedClosure.reviewedExternalsBeforeLink, "reviewed external count");
assertOptional(baseWasm.byteLength, expectedClosure.baseWasmBytes,
  "base Wasm bytes");
assertOptional(frontierInventory.functions.length,
  expectedClosure.frontierFunctions, "frontier function count");
assertOptional(sha256(JSON.stringify(frontierInventory.functions)),
  expectedClosure.frontierFunctionSha256, "frontier function inventory");
assertOptional(frontierInventory.imports.length,
  expectedClosure.frontierImports, "frontier import count");
assertOptional(sha256(JSON.stringify(frontierInventory.imports)),
  expectedClosure.frontierImportSha256, "frontier import inventory");
assertOptional(wasm.byteLength, expectedClosure.completeWasmBytes,
  "complete Wasm bytes");

const fixture = readFileSync(fixturePath);
const fixtureJson = JSON.parse(fixture);
assert.equal(fixtureJson.schemaVersion, "illuminate.hit-scene-benchmark/v1");
assert.equal(fixtureJson.queries.length, 301);
const suite = readFileSync(suitePath);
const suiteJson = JSON.parse(suite);
assert.equal(suiteJson.schemaVersion, "illuminate.hit-scene-benchmark-suite/v1");
assert.deepEqual(suiteJson.fixtures.map(({ queries }) => queries.length),
  [83, 301, 625]);
const adapter = readFileSync(join(directory,
  "illuminate-spatial-hit-scene-browser-adapter.mjs"));
const browserSmoke = readFileSync(join(directory, "browser-smoke.html"));
const smoke = readFileSync(join(directory, "package-smoke.mjs"));
const leanToolchain = readFileSync(join(directory, "lean-toolchain"), "utf8").trim();
const leanVersion = capture("lake", ["--keep-toolchain", "env", "lean",
  "--version"]);
const libmExports = WebAssembly.Module.exports(new WebAssembly.Module(
  readFileSync(libmStem))).filter(({ kind }) => kind === "function")
  .map(({ name }) => name).filter((name) => !name.startsWith("_") &&
    !name.startsWith("emscripten_"));
const build = {
  schemaVersion: "fir.illuminate-spatial-hit-scene.build/v2",
  sources: {
    fir: { repository: "git@github.com:ejgallego/lean-fir.git", ...fir },
    illuminate: {
      repository: sourcePin.repository,
      ...illuminate,
      sourceView: {
        mechanism: "Lake external source root",
        reconfiguredBeforeCapture: true,
        consumedSourceBuildArtifacts: false,
      },
      relevantFiles: Object.entries(sourcePin.files).map(([path, digest]) =>
        ({ path, sha256: digest })),
    },
  },
  toolchain: {
    leanToolchain,
    leanVersion,
    emscriptenVersion: capture(emcc, ["--version"]).split("\n")[0],
    emscriptenSha256: sha256(readFileSync(emcc)),
    externalRuntimeSourceSha256: sha256(readFileSync(externalLibmSource)),
    externalRuntimeContractSha256:
      sha256(readFileSync(externalRuntimeContract)),
  },
  entries: {
    prepare: {
      sourceName: "Illuminate.SpatialHitScene.ofHitScene",
      exportName: "Illuminate.SpatialHitScene.ofHitScene",
      parameters: [{ name: "scene", lean: "HitScene", fir: "object" }],
      result: { lean: "SpatialHitScene", fir: "object" },
    },
    query: {
      sourceName: "Illuminate.SpatialHitScene.query",
      exportedFacade: "IlluminateFirSpatialHitScene.queryBorrowed._fir_bit_exact",
      parameters: [
        { name: "scene", lean: "SpatialHitScene", fir: "object" },
        { name: "x", lean: "Float", fir: "float", transport: "uint64-bits" },
        { name: "y", lean: "Float", fir: "float", transport: "uint64-bits" },
      ],
      result: { lean: "HitSceneResult", fir: "tobject" },
    },
  },
  wasm: {
    file: "illuminate-spatial-hit-scene.wasm",
    byteLength: wasm.byteLength,
    sha256: sha256(wasm),
    base: { byteLength: baseWasm.byteLength, sha256: sha256(baseWasm) },
    frontier: { byteLength: frontierWasm.byteLength, sha256: frontierHash },
    functionImportCount: 0,
    memoryImportCount: 0,
    memoryOwner: "module",
    exports,
  },
  closure: {
    capturedDeclarations: frontierInventory.capturedDeclarations,
    reviewedExternalsBeforeLink: frontierInventory.reviewedExternalsBeforeLink,
    retainedFunctions: frontierInventory.functions,
    unresolvedBeforeLibmLink: frontierInventory.imports,
    runtimeOperationsAfterResidentLink: frontierInventory.runtimeOperations,
    libmRuntimeFunctions: libmExports,
  },
  capabilities: {
    completeRuntime: {
      version: "fir.illuminate-spatial-hit-scene.complete-runtime/v1",
      selfContained: true,
      functionImports: 0,
      memoryImports: 0,
      externalRuntime: standardLibmRuntimeCapability(
        frontierInventory.imports.map(({ name }) => name)),
    },
    inputLayout: {
      version: ILLUMINATE_SPATIAL_HIT_SCENE_INPUT_LAYOUT_VERSION,
      source: "Illuminate.HitScene.encode JSON projected once to raw Lean values",
      coordinateTransport: "bit-exact IEEE-754 binary64",
    },
    ownership: {
      version: ILLUMINATE_SPATIAL_HIT_SCENE_OWNERSHIP_VERSION,
      instance: "one WebAssembly.Instance per opaque scene",
      memoryOwner: "module",
      runtimeReservation:
        "adapter advances the FIR frontier past the external runtime prefix",
      persistent: "source graph and Lean-produced spatial scene below a per-instance checkpoint",
      preparation: "SpatialHitScene.ofHitScene executes once in Wasm during createHitScene",
      scratch: "result graph cleared and rewound after every query",
      disposal: "drop instance; no raw Wasm address escapes",
    },
    browserAdapter: {
      apiVersion: ILLUMINATE_SPATIAL_HIT_SCENE_ADAPTER_API_VERSION,
      operations: ["createHitScene", "hitTest", "hitTestDiagnostic",
        "disposeHitScene"],
    },
  },
  fixture: {
    file: "hit-scene-benchmark.json",
    schemaVersion: fixtureJson.schemaVersion,
    queryCount: fixtureJson.queryCount,
    byteLength: fixture.byteLength,
    sha256: sha256(fixture),
  },
  fixtureSuite: {
    file: "hit-scene-benchmark-suite.json",
    schemaVersion: suiteJson.schemaVersion,
    fixtureCount: suiteJson.fixtures.length,
    queryCount: suiteJson.fixtures.reduce(
      (count, item) => count + item.queries.length, 0),
    byteLength: suite.byteLength,
    sha256: sha256(suite),
  },
  deterministicGate: {
    repeatedFrontierCompared:
      process.env.FIR_SPATIAL_HIT_SCENE_REQUIRE_REPEAT === "1",
    repeatedCompleteLinkCompared:
      process.env.FIR_SPATIAL_HIT_SCENE_REQUIRE_REPEAT === "1",
  },
};

const publication = mkdtempSync(join(buildDirectory,
  ".illuminate-spatial-hit-scene-package-"));
writeFileSync(join(publication, "BUILD.json"),
  `${JSON.stringify(build, null, 2)}\n`);
writeFileSync(join(publication, "illuminate-spatial-hit-scene.wasm"), wasm);
writeFileSync(join(publication, "illuminate-spatial-hit-scene.wasm.json"),
  `${JSON.stringify(descriptor, null, 2)}\n`);
writeFileSync(join(publication, "illuminate-spatial-hit-scene-browser-adapter.mjs"),
  adapter);
writeFileSync(join(publication, "browser-smoke.html"), browserSmoke);
writeFileSync(join(publication, "hit-scene-benchmark.json"), fixture);
writeFileSync(join(publication, "hit-scene-benchmark-suite.json"), suite);
writeFileSync(join(publication, "smoke.mjs"), smoke);
const sums = outputNames.map((name) =>
  `${sha256(readFileSync(join(publication, name)))}  ${name}`).join("\n") + "\n";
writeFileSync(join(publication, "SHA256SUMS"), sums);
run(process.execPath, [join(publication, "smoke.mjs")], {
  cwd: publication, capture: false,
});

const packageSha256 = sha256(sums);
const destination = join(buildDirectory,
  `illuminate-spatial-hit-scene-${packageSha256.slice(0, 16)}`);
if (existsSync(destination)) {
  for (const name of [...outputNames, "SHA256SUMS"]) {
    assert.equal(sha256(readFileSync(join(publication, name))),
      sha256(readFileSync(join(destination, name))),
      `immutable publication differs for ${name}`);
  }
  rmSync(publication, { recursive: true, force: true });
} else {
  renameSync(publication, destination);
}
publishCurrent(destination);
console.log(JSON.stringify({
  package: destination,
  current: join(buildDirectory, "illuminate-spatial-hit-scene-current"),
  wasmBytes: wasm.byteLength,
  wasmSha256: sha256(wasm),
  packageSha256,
  imports,
  exports,
}, null, 2));
