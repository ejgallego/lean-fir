import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import {
  copyFileSync,
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  realpathSync,
  renameSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION } from
  "./lean-zip-byte-array-browser-adapter.mjs";
import {
  LEAN_ZIP_RAW_ADAPTER_API_VERSION,
  LEAN_ZIP_RAW_OWNERSHIP_VERSION,
  LEAN_ZIP_RAW_PERSISTENT_INITIALIZER,
} from "./lean-zip-raw-browser-adapter.mjs";
import { standardLibmRuntimeCapability } from
  "../wasm-runtime/contract.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const leanZipRoot = realpathSync(process.env.LEAN_ZIP_ROOT ??
  "/tmp/fir-lean-zip-273d");
const zipCommonRoot = realpathSync(process.env.ZIP_COMMON_ROOT ??
  "/tmp/fir-zip-common-4425");
const buildDirectory = join(directory, "_build");
const wasmStem = join(buildDirectory, "lean-zip-raw.wasm");
const frontierStem = join(buildDirectory, "lean-zip-raw-frontier.wasm");
const baseStem = join(buildDirectory, "lean-zip-raw-base.wasm");
const externalLibmStem = join(buildDirectory,
  "lean-zip-raw-external-libm.wasm");
const externalRuntimeDirectory = join(firRoot, "integration/wasm-runtime");
const externalLibmSource = join(externalRuntimeDirectory, "libm-runtime.c");
const externalRuntimeLinker = join(externalRuntimeDirectory,
  "link-runtime.mjs");
const functionIndexTool = join(firRoot, "tooling/wasm/function-index.mjs");
const externalRuntimeContract = join(externalRuntimeDirectory,
  "contract.mjs");
const packagedRuntimeContractName = "standard-libm-runtime-contract.mjs";
const previewDirectory = process.env.FIR_RAW_PACKAGE_PREVIEW_DIR === undefined
  ? null
  : resolve(process.env.FIR_RAW_PACKAGE_PREVIEW_DIR);
const emcc = join(firRoot,
  ".deps/lcnf-c-wasm/emsdk/upstream/emscripten/emcc");
const inventoryPath = join(buildDirectory, "lean-zip-raw.inventory.json");
const functionSidecarStem = `${wasmStem}.functions.json`;
const expectedClosure = JSON.parse(readFileSync(
  join(directory, "raw-closure-contract.json"), "utf8"));
const expectedSources = JSON.parse(readFileSync(
  join(directory, "raw-source-contract.json"), "utf8"));
const byteArrayAdapterPath = join(directory,
  "lean-zip-byte-array-browser-adapter.mjs");
const adapterPath = join(directory, "lean-zip-raw-browser-adapter.mjs");
const smokePath = join(directory, "raw-package-smoke.mjs");
const outputNames = [
  "BUILD.json",
  "lean-zip-byte-array-browser-adapter.mjs",
  "lean-zip-raw-browser-adapter.mjs",
  packagedRuntimeContractName,
  "lean-zip-raw.wasm",
  "lean-zip-raw.wasm.functions.json",
  "lean-zip-raw.wasm.json",
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

function capture(command, args, cwd) {
  return run(command, args, { cwd }).trim();
}

function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

function gitState(root) {
  const status = capture("git", ["status", "--porcelain"], root);
  return {
    repository: capture("git", ["remote", "get-url", "origin"], root),
    commit: capture("git", ["rev-parse", "HEAD"], root),
    dirty: status !== "",
    dirtyStatusSha256: status === "" ? null : sha256(status),
  };
}

function sourceFile(root, path) {
  return { path, sha256: sha256(readFileSync(join(root, path))) };
}

function publishCurrent(destination) {
  const current = join(buildDirectory, "lean-zip-raw-current");
  const temporary = join(buildDirectory, `.lean-zip-raw-current-${process.pid}`);
  rmSync(temporary, { force: true });
  symlinkSync(relative(buildDirectory, destination), temporary);
  renameSync(temporary, current);
  assert.equal(lstatSync(current).isSymbolicLink(), true);
  assert.equal(realpathSync(current), realpathSync(destination));
}

const expectedFrontierImports = Object.freeze([
  { module: "lean.extern", name: "Float.log2", kind: "function" },
]);

function generateCompleteRaw() {
  run("lake", ["--keep-toolchain", "env", "lean", "EmitRaw.lean"],
    { capture: false });
  run(emcc, [externalLibmSource, "-O3", "-flto", "--no-entry",
    "-sSTANDALONE_WASM=1", "-sIMPORTED_MEMORY=1",
    "-sALLOW_MEMORY_GROWTH=1", "-sINITIAL_MEMORY=65536",
    "-sSTACK_SIZE=16384", "-Wl,--gc-sections", "-Wl,--strip-all",
    "-o", externalLibmStem], { capture: false });
  const frontier = readFileSync(frontierStem);
  const frontierImports = WebAssembly.Module.imports(
    new WebAssembly.Module(frontier));
  assert.deepEqual(frontierImports, expectedFrontierImports,
    "raw frontier math import inventory changed");
  run(process.execPath, [externalRuntimeLinker, frontierStem,
    externalLibmStem, wasmStem,
    "--function-inventory", inventoryPath,
    "--function-sidecar", functionSidecarStem], { capture: false });
  const frontierDescriptor = JSON.parse(readFileSync(
    `${frontierStem}.json`, "utf8"));
  const descriptor = {
    ...frontierDescriptor,
    imports: [],
    completeRuntime: true,
    externalRuntime: standardLibmRuntimeCapability(
      frontierImports.map(({ name }) => name)),
  };
  writeFileSync(`${wasmStem}.json`, `${JSON.stringify(descriptor)}\n`);
  return { frontierImports };
}

const leanZip = gitState(leanZipRoot);
const zipCommon = gitState(zipCommonRoot);
const fir = gitState(firRoot);
assert.equal(expectedSources.schemaVersion, "fir.lean-zip.raw-source/v1");
assert.equal(leanZip.commit, expectedSources.clientRevision,
  "unexpected lean-zip source revision");
assert.equal(zipCommon.commit, expectedSources.zipCommonRevision,
  "unexpected zipCommon source revision");
assert.equal(leanZip.dirty, false, "lean-zip source view must be clean");
assert.equal(zipCommon.dirty, false, "zipCommon source view must be clean");
if (fir.dirty && process.env.FIR_ALLOW_DIRTY_PACKAGE !== "1") {
  throw new Error("FIR checkout must be clean for immutable publication");
}

const lakeArguments = [
  "--keep-toolchain",
  "--reconfigure",
  `-KleanZipRoot=${leanZipRoot}`,
  `-KzipCommonRoot=${zipCommonRoot}`,
];
run("lake", [...lakeArguments, "build", "LeanZipFir.Compile",
  "leanZipFirOracle"], { capture: false });
run("lake", ["--keep-toolchain", "env", "lean", "ProbeRaw.lean"],
  { capture: false });
const { frontierImports } = generateCompleteRaw();
const firstWasm = readFileSync(wasmStem);
const firstFrontierWasm = readFileSync(frontierStem);
const firstDescriptor = readFileSync(`${wasmStem}.json`);
const firstExternalLibm = readFileSync(externalLibmStem);
const firstFunctionSidecar = readFileSync(functionSidecarStem);
generateCompleteRaw();
assert.deepEqual(readFileSync(wasmStem), firstWasm,
  "repeated complete raw generation was not deterministic");
assert.deepEqual(readFileSync(frontierStem), firstFrontierWasm,
  "repeated raw frontier generation was not deterministic");
assert.deepEqual(readFileSync(`${wasmStem}.json`), firstDescriptor,
  "repeated raw descriptor generation was not deterministic");
assert.deepEqual(readFileSync(externalLibmStem), firstExternalLibm,
  "repeated standard libm runtime generation was not deterministic");
assert.deepEqual(readFileSync(functionSidecarStem), firstFunctionSidecar,
  "repeated final function-sidecar generation was not deterministic");
run(process.execPath, [join(directory, "raw-smoke.mjs")], { capture: false });

const wasm = readFileSync(wasmStem);
const frontierWasm = readFileSync(frontierStem);
const baseWasm = readFileSync(baseStem);
const descriptorBytes = readFileSync(`${wasmStem}.json`);
const descriptor = JSON.parse(descriptorBytes);
const inventory = JSON.parse(readFileSync(inventoryPath, "utf8"));
const functionSidecarBytes = readFileSync(functionSidecarStem);
const functionSidecar = JSON.parse(functionSidecarBytes);
run(process.execPath, [functionIndexTool, "verify", "--wasm", wasmStem,
  "--sidecar", functionSidecarStem], { capture: false });
const inventoryHashes = Object.freeze({
  externalsSha256: sha256(JSON.stringify(inventory.externals)),
  sourceFunctionsSha256: sha256(JSON.stringify(inventory.sourceFunctions)),
  residentHelpersSha256: sha256(JSON.stringify(inventory.residentHelpers)),
  completeFunctionsSha256: sha256(JSON.stringify(inventory.functions)),
});
const module = new WebAssembly.Module(wasm);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
assert.deepEqual(imports, []);
const functionOrigins = Object.fromEntries([
  "lean-source",
  "optimizer-or-linked-runtime",
  "resident-helper",
].map((origin) => [origin, functionSidecar.functions.filter(
  (function_) => function_.origin === origin).length]));
const functionExports = functionSidecar.functions.flatMap((function_) =>
  function_.exportedAs.map((name) => ({ name, index: function_.index })));
const functionIndexSha256 = sha256(JSON.stringify(functionSidecar.functions));
assert.equal(functionSidecar.schemaVersion, "fir.wasm.function-index/v1");
assert.deepEqual(functionSidecar.artifact, {
  file: "lean-zip-raw.wasm",
  byteLength: wasm.byteLength,
  sha256: sha256(wasm),
  functionImportCount: 0,
  definedFunctionCount: 2305,
  functionCount: 2305,
});
assert.deepEqual(functionSidecar.functions.map(({ index }) => index),
  Array.from({ length: 2305 }, (_, index) => index));
assert(functionSidecar.functions.every(({ imported }) => imported === false));
assert.deepEqual(functionOrigins, {
  "lean-source": 390,
  "optimizer-or-linked-runtime": 0,
  "resident-helper": 1915,
});
assert.deepEqual(functionExports, [
  { name: "fir_heap_alloc", index: 17 },
  { name: "fir_heap_frontier", index: 37 },
  { name: "Zip.Wasm.compressRaw", index: 2302 },
  { name: "fir_heap_rewind", index: 2303 },
  { name: "fir_heap_set_frontier", index: 2304 },
]);
assert.deepEqual(inventory.frontierImports,
  frontierImports.map(({ name }) => name));
assert.deepEqual(exports, [
  { name: "Zip.Wasm.compressRaw", kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);
for (const [field, expected] of Object.entries(expectedClosure)) {
  const actual = {
    capturedDeclarations: inventory.capturedDeclarations,
    reviewedExternalsBeforeLink: inventory.reviewedExternalsBeforeLink,
    retainedSourceFunctions: inventory.sourceFunctions.length,
    residentHelpers: inventory.residentHelpers.length,
    completeFunctions: inventory.functions.length,
    ...inventoryHashes,
    releaseFunctionImports: functionSidecar.artifact.functionImportCount,
    releaseDefinedFunctions: functionSidecar.artifact.definedFunctionCount,
    releaseFunctions: functionSidecar.artifact.functionCount,
    releaseLeanSourceFunctions: functionOrigins["lean-source"],
    releaseResidentHelpers: functionOrigins["resident-helper"],
    releaseOptimizerOrLinkedRuntimeFunctions:
      functionOrigins["optimizer-or-linked-runtime"],
    releaseFunctionIndexSha256: functionIndexSha256,
    releaseFunctionSidecarBytes: functionSidecarBytes.byteLength,
    releaseFunctionSidecarSha256: sha256(functionSidecarBytes),
    baseWasmBytes: baseWasm.byteLength,
    frontierWasmBytes: frontierWasm.byteLength,
    completeWasmBytes: wasm.byteLength,
  }[field];
  assert.equal(actual, expected, `raw ${field} changed`);
}
assert.equal(inventory.runtimeOperations, 0);
assert.equal(descriptor.entry, "Zip.Wasm.compressRaw");
assert.deepEqual(descriptor.params, ["object", "uint8"]);
assert.equal(descriptor.result, "object");

const byteArrayAdapterBytes = readFileSync(byteArrayAdapterPath);
const adapterBytes = readFileSync(adapterPath);
const smokeBytes = readFileSync(smokePath);
const leanToolchain = readFileSync(join(firRoot, "lean-toolchain"), "utf8").trim();
const levels = Array.from({ length: 10 }, (_, index) => index + 1);
const build = {
  schemaVersion: "fir.lean-zip.raw.build/v3",
  sources: {
    fir,
    leanZip: {
      ...leanZip,
      sourceView: "clean read-only source compiled by FIR toolchain",
      relevantFiles: [
        sourceFile(leanZipRoot, "Zip/Wasm/Entry.lean"),
        sourceFile(leanZipRoot, "Zip/Native/DeflateDynamic.lean"),
        sourceFile(leanZipRoot, "Zip/Native/DeflateFreqsFused.lean"),
        sourceFile(leanZipRoot, "Zip/Native/Deflate.lean"),
      ],
    },
    zipCommon: {
      ...zipCommon,
      relevantFiles: [sourceFile(zipCommonRoot, "ZipForStd/ByteArray.lean")],
    },
  },
  toolchain: {
    leanToolchain,
    leanVersion: capture("lake", ["--keep-toolchain", "env", "lean",
      "--version"], directory),
    emscriptenVersion: capture(emcc, ["--version"], directory).split("\n")[0],
    externalRuntimeSourceSha256: sha256(readFileSync(externalLibmSource)),
    externalRuntimeContractSha256:
      sha256(readFileSync(externalRuntimeContract)),
  },
  entry: {
    sourceName: "Zip.Wasm.compressRaw",
    parameters: [
      { name: "input", lean: "ByteArray", fir: "object" },
      { name: "level", lean: "UInt8", fir: "uint8" },
    ],
    result: { lean: "ByteArray", fir: "object" },
    levels,
    persistentInitializer: LEAN_ZIP_RAW_PERSISTENT_INITIALIZER,
  },
  wasm: {
    file: "lean-zip-raw.wasm",
    byteLength: wasm.byteLength,
    sha256: sha256(wasm),
    base: { byteLength: baseWasm.byteLength, sha256: sha256(baseWasm) },
    frontier: {
      byteLength: frontierWasm.byteLength,
      sha256: sha256(frontierWasm),
      imports: frontierImports,
    },
    functionImportCount: 0,
    memoryImportCount: 0,
    memoryOwner: "module",
    exports,
    functionEvidence: {
      file: "lean-zip-raw.wasm.functions.json",
      schemaVersion: functionSidecar.schemaVersion,
      byteLength: functionSidecarBytes.byteLength,
      sha256: sha256(functionSidecarBytes),
      functionImportCount: functionSidecar.artifact.functionImportCount,
      definedFunctionCount: functionSidecar.artifact.definedFunctionCount,
      functionCount: functionSidecar.artifact.functionCount,
      functionsSha256: functionIndexSha256,
      origins: functionOrigins,
      exports: functionExports,
      runtimeUse: false,
      releaseBytesIdentical: true,
      protocol: "prepare/restamp/optimize across runtime linking and DCE",
    },
  },
  closure: {
    capture: "compileEntriesFinalCapturedInternalized",
    residentPolicy:
      "closedApplicationAvailablePolicy with reviewed math imports retained",
    arenaPreparation:
      "compiler lazy caches retained with cache-aware rewind floor",
    capturedDeclarations: inventory.capturedDeclarations,
    reviewedExternalsBeforeLink: inventory.reviewedExternalsBeforeLink,
    inventoryHashes,
    retainedSourceFunctions: inventory.sourceFunctions,
    residentHelpers: inventory.residentHelpers,
    residualRuntimeOperations: inventory.runtimeOperations,
  },
  capabilities: {
    completeRuntime: {
      version: "fir.lean-zip.raw.complete-runtime/v1",
      selfContained: true,
      unresolvedRuntimeOperations: [],
      externalRuntime: standardLibmRuntimeCapability(
        frontierImports.map(({ name }) => name)),
    },
    byteArray: {
      layoutVersion: LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION,
      representation: "32-byte resident header followed by packed UInt8 bytes",
      operations: ["ByteArray.size", "ByteArray.mk",
        "ByteArray.emptyWithCapacity", "ByteArray.copySlice"],
      hostCallbacks: false,
    },
    adapter: {
      module: "lean-zip-raw-browser-adapter.mjs",
      implementationModule: "lean-zip-byte-array-browser-adapter.mjs",
      apiVersion: LEAN_ZIP_RAW_ADAPTER_API_VERSION,
      operation: "adapter.compressRaw(Uint8Array, level)",
      result: "copied Uint8Array",
      timings: ["encodeMs", "executeMs", "decodeMs", "totalMs", "overheadMs"],
      initialization: "adapter.initialization",
      initializationTimings: ["initializeMs", "idempotenceMs"],
    },
    persistentCaches: {
      initializer: LEAN_ZIP_RAW_PERSISTENT_INITIALIZER,
      invocation: "lazy at the original Lean use site",
      roots:
        "recursively persistent object graphs retained by compiler cache globals",
      checkpoint:
        "rewind floor advances through the cold-call prefix when an object cache is published",
      cacheAwareRewind: true,
      warmCallStable: true,
    },
    ownership: {
      version: LEAN_ZIP_RAW_OWNERSHIP_VERSION,
      publicInput: "borrowed JavaScript bytes",
      encodedInput: "fresh packed ByteArray in module-owned memory",
      output: "copied JavaScript bytes before rewind",
      rawAddressesExposed: false,
      reclamation:
        "warm-call scratch rewind; a cold object-cache miss retains the prefix through its published graph",
      persistentRegion:
        "compiler cache roots define a monotonic cache-aware rewind floor",
      runtimeRootsAboveCheckpoint: false,
      externalRuntimeReservation:
        "reserved before lazy-cache publication or Lean graph allocation",
    },
  },
  verification: {
    producer: "native-byte equality and independent raw inflate",
    levels,
    cases: ["empty", "boundaries", "repeated-4KiB", "random-4KiB", "unicode"],
  },
  proofStatus: {
    generation: "native-oracle and Node real-engine checked",
    refinement: "uses FIR's generic resident helper frontier",
  },
  test: "node smoke.mjs",
};

const buildBytes = Buffer.from(`${JSON.stringify(build, null, 2)}\n`);
const fingerprint = sha256(Buffer.concat([
  wasm, frontierWasm, descriptorBytes, functionSidecarBytes,
  byteArrayAdapterBytes, adapterBytes,
  readFileSync(externalRuntimeContract), buildBytes, smokeBytes,
]));
const packageId = `${fir.commit.slice(0, 12)}-${leanZip.commit.slice(0, 12)}-` +
  fingerprint.slice(0, 20);
const packages = previewDirectory === null
  ? join(buildDirectory, "lean-zip-raw-packages")
  : dirname(previewDirectory);
const destination = previewDirectory ?? join(packages, packageId);
const staging = join(packages, `.staging-${packageId}-${process.pid}`);
mkdirSync(packages, { recursive: true });
rmSync(staging, { recursive: true, force: true });
mkdirSync(staging);
copyFileSync(wasmStem, join(staging, "lean-zip-raw.wasm"));
copyFileSync(functionSidecarStem,
  join(staging, "lean-zip-raw.wasm.functions.json"));
copyFileSync(`${wasmStem}.json`, join(staging, "lean-zip-raw.wasm.json"));
copyFileSync(byteArrayAdapterPath,
  join(staging, "lean-zip-byte-array-browser-adapter.mjs"));
copyFileSync(adapterPath, join(staging, "lean-zip-raw-browser-adapter.mjs"));
copyFileSync(externalRuntimeContract,
  join(staging, packagedRuntimeContractName));
copyFileSync(smokePath, join(staging, "smoke.mjs"));
writeFileSync(join(staging, "BUILD.json"), buildBytes);
const sums = outputNames.map((name) =>
  `${sha256(readFileSync(join(staging, name)))}  ${name}`).join("\n") + "\n";
writeFileSync(join(staging, "SHA256SUMS"), sums);
run(process.execPath, [join(staging, "smoke.mjs")], { capture: false });

if (existsSync(destination)) {
  for (const name of [...outputNames, "SHA256SUMS"]) {
    assert.deepEqual(readFileSync(join(staging, name)),
      readFileSync(join(destination, name)),
      `immutable package ${packageId} differs at ${name}`);
  }
  rmSync(staging, { recursive: true });
} else {
  renameSync(staging, destination);
}
if (previewDirectory === null) publishCurrent(destination);
console.log(JSON.stringify({
  ok: true,
  preview: previewDirectory !== null,
  entry: "Zip.Wasm.compressRaw",
  levels,
  packageId,
  directory: destination,
  canonical: previewDirectory === null
    ? join(buildDirectory, "lean-zip-raw-current")
    : null,
  wasmBytes: wasm.byteLength,
  wasmSha256: sha256(wasm),
  functionSidecarBytes: functionSidecarBytes.byteLength,
  functionSidecarSha256: sha256(functionSidecarBytes),
  finalFunctions: functionSidecar.artifact.functionCount,
  functionImports: 0,
  memoryImports: 0,
  sourceFunctions: inventory.sourceFunctions.length,
  residentHelpers: inventory.residentHelpers.length,
}));
