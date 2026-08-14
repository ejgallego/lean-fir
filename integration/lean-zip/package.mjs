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
import { dirname, join, relative } from "node:path";
import { fileURLToPath } from "node:url";

import {
  LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION,
  LEAN_ZIP_STORED_ADAPTER_API_VERSION,
  LEAN_ZIP_STORED_OWNERSHIP_VERSION,
} from "./lean-zip-stored-browser-adapter.mjs";
import {
  LEAN_ZIP_LEVEL1_ADAPTER_API_VERSION,
  LEAN_ZIP_LEVEL1_OWNERSHIP_VERSION,
  LEAN_ZIP_LEVEL1_PERSISTENT_INITIALIZER,
} from "./lean-zip-level1-browser-adapter.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const leanZipRoot = realpathSync(process.env.LEAN_ZIP_ROOT ??
  "/tmp/fir-lean-zip-30737");
const zipCommonRoot = realpathSync(process.env.ZIP_COMMON_ROOT ??
  "/tmp/fir-zip-common-4425");
const buildDirectory = join(directory, "_build");
const lakeBuildDirectory = join(directory, ".lake", "build");
const wasmStem = join(buildDirectory, "lean-zip-stored.wasm");
const baseStem = join(buildDirectory, "lean-zip-stored-base.wasm");
const inventoryPath = join(buildDirectory, "lean-zip-stored.inventory.json");
const level1WasmStem = join(buildDirectory, "lean-zip-level1.wasm");
const level1BaseStem = join(buildDirectory, "lean-zip-level1-base.wasm");
const level1InventoryPath = join(buildDirectory,
  "lean-zip-level1.inventory.json");
const executableSuffix = process.platform === "win32" ? ".exe" : "";
const level1GeneratorPath = join(lakeBuildDirectory, "bin",
  `leanZipFirLevel1Artifact${executableSuffix}`);
const expectedClosure = JSON.parse(readFileSync(
  join(directory, "closure-contract.json"), "utf8"));
const expectedLevel1Closure = JSON.parse(readFileSync(
  join(directory, "level1-closure-contract.json"), "utf8"));
const byteArrayAdapterPath = join(directory,
  "lean-zip-byte-array-browser-adapter.mjs");
const adapterPath = join(directory, "lean-zip-stored-browser-adapter.mjs");
const smokePath = join(directory, "package-smoke.mjs");
const level1AdapterPath = join(directory,
  "lean-zip-level1-browser-adapter.mjs");
const level1SmokePath = join(directory, "level1-package-smoke.mjs");
const outputNames = [
  "BUILD.json",
  "lean-zip-byte-array-browser-adapter.mjs",
  "lean-zip-stored-browser-adapter.mjs",
  "lean-zip-stored.wasm",
  "lean-zip-stored.wasm.json",
  "smoke.mjs",
];
const level1OutputNames = [
  "BUILD.json",
  "lean-zip-byte-array-browser-adapter.mjs",
  "lean-zip-level1-browser-adapter.mjs",
  "lean-zip-level1.wasm",
  "lean-zip-level1.wasm.json",
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

function publishCurrent(destination, currentName) {
  const current = join(buildDirectory, currentName);
  const temporary = join(buildDirectory,
    `.${currentName}-${process.pid}`);
  rmSync(temporary, { force: true });
  symlinkSync(relative(buildDirectory, destination), temporary);
  renameSync(temporary, current);
  assert.equal(lstatSync(current).isSymbolicLink(), true);
  assert.equal(realpathSync(current), realpathSync(destination));
}

const leanZip = gitState(leanZipRoot);
const zipCommon = gitState(zipCommonRoot);
const fir = gitState(firRoot);
assert.equal(leanZip.commit,
  "30737b4e2ebfd0fc889f0b2e265aae0635d668a1",
  "unexpected lean-zip source revision");
assert.equal(zipCommon.commit,
  "4425bab1f9522307d77e8d485bc536149ba31c36",
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
  "leanZipFirOracle", "leanZipFirLevel1Artifact"], { capture: false });
run("lake", ["--keep-toolchain", "env", "lean", "Probe.lean"],
  { capture: false });
run("lake", ["--keep-toolchain", "env", "lean", "EmitStored.lean"],
  { capture: false });
run(level1GeneratorPath, [], { capture: false });
const firstWasm = readFileSync(wasmStem);
const firstDescriptor = readFileSync(`${wasmStem}.json`);
const firstLevel1Wasm = readFileSync(level1WasmStem);
const firstLevel1Descriptor = readFileSync(`${level1WasmStem}.json`);
run("lake", ["--keep-toolchain", "env", "lean", "EmitStored.lean"],
  { capture: false });
run(level1GeneratorPath, [], { capture: false });
assert.deepEqual(readFileSync(wasmStem), firstWasm,
  "repeated stored generation was not deterministic");
assert.deepEqual(readFileSync(`${wasmStem}.json`), firstDescriptor,
  "repeated stored descriptor generation was not deterministic");
assert.deepEqual(readFileSync(level1WasmStem), firstLevel1Wasm,
  "repeated Level-1 generation was not deterministic");
assert.deepEqual(readFileSync(`${level1WasmStem}.json`),
  firstLevel1Descriptor,
  "repeated Level-1 descriptor generation was not deterministic");
run(process.execPath, [join(directory, "smoke.mjs")], { capture: false });

const wasm = readFileSync(wasmStem);
const baseWasm = readFileSync(baseStem);
const descriptorBytes = readFileSync(`${wasmStem}.json`);
const descriptor = JSON.parse(descriptorBytes);
const inventory = JSON.parse(readFileSync(inventoryPath, "utf8"));
const module = new WebAssembly.Module(wasm);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
assert.deepEqual(imports, []);
assert.deepEqual(exports, [
  { name: "Zip.Wasm.compressStored", kind: "function" },
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
    baseWasmBytes: baseWasm.byteLength,
    completeWasmBytes: wasm.byteLength,
  }[field];
  assert.equal(actual, expected, `${field} changed`);
}
assert.equal(inventory.runtimeOperations, 0);
assert.equal(descriptor.entry, "Zip.Wasm.compressStored");
assert.deepEqual(descriptor.params, ["object"]);
assert.equal(descriptor.result, "object");

const byteArrayAdapterBytes = readFileSync(byteArrayAdapterPath);
const adapterBytes = readFileSync(adapterPath);
const smokeBytes = readFileSync(smokePath);
const leanToolchain = readFileSync(join(firRoot, "lean-toolchain"), "utf8").trim();
const build = {
  schemaVersion: "fir.lean-zip.stored.build/v1",
  sources: {
    fir,
    leanZip: {
      ...leanZip,
      sourceView: "clean read-only source compiled by FIR toolchain",
      relevantFiles: [
        sourceFile(leanZipRoot, "Zip/Wasm/Stored.lean"),
        sourceFile(leanZipRoot, "Zip/Spec/DeflateStoredCorrect.lean"),
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
  },
  entry: {
    sourceName: "Zip.Wasm.compressStored",
    parameters: [{ name: "input", lean: "ByteArray", fir: "object" }],
    result: { lean: "ByteArray", fir: "object" },
  },
  wasm: {
    file: "lean-zip-stored.wasm",
    byteLength: wasm.byteLength,
    sha256: sha256(wasm),
    base: { byteLength: baseWasm.byteLength, sha256: sha256(baseWasm) },
    functionImportCount: 0,
    memoryImportCount: 0,
    memoryOwner: "module",
    exports,
  },
  closure: {
    capture: "compileEntriesFinalCapturedInternalized",
    residentPolicy: "closedApplicationAvailablePolicy",
    capturedDeclarations: inventory.capturedDeclarations,
    reviewedExternalsBeforeLink: inventory.reviewedExternalsBeforeLink,
    retainedSourceFunctions: inventory.sourceFunctions,
    residentHelpers: inventory.residentHelpers,
    residualRuntimeOperations: inventory.runtimeOperations,
  },
  capabilities: {
    byteArray: {
      layoutVersion: LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION,
      representation: "32-byte resident header followed by packed UInt8 bytes",
      operations: ["ByteArray.size", "ByteArray.mk",
        "ByteArray.emptyWithCapacity", "ByteArray.copySlice"],
      allocationOwnership: "live nonpersistent, reference count one",
      uniqueUpdate:
        "copySlice preserves identity iff capacity suffices and refcount is one",
      sharedUpdate:
        "copySlice allocates and consumes one destination reference",
      hostCallbacks: false,
    },
    adapter: {
      module: "lean-zip-stored-browser-adapter.mjs",
      implementationModule: "lean-zip-byte-array-browser-adapter.mjs",
      apiVersion: LEAN_ZIP_STORED_ADAPTER_API_VERSION,
      operation: "adapter.compressStored(Uint8Array)",
      result: "copied Uint8Array",
      timings: ["encodeMs", "executeMs", "decodeMs", "totalMs", "overheadMs"],
    },
    ownership: {
      version: LEAN_ZIP_STORED_OWNERSHIP_VERSION,
      publicInput: "borrowed JavaScript bytes",
      encodedInput: "fresh packed ByteArray in module-owned memory",
      encodedInputOwnership: "borrowed persistent; never mutated by Lean",
      residentResults: "ordinary Lean-owned values with checked reference counts",
      output: "copied JavaScript bytes before rewind",
      rawAddressesExposed: false,
      reclamation: "per-call scratch checkpoint rewind",
      runtimeRootsAboveCheckpoint: false,
    },
  },
  proofStatus: {
    generation: "native-oracle and real-engine checked",
    refinement: "W6 concrete-runtime ByteArray proofs pending",
  },
  test: "node smoke.mjs",
};

const buildBytes = Buffer.from(`${JSON.stringify(build, null, 2)}\n`);
const fingerprint = sha256(Buffer.concat([
  wasm, descriptorBytes, byteArrayAdapterBytes, adapterBytes, buildBytes,
  smokeBytes,
]));
const packageId = `${fir.commit.slice(0, 12)}-${leanZip.commit.slice(0, 12)}-` +
  fingerprint.slice(0, 20);
const packages = join(buildDirectory, "lean-zip-stored-packages");
const destination = join(packages, packageId);
const staging = join(packages, `.staging-${packageId}-${process.pid}`);
mkdirSync(packages, { recursive: true });
rmSync(staging, { recursive: true, force: true });
mkdirSync(staging);
copyFileSync(wasmStem, join(staging, "lean-zip-stored.wasm"));
copyFileSync(`${wasmStem}.json`, join(staging, "lean-zip-stored.wasm.json"));
copyFileSync(byteArrayAdapterPath,
  join(staging, "lean-zip-byte-array-browser-adapter.mjs"));
copyFileSync(adapterPath,
  join(staging, "lean-zip-stored-browser-adapter.mjs"));
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
publishCurrent(destination, "lean-zip-stored-current");
console.log(JSON.stringify({
  ok: true,
  entry: "Zip.Wasm.compressStored",
  packageId,
  directory: destination,
  canonical: join(buildDirectory, "lean-zip-stored-current"),
  wasmBytes: wasm.byteLength,
  wasmSha256: sha256(wasm),
  functionImports: 0,
  memoryImports: 0,
  sourceFunctions: inventory.sourceFunctions.length,
  residentHelpers: inventory.residentHelpers.length,
}));

const level1Wasm = readFileSync(level1WasmStem);
const level1BaseWasm = readFileSync(level1BaseStem);
const level1DescriptorBytes = readFileSync(`${level1WasmStem}.json`);
const level1Descriptor = JSON.parse(level1DescriptorBytes);
const level1Inventory = JSON.parse(readFileSync(level1InventoryPath, "utf8"));
const level1Module = new WebAssembly.Module(level1Wasm);
const level1Imports = WebAssembly.Module.imports(level1Module);
const level1Exports = WebAssembly.Module.exports(level1Module);
assert.deepEqual(level1Imports, []);
assert.deepEqual(level1Exports, [
  { name: "Zip.Wasm.compressLevel1", kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);
for (const [field, expected] of Object.entries(expectedLevel1Closure)) {
  const actual = {
    capturedDeclarations: level1Inventory.capturedDeclarations,
    reviewedExternalsBeforeLink: level1Inventory.reviewedExternalsBeforeLink,
    retainedSourceFunctions: level1Inventory.sourceFunctions.length,
    residentHelpers: level1Inventory.residentHelpers.length,
    completeFunctions: level1Inventory.functions.length,
    baseWasmBytes: level1BaseWasm.byteLength,
    completeWasmBytes: level1Wasm.byteLength,
  }[field];
  assert.equal(actual, expected, `Level-1 ${field} changed`);
}
assert.equal(level1Inventory.runtimeOperations, 0);
assert.equal(level1Descriptor.entry, "Zip.Wasm.compressLevel1");
assert.deepEqual(level1Descriptor.params, ["object"]);
assert.equal(level1Descriptor.result, "object");
run(process.execPath, [join(directory, "level1-smoke.mjs")],
  { capture: false });

const level1AdapterBytes = readFileSync(level1AdapterPath);
const level1SmokeBytes = readFileSync(level1SmokePath);
const level1Build = {
  schemaVersion: "fir.lean-zip.level1.build/v3",
  sources: {
    fir,
    leanZip: {
      ...leanZip,
      sourceView: "clean read-only source compiled by FIR toolchain",
      relevantFiles: [
        sourceFile(leanZipRoot, "Zip/Wasm/Level1.lean"),
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
  },
  entry: {
    sourceName: "Zip.Wasm.compressLevel1",
    parameters: [{ name: "input", lean: "ByteArray", fir: "object" }],
    result: { lean: "ByteArray", fir: "object" },
    persistentInitializer: LEAN_ZIP_LEVEL1_PERSISTENT_INITIALIZER,
  },
  wasm: {
    file: "lean-zip-level1.wasm",
    byteLength: level1Wasm.byteLength,
    sha256: sha256(level1Wasm),
    base: {
      byteLength: level1BaseWasm.byteLength,
      sha256: sha256(level1BaseWasm),
    },
    functionImportCount: 0,
    memoryImportCount: 0,
    memoryOwner: "module",
    exports: level1Exports,
  },
  closure: {
    capture: "compileEntriesFinalCapturedInternalized",
    residentPolicy: "closedApplicationAvailablePolicy",
    arenaPreparation: "linkArtifact with cache-aware lazy publication",
    lazyCaches:
      "compiler flag/value globals retained at their original lazy use sites",
    capturedDeclarations: level1Inventory.capturedDeclarations,
    reviewedExternalsBeforeLink:
      level1Inventory.reviewedExternalsBeforeLink,
    retainedSourceFunctions: level1Inventory.sourceFunctions,
    residentHelpers: level1Inventory.residentHelpers,
    residualRuntimeOperations: level1Inventory.runtimeOperations,
  },
  capabilities: {
    byteArray: {
      layoutVersion: LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION,
      representation: "32-byte resident header followed by packed UInt8 bytes",
      operations: ["ByteArray.size", "ByteArray.mk",
        "ByteArray.emptyWithCapacity", "ByteArray.copySlice"],
      allocationOwnership: "live nonpersistent, reference count one",
      uniqueUpdate:
        "copySlice preserves identity iff capacity suffices and refcount is one",
      sharedUpdate:
        "copySlice allocates and consumes one destination reference",
      hostCallbacks: false,
    },
    adapter: {
      module: "lean-zip-level1-browser-adapter.mjs",
      implementationModule: "lean-zip-byte-array-browser-adapter.mjs",
      apiVersion: LEAN_ZIP_LEVEL1_ADAPTER_API_VERSION,
      operation: "adapter.compressLevel1(Uint8Array)",
      result: "copied Uint8Array",
      timings: ["encodeMs", "executeMs", "decodeMs", "totalMs", "overheadMs"],
      initialization: "adapter.initialization",
      initializationTimings: ["initializeMs=0", "idempotenceMs=0"],
    },
    persistentCaches: {
      initializer: LEAN_ZIP_LEVEL1_PERSISTENT_INITIALIZER,
      invocation: "lazy at the original Lean use site",
      roots:
        "recursively persistent object graphs retained by compiler cache globals",
      checkpoint:
        "rewind floor advances through the cold-call prefix when an object cache is published",
      cacheAwareRewind: true,
      warmCallStable: true,
    },
    ownership: {
      version: LEAN_ZIP_LEVEL1_OWNERSHIP_VERSION,
      publicInput: "borrowed JavaScript bytes",
      encodedInput: "fresh packed ByteArray in module-owned memory",
      encodedInputOwnership: "borrowed persistent; never mutated by Lean",
      residentResults: "ordinary Lean-owned values with checked reference counts",
      output: "copied JavaScript bytes before rewind",
      rawAddressesExposed: false,
      reclamation:
        "warm-call scratch rewind; a cold object-cache miss retains the prefix through its published graph",
      persistentRegion:
        "compiler cache roots define a monotonic cache-aware rewind floor",
      runtimeRootsAboveCheckpoint: false,
    },
  },
  performance: {
    status: "correctness artifact with lazy compiler-cache publication",
    generator:
      "native lowering/linking over a persistent final-LCNF capture checkpoint",
    caveat:
      "cold executeMs may include first-use compiler-cache publication; no cross-runtime performance claim",
  },
  proofStatus: {
    generation: "native-oracle and Node/Chrome real-engine checked",
    refinement: "W6 concrete-runtime proofs pending for newly used helpers",
  },
  test: "node smoke.mjs",
};

const level1BuildBytes = Buffer.from(
  `${JSON.stringify(level1Build, null, 2)}\n`);
const level1Fingerprint = sha256(Buffer.concat([
  level1Wasm,
  level1DescriptorBytes,
  byteArrayAdapterBytes,
  level1AdapterBytes,
  level1BuildBytes,
  level1SmokeBytes,
]));
const level1PackageId = `${fir.commit.slice(0, 12)}-` +
  `${leanZip.commit.slice(0, 12)}-${level1Fingerprint.slice(0, 20)}`;
const level1Packages = join(buildDirectory, "lean-zip-level1-packages");
const level1Destination = join(level1Packages, level1PackageId);
const level1Staging = join(level1Packages,
  `.staging-${level1PackageId}-${process.pid}`);
mkdirSync(level1Packages, { recursive: true });
rmSync(level1Staging, { recursive: true, force: true });
mkdirSync(level1Staging);
copyFileSync(level1WasmStem,
  join(level1Staging, "lean-zip-level1.wasm"));
copyFileSync(`${level1WasmStem}.json`,
  join(level1Staging, "lean-zip-level1.wasm.json"));
copyFileSync(byteArrayAdapterPath,
  join(level1Staging, "lean-zip-byte-array-browser-adapter.mjs"));
copyFileSync(level1AdapterPath,
  join(level1Staging, "lean-zip-level1-browser-adapter.mjs"));
copyFileSync(level1SmokePath, join(level1Staging, "smoke.mjs"));
writeFileSync(join(level1Staging, "BUILD.json"), level1BuildBytes);
const level1Sums = level1OutputNames.map((name) =>
  `${sha256(readFileSync(join(level1Staging, name)))}  ${name}`)
  .join("\n") + "\n";
writeFileSync(join(level1Staging, "SHA256SUMS"), level1Sums);
run(process.execPath, [join(level1Staging, "smoke.mjs")],
  { capture: false });

if (existsSync(level1Destination)) {
  for (const name of [...level1OutputNames, "SHA256SUMS"]) {
    assert.deepEqual(readFileSync(join(level1Staging, name)),
      readFileSync(join(level1Destination, name)),
      `immutable package ${level1PackageId} differs at ${name}`);
  }
  rmSync(level1Staging, { recursive: true });
} else {
  renameSync(level1Staging, level1Destination);
}
publishCurrent(level1Destination, "lean-zip-level1-current");
console.log(JSON.stringify({
  ok: true,
  entry: "Zip.Wasm.compressLevel1",
  packageId: level1PackageId,
  directory: level1Destination,
  canonical: join(buildDirectory, "lean-zip-level1-current"),
  wasmBytes: level1Wasm.byteLength,
  wasmSha256: sha256(level1Wasm),
  functionImports: 0,
  memoryImports: 0,
  sourceFunctions: level1Inventory.sourceFunctions.length,
  residentHelpers: level1Inventory.residentHelpers.length,
}));
