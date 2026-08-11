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

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const leanZipRoot = realpathSync(process.env.LEAN_ZIP_ROOT ??
  "/tmp/fir-lean-zip-30737");
const zipCommonRoot = realpathSync(process.env.ZIP_COMMON_ROOT ??
  "/tmp/fir-zip-common-4425");
const buildDirectory = join(directory, "_build");
const wasmStem = join(buildDirectory, "lean-zip-stored.wasm");
const baseStem = join(buildDirectory, "lean-zip-stored-base.wasm");
const inventoryPath = join(buildDirectory, "lean-zip-stored.inventory.json");
const expectedClosure = JSON.parse(readFileSync(
  join(directory, "closure-contract.json"), "utf8"));
const adapterPath = join(directory, "lean-zip-stored-browser-adapter.mjs");
const smokePath = join(directory, "package-smoke.mjs");
const outputNames = [
  "BUILD.json",
  "lean-zip-stored-browser-adapter.mjs",
  "lean-zip-stored.wasm",
  "lean-zip-stored.wasm.json",
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
  const current = join(buildDirectory, "lean-zip-stored-current");
  const temporary = join(buildDirectory,
    `.lean-zip-stored-current-${process.pid}`);
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
  "leanZipFirOracle"], { capture: false });
run("lake", ["--keep-toolchain", "env", "lean", "Probe.lean"],
  { capture: false });
run("lake", ["--keep-toolchain", "env", "lean", "Emit.lean"],
  { capture: false });
const firstWasm = readFileSync(wasmStem);
const firstDescriptor = readFileSync(`${wasmStem}.json`);
run("lake", ["--keep-toolchain", "env", "lean", "Emit.lean"],
  { capture: false });
assert.deepEqual(readFileSync(wasmStem), firstWasm,
  "repeated stored generation was not deterministic");
assert.deepEqual(readFileSync(`${wasmStem}.json`), firstDescriptor,
  "repeated stored descriptor generation was not deterministic");
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
  wasm, descriptorBytes, adapterBytes, buildBytes, smokeBytes,
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
publishCurrent(destination);
console.log(JSON.stringify({
  ok: true,
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
