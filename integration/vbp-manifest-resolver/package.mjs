import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  chmodSync,
  copyFileSync,
  existsSync,
  mkdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { dirname, join, resolve } from "node:path";
import { performance } from "node:perf_hooks";
import { fileURLToPath } from "node:url";

import {
  publishImmutablePackage,
  sha256,
} from "../package-tools/immutable-package.mjs";
import { verifyBrowserPackage } from
  "../package-tools/verified-package.mjs";
import {
  VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION,
  VBP_MANIFEST_RESOLVER_ENTRY,
  VBP_MANIFEST_RESOLVER_INPUT_LAYOUT_VERSION,
  VBP_MANIFEST_RESOLVER_OWNERSHIP_VERSION,
} from "./vbp-manifest-resolver-browser-adapter.mjs";
import {
  vbpManifestResolverPackagePolicy,
  vbpManifestResolverPayloadFiles,
} from "./package-policy.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const vbpRoot = realpathSync(process.env.VBP_ROOT ?? join(firRoot,
  ".deps/source-views/vbp-manifest-resolver-1af64db2"));
const buildDirectory = join(directory, "_build");
const firSourceRoot = join(firRoot,
  ".deps/source-views/fir-vbp-manifest-resolver");
const baseStem = join(buildDirectory, "vbp-manifest-resolver-base.wasm");
const residentStem = join(buildDirectory, "vbp-manifest-resolver.wasm");
const sourcePin = Object.freeze(JSON.parse(readFileSync(
  join(directory, "vbp-source.json"), "utf8")));
const expectedClosure = Object.freeze(JSON.parse(readFileSync(
  join(directory, "closure-contract.json"), "utf8")));

function run(command, args, options = {}) {
  return execFileSync(command, args, {
    cwd: options.cwd ?? directory,
    encoding: options.encoding ?? "utf8",
    env: { ...process.env, ...options.env },
    stdio: options.capture === false ? "inherit" : ["ignore", "pipe", "inherit"],
    maxBuffer: options.maxBuffer ?? 128 * 1024 * 1024,
  });
}

function capture(command, args, cwd = directory) {
  return run(command, args, { cwd }).trim();
}

function gitState(root) {
  return {
    commit: capture("git", ["rev-parse", "HEAD"], root),
    dirty: capture("git", ["status", "--porcelain"], root) !== "",
  };
}

function assertOptional(actual, expected, label) {
  if (expected !== null) assert.equal(actual, expected, `${label} changed`);
}

function relevantFiles(root, paths) {
  return paths.map((path) => ({ path, sha256: sha256(readFileSync(join(root, path))) }));
}

function assertPinnedVbp() {
  const state = gitState(vbpRoot);
  assert.equal(state.commit, sourcePin.revision,
    "VBP checkout does not match vbp-source.json");
  assert.equal(state.dirty, false, "VBP source checkout must be clean");
  for (const [path, digest] of Object.entries(sourcePin.files)) {
    assert.equal(sha256(readFileSync(join(vbpRoot, path))), digest,
      `VBP source digest changed for ${path}`);
  }
  return state;
}

function prepareFirSourceArchive(commit) {
  const marker = join(firSourceRoot, ".fir-source-commit");
  if (existsSync(marker) && readFileSync(marker, "utf8").trim() === commit) {
    return firSourceRoot;
  }
  rmSync(firSourceRoot, { recursive: true, force: true });
  mkdirSync(firSourceRoot, { recursive: true });
  const archive = join(firRoot, ".deps/source-views",
    `.fir-vbp-manifest-resolver-${commit}.tar`);
  rmSync(archive, { force: true });
  try {
    run("git", ["archive", "--format=tar", "--output", archive, commit], {
      cwd: firRoot,
    });
    run("tar", ["-xf", archive, "-C", firSourceRoot]);
  } finally {
    rmSync(archive, { force: true });
  }
  writeFileSync(marker, `${commit}\n`);
  return firSourceRoot;
}

const generationStarted = performance.now();
const vbp = assertPinnedVbp();
const fir = gitState(firRoot);
if (fir.dirty && process.env.FIR_ALLOW_DIRTY_PACKAGE !== "1") {
  throw new Error("FIR checkout must be clean for immutable publication");
}
prepareFirSourceArchive(fir.commit);
mkdirSync(buildDirectory, { recursive: true });
const tmpdir = join(firRoot, ".deps/tmp/vbp-manifest-resolver");
mkdirSync(tmpdir, { recursive: true });
const cacheDir = join(firRoot,
  ".lake_cache/leanprover--lean4---v4.34.0-rc2");
mkdirSync(cacheDir, { recursive: true, mode: 0o700 });
chmodSync(cacheDir, 0o700);
const buildEnv = {
  LAKE_CACHE_DIR: cacheDir,
  LAKE_ARTIFACT_CACHE: "true",
  LAKE_RESTORE_ARTIFACTS: "true",
  TMPDIR: tmpdir,
};
run("lake", ["--keep-toolchain", "--reconfigure", `-KvbpRoot=${vbpRoot}`,
  "build", "VbpManifestResolverSource", "FirVbpManifestResolver.Compile"], {
  capture: false,
  env: buildEnv,
});
const lean = capture("lake", ["--keep-toolchain", "env", "which", "lean"]);
const leanPath = capture("lake", ["--keep-toolchain", "env", "printenv",
  "LEAN_PATH"]);
run(lean, ["-DmaxHeartbeats=0", "Emit.lean"], {
  capture: false,
  env: { ...buildEnv, LEAN_PATH: leanPath },
});
const packageGenerationMs = performance.now() - generationStarted;

const wasm = readFileSync(residentStem);
const baseWasm = readFileSync(baseStem);
const inventory = JSON.parse(readFileSync(
  join(buildDirectory, "vbp-manifest-resolver.inventory.json"), "utf8"));
const descriptor = JSON.parse(readFileSync(`${residentStem}.json`, "utf8"));
descriptor.completeRuntime = true;
descriptor.abiVersion = 1;
descriptor.logicalParams = ["String"];
descriptor.logicalResult = "String";
descriptor.memoryOwner = "module";
const descriptorBytes = Buffer.from(`${JSON.stringify(descriptor, null, 2)}\n`);
const adapterBytes = readFileSync(join(directory,
  "vbp-manifest-resolver-browser-adapter.mjs"));
const smokeBytes = readFileSync(join(directory, "package-smoke.mjs"));
const fixturePath = join(vbpRoot,
  "tests/fixtures/runtime-manifest-resolver.json");
const fixtureBytes = readFileSync(fixturePath);
const module = new WebAssembly.Module(wasm);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
const functionExports = exports.filter(({ kind }) => kind === "function")
  .map(({ name }) => name);
const memoryExports = exports.filter(({ kind }) => kind === "memory")
  .map(({ name }) => name);

assert.deepEqual(imports, []);
assert.deepEqual(descriptor.imports, []);
assert.equal(descriptor.entry, VBP_MANIFEST_RESOLVER_ENTRY);
assert.deepEqual(descriptor.params, ["object"]);
assert.equal(descriptor.result, "object");
assert.deepEqual(functionExports, [
  VBP_MANIFEST_RESOLVER_ENTRY,
  "fir_heap_frontier",
  "fir_heap_set_frontier",
  "fir_heap_rewind",
  "fir_heap_alloc",
]);
assert.deepEqual(memoryExports, ["memory"]);
assert.deepEqual(inventory.publicFunctions, functionExports);
assert.equal(inventory.runtimeOperations, 0);
assertOptional(inventory.capturedDeclarations,
  expectedClosure.capturedDeclarations, "captured declaration count");
assertOptional(inventory.reviewedExternalsBeforeLink,
  expectedClosure.reviewedExternalsBeforeLink, "reviewed external count");
assertOptional(inventory.sourceFunctions.length,
  expectedClosure.retainedSourceFunctions, "retained source functions");
assertOptional(sha256(JSON.stringify(inventory.sourceFunctions)),
  expectedClosure.retainedSourceFunctionSha256, "retained source inventory");
assertOptional(inventory.residentHelpers.length,
  expectedClosure.residentHelpers, "resident helper count");
assertOptional(sha256(JSON.stringify(inventory.residentHelpers)),
  expectedClosure.residentHelperSha256, "resident helper inventory");
assertOptional(inventory.functions.length,
  expectedClosure.completeFunctions, "complete function count");
assertOptional(baseWasm.byteLength,
  expectedClosure.baseWasmBytes, "base Wasm size");
assertOptional(wasm.byteLength,
  expectedClosure.completeWasmBytes, "complete Wasm size");
assertOptional(inventory.lazyCacheInitializers,
  expectedClosure.lazyCacheInitializers, "lazy cache initializer count");
assertOptional(inventory.residentGlobals,
  expectedClosure.residentGlobals, "resident global count");

const leanToolchain = readFileSync(join(directory, "lean-toolchain"), "utf8").trim();
const leanVersion = capture("lake", ["--keep-toolchain", "env", "lean",
  "--version"]);
assert.ok(leanVersion.includes("4.34.0-rc2"), "wrong Lean version");
assert.ok(leanVersion.includes("6a10ac8c22beadecabdbb0919c2b50214762f91d"),
  "wrong Lean Git commit");
const firRelevantPaths = [
  "Fir/Wasm/Emit/ResidentBigNumeric.lean",
  "Fir/Wasm/Emit/ResidentFixedWidth.lean",
  "Fir/Wasm/Emit/ResidentHash.lean",
  "Fir/Wasm/Emit/ResidentLinker.lean",
  "Fir/Wasm/Emit/ResidentName.lean",
  "Fir/Wasm/Emit/ResidentNatArithmetic.lean",
  "Fir/Wasm/Emit/ResidentNumeric.lean",
  "Fir/Wasm/Emit/ResidentString.lean",
  "Fir/Wasm/Emit/Source.lean",
];
const build = {
  schemaVersion: "fir.vbp-manifest-resolver.build/v1",
  provisional: true,
  sources: {
    fir: {
      repository: "https://github.com/ejgallego/lean-fir.git",
      ...fir,
      sourceView: "clean-git-archive-with-toolchain-local-build-state",
      relevantFiles: relevantFiles(firRoot, firRelevantPaths),
    },
    vbp: {
      repository: sourcePin.repository,
      ...vbp,
      sourceView: "clean-read-only-source-with-postponed-final-lcnf",
      relevantFiles: Object.entries(sourcePin.files).map(([path, digest]) =>
        ({ path, sha256: digest })),
    },
  },
  toolchain: {
    leanToolchain,
    leanVersion,
    leanCommit: "6a10ac8c22beadecabdbb0919c2b50214762f91d",
  },
  entry: {
    sourceModule: "VersoBlueprintRuntime.ManifestResolver",
    sourceName: VBP_MANIFEST_RESOLVER_ENTRY,
    exportName: VBP_MANIFEST_RESOLVER_ENTRY,
  },
  abi: {
    version: 1,
    logical: "String -> String",
    logicalParameters: ["String"],
    logicalResult: "String",
    physicalParameters: descriptor.params,
    physicalResult: descriptor.result,
    stringRepresentation: "lean-4.34-utf8-string-object/v1",
  },
  closure: {
    capture: "compileEntryIndividuallyInternalized+internalizeFinalDependencies",
    sourceView: "package-local-postponed-final-lcnf-module/v1",
    residentPolicy: "closedApplicationPolicy",
    capturedDeclarations: inventory.capturedDeclarations,
    capturedDeclarationNames: inventory.capturedDeclarationNames,
    reviewedExternalsBeforeLink: inventory.reviewedExternalsBeforeLink,
    reviewedExternalNamesBeforeLink: inventory.reviewedExternalNamesBeforeLink,
    retainedSourceFunctions: inventory.sourceFunctions,
  },
  residentRuntime: {
    completeFunctions: inventory.functions.length,
    residentHelpers: inventory.residentHelpers,
    residualRuntimeOperations: inventory.runtimeOperations,
    lazyCacheInitializers: inventory.lazyCacheInitializerNames,
    residentGlobals: inventory.residentGlobals,
  },
  wasm: {
    file: "vbp-manifest-resolver.wasm",
    byteLength: wasm.byteLength,
    sha256: sha256(wasm),
    baseByteLength: baseWasm.byteLength,
    baseSha256: sha256(baseWasm),
    functionImportCount: 0,
    memoryImportCount: 0,
    functionExportCount: functionExports.length,
    memoryExports,
    memoryOwner: "module",
    exports,
  },
  fixture: {
    file: "runtime-manifest-resolver.json",
    byteLength: fixtureBytes.byteLength,
    sha256: sha256(fixtureBytes),
    validAndMissingResults: 11,
    malformedManifestCases: 5,
    malformedJsonCases: 1,
  },
  capabilities: {
    completeRuntime: {
      version: "fir.vbp-manifest-resolver.complete-runtime/v1",
      selfContained: true,
      hostFallbacks: [],
    },
    browserAdapter: {
      module: "vbp-manifest-resolver-browser-adapter.mjs",
      apiVersion: VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION,
      operations: ["invoke"],
      invocation: "invoke(entry, [inputJson]) -> outputJson",
      synchronous: true,
      timings: ["fetchMs", "compileMs", "instantiateMs", "encodeMs",
        "executeMs", "decodeMs", "rewindMs", "totalMs", "overheadMs"],
    },
    inputLayout: {
      version: VBP_MANIFEST_RESOLVER_INPUT_LAYOUT_VERSION,
      abiVersion: 1,
      publicInput: "JSON String",
      publicOutput: "JSON String",
    },
    ownership: {
      version: VBP_MANIFEST_RESOLVER_OWNERSHIP_VERSION,
      memoryOwner: "module",
      publicInput: "borrowed-javascript-string",
      encodedInput: "fresh-transferred-lean-string",
      output: "decoded-javascript-string-copy",
      arena: "rewound-to-pre-call-checkpoint-on-success-or-failure",
      initializationRoots: "none",
      rawAddressesExposed: false,
      reclamation: "per-call-rewind-and-instance-drop-on-dispose",
    },
  },
  test: "node smoke.mjs",
};

const buildBytes = Buffer.from(`${JSON.stringify(build, null, 2)}\n`);
const packageFingerprint = sha256(Buffer.concat([
  wasm, descriptorBytes, adapterBytes, buildBytes, smokeBytes, fixtureBytes,
]));
const packageId = `${fir.commit.slice(0, 12)}-${vbp.commit.slice(0, 12)}-` +
  packageFingerprint.slice(0, 20);
const packages = join(buildDirectory, "vbp-manifest-resolver-packages");
const { directory: destination } = publishImmutablePackage({
  packagesDirectory: packages,
  packageId,
  outputNames: vbpManifestResolverPayloadFiles,
  currentLink: join(buildDirectory, "vbp-manifest-resolver-current"),
  populate(staging) {
    writeFileSync(join(staging, "BUILD.json"), buildBytes);
    writeFileSync(join(staging, "runtime-manifest-resolver.json"), fixtureBytes);
    writeFileSync(join(staging, "smoke.mjs"), smokeBytes);
    writeFileSync(join(staging, "vbp-manifest-resolver-browser-adapter.mjs"),
      adapterBytes);
    copyFileSync(residentStem, join(staging, "vbp-manifest-resolver.wasm"));
    writeFileSync(join(staging, "vbp-manifest-resolver.wasm.json"),
      descriptorBytes);
  },
  validate(staging) {
    verifyBrowserPackage(staging, vbpManifestResolverPackagePolicy);
  },
});

console.log(JSON.stringify({
  ok: true,
  packageId,
  directory: destination,
  packageGenerationMs,
  wasmBytes: wasm.byteLength,
  wasmSha256: build.wasm.sha256,
  capturedDeclarations: inventory.capturedDeclarations,
  retainedSourceFunctions: inventory.sourceFunctions.length,
  residentHelpers: inventory.residentHelpers.length,
  completeFunctions: inventory.functions.length,
  imports: imports.length,
  exports,
}, null, 2));
