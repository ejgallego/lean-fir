import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  chmodSync,
  copyFileSync,
  existsSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { dirname, join, relative } from "node:path";
import { performance } from "node:perf_hooks";
import { fileURLToPath } from "node:url";

import {
  publishImmutablePackage,
  sha256,
} from "../package-tools/immutable-package.mjs";
import { verifyBrowserPackage } from
  "../package-tools/verified-package.mjs";
import {
  LEAN_COMPONENT_RUNTIME_PROVIDER_API,
  VBP_VERSO_VIEWER_ADAPTER_API_VERSION,
  VBP_VERSO_VIEWER_BRIDGE_ENTRIES,
  VBP_VERSO_VIEWER_HOST_IMPORTS,
  VBP_VERSO_VIEWER_INPUT_LAYOUT_VERSION,
  VBP_VERSO_VIEWER_MOUNT_ENTRY,
  VBP_VERSO_VIEWER_OWNERSHIP_VERSION,
  VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
} from "./vbp-verso-viewer-browser-adapter.mjs";
import {
  vbpVersoViewerPackagePolicy,
  vbpVersoViewerPayloadFiles,
} from "./package-policy.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const sourceContract = Object.freeze(JSON.parse(readFileSync(
  join(directory, "source-contract.json"), "utf8")));
const expectedClosure = Object.freeze(JSON.parse(readFileSync(
  join(directory, "closure-contract.json"), "utf8")));
const vbpRoot = realpathSync(process.env.VBP_ROOT ?? join(firRoot,
  sourceContract.vbp.sourceView));
const virRoot = realpathSync(process.env.VIR_ROOT ?? join(firRoot,
  sourceContract.vir.sourceView));
const buildDirectory = join(directory, "_build");
const firSourceRoot = join(firRoot,
  ".deps/source-views/fir-vbp-verso-viewer");
const baseStem = join(buildDirectory, "vbp-verso-viewer-base.wasm");
const residentStem = join(buildDirectory, "vbp-verso-viewer.wasm");

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
  return paths.map((path) => ({
    path,
    sha256: sha256(readFileSync(join(root, path))),
  }));
}

function leanTreeDigest(root, specification) {
  const base = join(root, specification.path);
  const files = [];
  function walk(path) {
    for (const entry of readdirSync(path, { withFileTypes: true })) {
      const child = join(path, entry.name);
      if (entry.isDirectory()) walk(child);
      else if (entry.isFile() && entry.name.endsWith(".lean")) files.push(child);
    }
  }
  walk(base);
  files.sort();
  const parts = [];
  for (const path of files) {
    parts.push(Buffer.from(relative(root, path)), Buffer.from([0]),
      readFileSync(path), Buffer.from([0]));
  }
  return { files: files.length, sha256: sha256(Buffer.concat(parts)) };
}

function assertPinnedSource(root, specification, label) {
  for (const [path, digest] of Object.entries(specification.files)) {
    assert.equal(sha256(readFileSync(join(root, path))), digest,
      `${label} source digest changed for ${path}`);
  }
  assert.deepEqual(leanTreeDigest(root, specification.leanTree), {
    files: specification.leanTree.files,
    sha256: specification.leanTree.sha256,
  }, `${label} Lean source tree changed`);
  return {
    commit: specification.revision,
    dirty: false,
    sourceView: "read-only-content-pinned-source-view",
    relevantFiles: Object.entries(specification.files).map(([path, digest]) =>
      ({ path, sha256: digest })),
    leanTree: specification.leanTree,
  };
}

function prepareFirSourceArchive(commit) {
  const marker = join(firSourceRoot, ".fir-source-commit");
  if (existsSync(marker) && readFileSync(marker, "utf8").trim() === commit) {
    return firSourceRoot;
  }
  rmSync(firSourceRoot, { recursive: true, force: true });
  mkdirSync(firSourceRoot, { recursive: true });
  const archive = join(firRoot, ".deps/source-views",
    `.fir-vbp-verso-viewer-${commit}.tar`);
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
const vbp = assertPinnedSource(vbpRoot, sourceContract.vbp, "VBP");
const vir = assertPinnedSource(virRoot, sourceContract.vir, "VIR");
const fir = gitState(firRoot);
const reuseEmittedArtifact =
  process.env.FIR_REUSE_EMITTED_ARTIFACT === "1";
if (fir.dirty && process.env.FIR_ALLOW_DIRTY_PACKAGE !== "1") {
  throw new Error("FIR checkout must be clean for immutable publication");
}
mkdirSync(buildDirectory, { recursive: true });
const tmpdir = join(firRoot, ".deps/tmp/vbp-verso-viewer");
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
if (reuseEmittedArtifact) {
  assert.equal(process.env.FIR_ALLOW_DIRTY_PACKAGE, "1",
    "artifact reuse is a development-only dirty-package mode");
  for (const path of [baseStem, residentStem, `${residentStem}.json`,
    join(buildDirectory, "vbp-verso-viewer.inventory.json")]) {
    assert.ok(existsSync(path), `reused emitted artifact is missing ${path}`);
  }
} else {
  prepareFirSourceArchive(fir.commit);
  run("lake", ["--keep-toolchain", "--reconfigure", `-KvbpRoot=${vbpRoot}`,
    "build", "VbpVersoViewerSource", "FirVbpVersoViewer.Compile"], {
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
}
const packageGenerationMs = performance.now() - generationStarted;

const wasm = readFileSync(residentStem);
const baseWasm = readFileSync(baseStem);
const inventoryPath = join(buildDirectory, "vbp-verso-viewer.inventory.json");
const inventoryBytes = readFileSync(inventoryPath);
const inventory = JSON.parse(inventoryBytes);
const descriptor = JSON.parse(readFileSync(`${residentStem}.json`, "utf8"));
descriptor.completeRuntime = false;
descriptor.completeResidentRuntime = true;
descriptor.abiVersion = 1;
descriptor.logicalEntries = [{
  name: VBP_VERSO_VIEWER_MOUNT_ENTRY,
  params: ["String", "Lean.Vir.Infoview.RpcJson"],
  result: "Bool",
  effect: "DomM",
}, {
  name: VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
  params: ["String"],
  result: "Bool",
  effect: "DomM",
}];
descriptor.publicSignatures = inventory.publicSignatures;
const descriptorBytes = Buffer.from(`${JSON.stringify(descriptor, null, 2)}\n`);
const adapterBytes = readFileSync(join(directory,
  "vbp-verso-viewer-browser-adapter.mjs"));
const smokeBytes = readFileSync(join(directory, "package-smoke.mjs"));
const module = new WebAssembly.Module(wasm);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
const functionImports = imports.filter(({ kind }) => kind === "function");
const memoryImports = imports.filter(({ kind }) => kind === "memory");
const functionExports = exports.filter(({ kind }) => kind === "function")
  .map(({ name }) => name);
const memoryExports = exports.filter(({ kind }) => kind === "memory")
  .map(({ name }) => name);
const expectedHostNames = VBP_VERSO_VIEWER_HOST_IMPORTS
  .map(({ declaration }) => declaration).toSorted();

assert.equal(imports.length, 41);
assert.equal(functionImports.length, 41);
assert.equal(memoryImports.length, 0);
assert.ok(imports.every(({ module: namespace, kind }) =>
  namespace === "lean.extern" && kind === "function"));
assert.deepEqual(imports.map(({ name }) => name).toSorted(), expectedHostNames);
assert.deepEqual(descriptor.imports.map(({ name }) => name).toSorted(),
  expectedHostNames);
assert.equal(descriptor.entry, VBP_VERSO_VIEWER_MOUNT_ENTRY);
assert.deepEqual(descriptor.params, ["object", "tobject", "erased"]);
assert.equal(descriptor.result, "object");
assert.deepEqual(functionExports, [
  VBP_VERSO_VIEWER_MOUNT_ENTRY,
  VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
  ...VBP_VERSO_VIEWER_BRIDGE_ENTRIES,
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
  "integration/vbp-verso-viewer/FirVbpVersoViewer/Bridge.lean",
  "integration/vbp-verso-viewer/FirVbpVersoViewer/Compile.lean",
  "Fir/Wasm/Lower.lean",
  "Fir/Wasm/Emit/CompilerPrivate.lean",
  "Fir/Wasm/Emit/Manifest.lean",
  "Fir/Wasm/Emit/ResidentAllocator.lean",
  "Fir/Wasm/Emit/ResidentLinker.lean",
  "Fir/Wasm/Emit/Source.lean",
];
const hostFrontier = inventory.imports.map((import_) => ({
  declaration: import_.declaration,
  module: import_.module,
  name: import_.name,
  params: import_.params,
  results: import_.results,
  binding: VBP_VERSO_VIEWER_HOST_IMPORTS.find(
    ({ declaration }) => declaration === import_.name)?.binding,
}));
assert.ok(hostFrontier.every(({ binding }) => typeof binding === "string"));

const build = {
  schemaVersion: "fir.vbp-verso-viewer.build/v1",
  provisional: true,
  sources: {
    fir: {
      repository: "https://github.com/ejgallego/lean-fir.git",
      ...fir,
      sourceView: "clean-git-archive-with-toolchain-local-build-state",
      relevantFiles: relevantFiles(firRoot, firRelevantPaths),
    },
    vbp: { repository: sourceContract.vbp.repository, ...vbp },
    vir: { repository: sourceContract.vir.repository, ...vir },
    verso: {
      repository: sourceContract.verso.repository,
      commit: sourceContract.verso.revision,
      dirty: false,
      relevantFiles: [],
    },
  },
  toolchain: {
    leanToolchain,
    leanVersion,
    leanCommit: "6a10ac8c22beadecabdbb0919c2b50214762f91d",
  },
  entries: {
    sourceModule: "VersoBlueprintVir.Preview.Widget",
    mount: VBP_VERSO_VIEWER_MOUNT_ENTRY,
    unmount: VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
    bridges: VBP_VERSO_VIEWER_BRIDGE_ENTRIES,
    publicSignatures: inventory.publicSignatures,
  },
  upstreamPackageShape: {
    moduleMembers: 66,
    declarations: 1972,
    logicalExports: 2,
    hostImports: 41,
  },
  abi: {
    version: 1,
    logical: {
      mount: "String -> Lean.Vir.Infoview.RpcJson -> DomM Bool",
      unmount: "String -> DomM Bool",
      callbacks: "borrowed synchronous retained React/event/state/effect closures",
    },
    physical: inventory.publicSignatures,
    runtimeResult: "Lean EStateM.Result object",
    hostResources: "opaque module-memory handles resolved by the adapter",
  },
  closure: {
    capture: "compileEntriesIndividuallyInternalized+boxed-adapters+final-dependencies",
    sourceView: "package-local-postponed-final-lcnf-modules/v1",
    residentPolicy: "closedApplicationAvailablePolicy+reviewed-host-frontier",
    capturedDeclarations: inventory.capturedDeclarations,
    reviewedExternalsBeforeLink: inventory.reviewedExternalsBeforeLink,
    retainedSourceFunctions: inventory.sourceFunctions.length,
    retainedSourceFunctionSha256: sha256(JSON.stringify(inventory.sourceFunctions)),
  },
  residentRuntime: {
    completeWithinLeanBoundary: true,
    completeFunctions: inventory.functions.length,
    residentHelpers: inventory.residentHelpers.length,
    residentHelperSha256: sha256(JSON.stringify(inventory.residentHelpers)),
    residualRuntimeOperations: inventory.runtimeOperations,
    lazyCacheInitializers: inventory.lazyCacheInitializerNames,
    residentGlobals: inventory.residentGlobals,
    inventory: {
      file: "runtime-inventory.json",
      byteLength: inventoryBytes.byteLength,
      sha256: sha256(inventoryBytes),
    },
  },
  hostFrontier: {
    version: "lean-vir/react-browser-host-bindings/v1",
    functionImportCount: functionImports.length,
    memoryImportCount: memoryImports.length,
    undocumentedFallbacks: [],
    operations: hostFrontier,
  },
  wasm: {
    file: "vbp-verso-viewer.wasm",
    descriptorFile: "vbp-verso-viewer.wasm.json",
    descriptorSha256: sha256(descriptorBytes),
    byteLength: wasm.byteLength,
    sha256: sha256(wasm),
    baseByteLength: baseWasm.byteLength,
    baseSha256: sha256(baseWasm),
    functionImportCount: functionImports.length,
    memoryImportCount: memoryImports.length,
    imports,
    functionExportCount: functionExports.length,
    memoryExports,
    memoryOwner: "module",
    exports,
  },
  capabilities: {
    provider: {
      apiVersion: LEAN_COMPONENT_RUNTIME_PROVIDER_API,
      factory: "createVbpVersoViewerComponentRuntimeProvider",
      fetchFactory: "fetchVbpVersoViewerComponentRuntimeProvider",
      callsAfterOpen: "synchronous",
    },
    browserAdapter: {
      module: "vbp-verso-viewer-browser-adapter.mjs",
      apiVersion: VBP_VERSO_VIEWER_ADAPTER_API_VERSION,
      operations: ["mount", "unmount"],
      timings: ["fetchMs", "compileMs", "instantiateMs", "encodeMs",
        "executeMs", "decodeMs", "totalMs", "overheadMs"],
    },
    inputLayout: {
      version: VBP_VERSO_VIEWER_INPUT_LAYOUT_VERSION,
      abiVersion: 1,
      mount: ["selector String", "Lean.Vir.Infoview.RpcJson-shaped object"],
      unmount: ["selector String"],
    },
    ownership: {
      version: VBP_VERSO_VIEWER_OWNERSHIP_VERSION,
      memoryOwner: "module",
      arena: "monotonic-instance-lifetime",
      input: "fresh-transferred-Lean-graph-per-call",
      output: "copied-JavaScript-Boolean",
      callbacks: "retained-by-explicit-JavaScript-leases-and-borrowed-by-each-Lean-bridge-call-until-release-or-dispose",
      hostResources: "adapter-owned-opaque-handle-table-until-dispose",
      rawAddressesExposed: false,
      reclamation: "unmount-releases-root-leases; dispose-invalidates-callbacks-and-drops-instance",
    },
  },
  referenceAcceptance: sourceContract.referenceAcceptance,
  test: "node smoke.mjs",
};

const buildBytes = Buffer.from(`${JSON.stringify(build, null, 2)}\n`);
const packageFingerprint = sha256(Buffer.concat([
  wasm, descriptorBytes, adapterBytes, buildBytes, inventoryBytes, smokeBytes,
]));
const packageId = `${fir.commit.slice(0, 12)}-${vbp.commit.slice(0, 12)}-` +
  `${vir.commit.slice(0, 12)}-${packageFingerprint.slice(0, 20)}`;
const packages = join(buildDirectory, "vbp-verso-viewer-packages");
const { directory: destination } = publishImmutablePackage({
  packagesDirectory: packages,
  packageId,
  outputNames: vbpVersoViewerPayloadFiles,
  currentLink: join(buildDirectory, "vbp-verso-viewer-current"),
  populate(staging) {
    writeFileSync(join(staging, "BUILD.json"), buildBytes);
    writeFileSync(join(staging, "runtime-inventory.json"), inventoryBytes);
    writeFileSync(join(staging, "smoke.mjs"), smokeBytes);
    writeFileSync(join(staging, "vbp-verso-viewer-browser-adapter.mjs"),
      adapterBytes);
    copyFileSync(residentStem, join(staging, "vbp-verso-viewer.wasm"));
    writeFileSync(join(staging, "vbp-verso-viewer.wasm.json"),
      descriptorBytes);
  },
  validate(staging) {
    verifyBrowserPackage(staging, vbpVersoViewerPackagePolicy);
    run(process.execPath, ["smoke.mjs"], { cwd: staging, capture: false });
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
  imports,
  exports,
}, null, 2));
