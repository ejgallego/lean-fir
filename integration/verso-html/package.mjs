import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  copyFileSync,
  mkdirSync,
  readFileSync,
  realpathSync,
  writeFileSync,
} from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { publishImmutablePackage, sha256 } from
  "../package-tools/immutable-package.mjs";
import { buildPostponedSourceView } from
  "../package-tools/postponed-source-view.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const versoRoot = realpathSync(process.env.VERSO_ROOT ?? join(directory, ".verso"));
const buildDirectory = join(directory, "_build");
const baseStem = join(buildDirectory, "prettyM-html-base.wasm");
const residentStem = join(buildDirectory, "prettyM-html-resident.wasm");
const adapterPath = join(buildDirectory, "prettyM-browser-adapter.mjs");
const expectedSource = Object.freeze(JSON.parse(readFileSync(
  join(directory, "verso-source.json"), "utf8")));
const expectedClosure = Object.freeze(JSON.parse(readFileSync(
  join(directory, "closure-contract.json"), "utf8")));
const outputNames = [
  "BUILD.json",
  "prettyM-browser-adapter.mjs",
  "prettyM.wasm",
  "prettyM.wasm.json",
  "smoke.mjs",
];

function run(command, args, options = {}) {
  return execFileSync(command, args, {
    cwd: options.cwd ?? directory,
    encoding: options.encoding ?? "utf8",
    env: { ...process.env, ...options.env },
    stdio: options.capture === false ? "inherit" : ["ignore", "pipe", "inherit"],
    maxBuffer: options.maxBuffer ?? 64 * 1024 * 1024,
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

function assertExpectedVersoSource() {
  const source = gitState(versoRoot);
  assert.equal(source.commit, expectedSource.revision,
    "Verso source revision does not match verso-source.json");
  assert.equal(source.dirty, false, "Verso source checkout must be clean");
  for (const [path, digest] of Object.entries(expectedSource.files)) {
    assert.equal(sha256(readFileSync(join(versoRoot, path))), digest,
      `Verso source digest changed for ${path}`);
  }
  run("git", ["rev-parse", "--verify", expectedSource.remoteRef], {
    cwd: versoRoot,
  });
  run("git", ["merge-base", "--is-ancestor", expectedSource.revision,
    expectedSource.remoteRef], { cwd: versoRoot });
  return source;
}

function assertExpected(value, expected, label) {
  assert.equal(value, expected, `${label} changed`);
}

const verso = assertExpectedVersoSource();
const fir = gitState(firRoot);
if (fir.dirty && process.env.FIR_ALLOW_DIRTY_PACKAGE !== "1") {
  throw new Error("FIR checkout must be clean for immutable publication");
}

mkdirSync(buildDirectory, { recursive: true });
run("lake", ["--keep-toolchain", "--reconfigure",
  `-KversoRoot=${versoRoot}`, "build", "VersoFirHtml.Compile"],
{ capture: false });
const lean = capture("lake", ["--keep-toolchain", "env", "which", "lean"]);
const leanPath = capture("lake", ["--keep-toolchain", "env", "printenv",
  "LEAN_PATH"]);
const sourceView = buildPostponedSourceView({
  lean,
  leanPath,
  moduleName: "VersoSlides.Pretty",
  outputRoot: join(buildDirectory, "source-view", "lib", "lean"),
  packageName: "VersoFirHtmlSourceView",
  sourceFile: join(versoRoot, "VersoSlides/Pretty.lean"),
});
run(lean, ["Emit.lean"], {
  capture: false,
  env: { LEAN_PATH: sourceView.leanPath },
});
run("node", ["build-adapter.mjs", adapterPath], { capture: false });

const wasm = readFileSync(residentStem);
const baseWasm = readFileSync(baseStem);
const descriptorBytes = readFileSync(`${residentStem}.json`);
const descriptor = JSON.parse(descriptorBytes);
const inventory = JSON.parse(readFileSync(
  join(buildDirectory, "prettyM-html-resident.inventory.json"), "utf8"));
const adapterBytes = readFileSync(adapterPath);
const smokeBytes = readFileSync(join(directory, "package-smoke.mjs"));
const module = new WebAssembly.Module(wasm);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
const functionExports = exports.filter(({ kind }) => kind === "function")
  .map(({ name }) => name);
const memoryExports = exports.filter(({ kind }) => kind === "memory")
  .map(({ name }) => name);
const wasmHash = sha256(wasm);

assert.deepEqual(imports, []);
assert.deepEqual(descriptor.imports, []);
assert.equal(descriptor.entry, "VersoSlides.Pretty.formatHtmlForRuntime");
assert.deepEqual(descriptor.params,
  ["tobject", "object", "tobject", "tobject", "tobject"]);
assert.equal(descriptor.result, "object");
assert.deepEqual(functionExports, [
  descriptor.entry,
  "fir_heap_frontier",
  "fir_heap_set_frontier",
  "fir_heap_rewind",
  "fir_heap_alloc",
]);
assert.deepEqual(memoryExports, ["memory"]);
assert.deepEqual(inventory.publicFunctions, functionExports);
assertExpected(inventory.capturedDeclarations,
  expectedClosure.capturedDeclarations, "captured declaration count");
assertExpected(inventory.reviewedExternalsBeforeLink,
  expectedClosure.reviewedExternalsBeforeLink, "reviewed external count");
assertExpected(inventory.sourceFunctions.length,
  expectedClosure.retainedSourceFunctions, "retained source-function count");
assertExpected(inventory.residentHelpers.length,
  expectedClosure.residentHelpers, "resident-helper count");
assertExpected(inventory.functions.length,
  expectedClosure.completeFunctions, "complete function count");
assertExpected(baseWasm.byteLength,
  expectedClosure.baseWasmBytes, "base Wasm size");
assertExpected(wasm.byteLength,
  expectedClosure.completeWasmBytes, "complete Wasm size");
assertExpected(sha256(JSON.stringify(inventory.sourceFunctions)),
  expectedClosure.retainedSourceFunctionSha256,
  "retained source-function inventory");
assertExpected(sha256(JSON.stringify(inventory.residentHelpers)),
  expectedClosure.residentHelperSha256, "resident-helper inventory");
assertExpected(inventory.lazyCacheInitializers,
  expectedClosure.lazyCacheInitializers, "lazy-cache initializer count");
assertExpected(inventory.residentGlobals,
  expectedClosure.residentGlobals, "resident global count");
assert.equal(inventory.runtimeOperations, 0);

const leanToolchain = readFileSync(join(directory, "lean-toolchain"), "utf8").trim();
const leanVersion = capture("lake", ["--keep-toolchain", "env", "lean", "--version"]);
const build = {
  format: "fir-prettyM-package-metadata-v2",
  provisional: false,
  sourceCommit: verso.commit,
  sourceDirty: false,
  sources: {
    verso: {
      repository: expectedSource.repository,
      commit: verso.commit,
      dirty: false,
      resolution: `reachable-from-${expectedSource.remoteRef}`,
      remoteRef: expectedSource.remoteRef,
      upstreamBaseRevision: expectedSource.upstreamBaseRevision,
      relevantFiles: Object.entries(expectedSource.files).map(([path, digest]) =>
        ({ path, sha256: digest })),
    },
    fir: {
      repository: "https://github.com/ejgallego/lean-fir.git",
      commit: fir.commit,
      dirty: fir.dirty,
    },
  },
  lean: { toolchain: leanToolchain, version: leanVersion },
  entry: descriptor.entry,
  params: descriptor.params,
  result: descriptor.result,
  functionImports: 0,
  memoryImports: 0,
  memoryExports: 1,
  functionExports: functionExports.length,
  publicFunctions: functionExports,
  artifact: {
    file: "prettyM.wasm",
    bytes: wasm.byteLength,
    sha256: wasmHash,
    baseBytes: baseWasm.byteLength,
    baseSha256: sha256(baseWasm),
  },
  closure: {
    capture: "compileEntryModuleWiseInternalizedFrom+internalizeFinalDependencies",
    sourceView: "postponed-final-lcnf-module/v1",
    arenaPreparation: "prepareArenaArtifact",
    residentPolicy: "closedApplicationPolicy",
    capturedDeclarations: inventory.capturedDeclarations,
    retainedSourceFunctions: inventory.sourceFunctions.length,
    retainedSourceFunctionSha256: sha256(JSON.stringify(inventory.sourceFunctions)),
    reviewedExternalsBeforeLink: inventory.reviewedExternalsBeforeLink,
  },
  residentRuntime: {
    completeFunctions: inventory.functions.length,
    residentAndHelperFunctions: inventory.residentHelpers.length,
    residentHelperSha256: sha256(JSON.stringify(inventory.residentHelpers)),
    residualRuntimeOperations: inventory.runtimeOperations,
    lazyCacheInitializers: inventory.lazyCacheInitializerNames,
    residentGlobals: inventory.residentGlobals,
    helpers: inventory.residentHelpers,
    newlyRequiredOperations: [
      "Array.pop",
      "String.append",
      "String.push",
      "String.Pos.next",
      "String.decodeChar",
      "UInt32.decEq",
    ],
  },
  capabilities: {
    representation: "wasm32-lean64",
    memoryOwner: "module",
    frontierProtocol: {
      read: "fir_heap_frontier",
      advance: "fir_heap_set_frontier",
      rewind: "fir_heap_rewind",
      allocate: "fir_heap_alloc",
      heapBase: 1024,
      alignment: 8,
    },
    browserAdapter: {
      module: "prettyM-browser-adapter.mjs",
      apiVersion: "fir.prettyM.html.browser/v1",
      phases: ["prepare", "execute", "decode"],
      timings: ["fetchMs", "compileMs", "instantiateMs", "normalizeMs",
        "allocateMs", "encodeMs", "prepareMs", "executeMs", "decodeMs",
        "totalMs"],
    },
    inputLayout: {
      version: "lean-4.33-Std.Format.compact/v1",
      leanVersion: "4.33.0",
      representation: "compact-discriminated-union-plus-tagged-annotations",
      constructors: ["nil", "line", "align", "text", "nest", "append",
        "group", "tag"],
      annotations: "Array VersoSlides.Pretty.TaggedAnnotation",
      rawTarget: "Lean 4.33 Std.Format",
    },
    ownership: {
      version: "fir.prettyM.module-owned-transfer/v1",
      publicInput: "borrowed-immutable-javascript",
      encodedInput: "fresh-owned-lean-graphs-transferred-to-entry",
      output: "decoded-javascript-string-copy",
      rawAddressesExposed: false,
      memoryOwner: "module",
      allocator: "two-bulk-resident-allocations-per-render",
      reclamation: "instance-lifetime-bump-arena",
    },
    output: {
      semantic: "EscapedHtmlString",
      schema: "verso-token-html/v1",
      physical: "object",
      escaping: "html-text-and-double-quoted-attribute/v1",
    },
  },
  test: "node smoke.mjs",
};

const buildBytes = Buffer.from(`${JSON.stringify(build, null, 2)}\n`);
const packageFingerprint = sha256(Buffer.concat([
  wasm, descriptorBytes, adapterBytes, buildBytes, smokeBytes,
]));
const packageId = `${fir.commit.slice(0, 12)}-${verso.commit.slice(0, 12)}-` +
  packageFingerprint.slice(0, 20);
const packages = join(buildDirectory, "verso-html-packages");
const { directory: destination } = publishImmutablePackage({
  packagesDirectory: packages,
  packageId,
  outputNames,
  currentLink: join(buildDirectory, "verso-html-current"),
  populate(staging) {
    copyFileSync(residentStem, join(staging, "prettyM.wasm"));
    copyFileSync(`${residentStem}.json`, join(staging, "prettyM.wasm.json"));
    writeFileSync(join(staging, "prettyM-browser-adapter.mjs"), adapterBytes);
    writeFileSync(join(staging, "smoke.mjs"), smokeBytes);
    writeFileSync(join(staging, "BUILD.json"), buildBytes);
  },
});
console.log(JSON.stringify({
  ok: true,
  packageId,
  directory: destination,
  wasmBytes: wasm.byteLength,
  wasmSha256: wasmHash,
  functionImports: 0,
  memoryImports: 0,
  sourceFunctions: inventory.sourceFunctions.length,
  residentHelpers: inventory.residentHelpers.length,
}));
