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

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const versoRoot = realpathSync(process.env.VERSO_ROOT ?? join(directory, ".verso"));
const buildDirectory = join(directory, "_build");
const baseStem = join(buildDirectory, "prettyM-flat-base.wasm");
const residentStem = join(buildDirectory, "prettyM-flat-resident.wasm");
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
    stdio: options.capture === false ? "inherit" : ["ignore", "pipe", "inherit"],
    maxBuffer: options.maxBuffer ?? 64 * 1024 * 1024,
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

function assertExpectedVersoSource() {
  const source = gitState(versoRoot);
  assert.equal(source.commit, expectedSource.revision,
    "Verso source revision does not match verso-source.json");
  assert.equal(source.dirty, false, "Verso source checkout must be clean");
  for (const [path, digest] of Object.entries(expectedSource.files)) {
    assert.equal(sha256(readFileSync(join(versoRoot, path))), digest,
      `Verso source digest changed for ${path}`);
  }
  if (expectedSource.remoteRef !== null) {
    run("git", ["rev-parse", "--verify", expectedSource.remoteRef], {
      cwd: versoRoot,
    });
    run("git", ["merge-base", "--is-ancestor", expectedSource.revision,
      expectedSource.remoteRef], { cwd: versoRoot });
  }
  return source;
}

function assertExpected(value, expected, label) {
  assert.equal(value, expected, `${label} changed`);
}

function assertOptionalDigest(items, expected, label) {
  if (expected !== null) {
    assert.equal(sha256(JSON.stringify(items)), expected, `${label} changed`);
  }
}

function replaceCurrentLink(destination) {
  const current = join(buildDirectory, "verso-flat-current");
  const temporary = join(buildDirectory, `.verso-flat-current-${process.pid}`);
  rmSync(temporary, { force: true });
  symlinkSync(relative(buildDirectory, destination), temporary);
  renameSync(temporary, current);
  assert.equal(lstatSync(current).isSymbolicLink(), true);
  assert.equal(realpathSync(current), realpathSync(destination));
}

const verso = assertExpectedVersoSource();
const fir = gitState(firRoot);
if (fir.dirty && process.env.FIR_ALLOW_DIRTY_PACKAGE !== "1") {
  throw new Error("FIR checkout must be clean for immutable publication");
}

mkdirSync(buildDirectory, { recursive: true });
run("lake", ["--keep-toolchain", "--reconfigure",
  `-KversoRoot=${versoRoot}`, "build", "VersoFirFlat.Compile"],
{ capture: false });
run("lake", ["--keep-toolchain", `-KversoRoot=${versoRoot}`, "env", "lean",
  "Emit.lean"], { capture: false });
run("node", ["build-adapter.mjs", adapterPath], { capture: false });

const wasm = readFileSync(residentStem);
const baseWasm = readFileSync(baseStem);
const descriptorBytes = readFileSync(`${residentStem}.json`);
const descriptor = JSON.parse(descriptorBytes);
const inventory = JSON.parse(readFileSync(
  join(buildDirectory, "prettyM-flat-resident.inventory.json"), "utf8"));
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
assert.equal(descriptor.entry,
  "VersoSlides.Pretty.formatRenderedForRuntime");
assert.deepEqual(descriptor.params, ["tobject", "tobject", "tobject", "tobject"]);
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
assertOptionalDigest(inventory.sourceFunctions,
  expectedClosure.retainedSourceFunctionSha256,
  "retained source-function inventory");
assertOptionalDigest(inventory.residentHelpers,
  expectedClosure.residentHelperSha256, "resident-helper inventory");
assertExpected(inventory.lazyCacheInitializers,
  expectedClosure.lazyCacheInitializers, "lazy-cache initializer count");
assertExpected(inventory.residentGlobals,
  expectedClosure.residentGlobals, "resident global count");
assert.equal(inventory.runtimeOperations, 0);

const leanToolchain = readFileSync(join(directory, "lean-toolchain"), "utf8").trim();
const leanVersion = capture("lake", ["--keep-toolchain", "env", "lean", "--version"]);
const sourceFile = Object.keys(expectedSource.files)[0];
const sourceResolution = expectedSource.remoteRef === null ?
  "clean-local-commit-awaiting-remote-pin" : `reachable-from-${expectedSource.remoteRef}`;
const build = {
  format: "fir-prettyM-package-metadata-v2",
  provisional: expectedSource.remoteRef === null,
  provisionalReason: expectedSource.remoteRef === null ?
    "Verso owner has not yet published the clean capture-refactor commit" : null,
  sourceCommit: verso.commit,
  sourceDirty: false,
  sources: {
    verso: {
      repository: expectedSource.repository,
      commit: verso.commit,
      dirty: false,
      resolution: sourceResolution,
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
    capture: "compileEntryFinalCapturedInternalized",
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
    families: [
      "allocator and raw scalar stores",
      "constructor and Array allocation",
      "closure allocation, projection, matching, and dispatch",
      "reference increments and recursive release",
      "tag, field, and cache mutation",
      "arbitrary-precision Nat and Int",
      "UTF-8 String operations and literals",
      "UInt8 box and UInt8/UInt32 unbox",
      "fail-closed runtime fallbacks",
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
      apiVersion: "fir.prettyM.flat.browser/v1",
      phases: ["prepare", "execute", "decode", "render"],
      timings: ["fetchMs", "compileMs", "instantiateMs", "normalizeMs",
        "allocateMs", "encodeMs", "prepareMs", "executeMs", "decodeMs",
        "totalMs"],
    },
    inputLayout: {
      version: "lean-4.32-Std.Format.compact/v1",
      leanVersion: "4.32.0",
      representation: "compact-discriminated-union",
      constructors: ["nil", "line", "align", "text", "nest", "append",
        "group", "tag"],
      rawTarget: "Lean 4.32 Std.Format",
    },
    ownership: {
      version: "fir.prettyM.module-owned-transfer/v1",
      publicInput: "borrowed-immutable-javascript",
      encodedInput: "fresh-owned-lean-graph-transferred-to-entry",
      output: "decoded-javascript-copy",
      rawAddressesExposed: false,
      memoryOwner: "module",
      allocator: "single-bulk-resident-allocation-per-render",
      reclamation: "instance-lifetime-bump-arena",
    },
    output: {
      semantic: "RenderedTextEvents",
      schema: "text-events-utf8/v1",
      physical: "object",
      textProjection: "String",
      offsetUnit: "utf8-byte",
      eventKinds: { startTag: 0, endTags: 1, unstyledNewline: 2 },
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
const packages = join(buildDirectory, "verso-flat-packages");
const destination = join(packages, packageId);
const staging = join(packages, `.staging-${packageId}-${process.pid}`);
mkdirSync(packages, { recursive: true });
rmSync(staging, { recursive: true, force: true });
mkdirSync(staging);
copyFileSync(residentStem, join(staging, "prettyM.wasm"));
copyFileSync(`${residentStem}.json`, join(staging, "prettyM.wasm.json"));
writeFileSync(join(staging, "prettyM-browser-adapter.mjs"), adapterBytes);
writeFileSync(join(staging, "smoke.mjs"), smokeBytes);
writeFileSync(join(staging, "BUILD.json"), buildBytes);
const sums = outputNames.map((name) =>
  `${sha256(readFileSync(join(staging, name)))}  ${name}`).join("\n") + "\n";
writeFileSync(join(staging, "SHA256SUMS"), sums);

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
replaceCurrentLink(destination);
console.log(JSON.stringify({
  ok: true,
  provisional: build.provisional,
  packageId,
  directory: destination,
  sourceFile,
  sourceResolution,
  wasmBytes: wasm.byteLength,
  wasmSha256: wasmHash,
  functionImports: 0,
  memoryImports: 0,
  sourceFunctions: inventory.sourceFunctions.length,
  residentHelpers: inventory.residentHelpers.length,
}));
