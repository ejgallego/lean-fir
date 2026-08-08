import assert from "node:assert/strict";
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
import { createHash } from "node:crypto";
import { dirname, join, relative } from "node:path";
import { fileURLToPath } from "node:url";

import {
  ILLUMINATE_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-player-browser-adapter.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const illuminateRoot = realpathSync(process.env.ILLUMINATE_ROOT ??
  join(directory, ".illuminate"));
const buildDirectory = join(directory, "_build");
const baseStem = join(buildDirectory, "illuminate-player-base.wasm");
const generatedStem = join(buildDirectory, "illuminate-player-resident.wasm");
const illuminateSourceFiles = [
  "src/Illuminate/Animation/Types.lean",
  "src/Illuminate/Animation/Player.lean",
];
const expectedClosure = Object.freeze({
  finalLcnfDeclarations: 115,
  finalLcnfDeclarationSha256:
    "3113b9072ef0af29b09e6a4ebb1eb90270f52ed68a6d43f3e75ef7d7fc01b53e",
  retainedSourceFunctions: 73,
  retainedSourceFunctionSha256:
    "8674052933b8c801deff6a48b9a6de0488d81acad9305c7cb229277390611586",
  residentHelpers: 184,
  residentHelperSha256:
    "8171feb2e3773e675bbe1c733193ac76fe6215780ef5756084b8f8e4a898b320",
  baseWasmBytes: 21977,
  completeWasmBytes: 53888,
});
const outputNames = [
  "BUILD.json",
  "illuminate-player-browser-adapter.mjs",
  "illuminate-player.wasm",
  "illuminate-player.wasm.json",
  "smoke.mjs",
];

function run(command, args, options = {}) {
  return execFileSync(command, args, {
    cwd: directory,
    encoding: "utf8",
    stdio: options.capture ? ["ignore", "pipe", "inherit"] : "inherit",
  });
}

function capture(command, args) {
  return run(command, args, { capture: true }).trim();
}

function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

function sourceFileState(root, path) {
  const tracked = capture("git", ["-C", root, "ls-files", "--", path]) === path;
  return {
    path,
    tracked,
    status: capture("git", ["-C", root, "status", "--porcelain", "--", path]) ||
      "clean",
    sha256: sha256(readFileSync(join(root, path))),
  };
}

function sourceState(root, relevantFiles = []) {
  return {
    commit: capture("git", ["-C", root, "rev-parse", "HEAD"]),
    dirty: capture("git", ["-C", root, "status", "--porcelain"]) !== "",
    relevantFiles: relevantFiles.map((path) => sourceFileState(root, path)),
  };
}

function sourceDeclarations(text) {
  return text.split("\n")
    .filter((line) => line.startsWith("def "))
    .map((line) => line.slice(4).split(/\s/, 1)[0]);
}

function replaceCurrentLink(targetDirectory) {
  const current = join(buildDirectory, "illuminate-player-current");
  const temporary = join(buildDirectory,
    `.illuminate-player-current-${process.pid}`);
  rmSync(temporary, { force: true });
  symlinkSync(relative(buildDirectory, targetDirectory), temporary);
  renameSync(temporary, current);
  assert.equal(lstatSync(current).isSymbolicLink(), true);
  assert.equal(realpathSync(current), realpathSync(targetDirectory));
}

mkdirSync(buildDirectory, { recursive: true });
run("lake", [
  "--keep-toolchain",
  `-KilluminateRoot=${illuminateRoot}`,
  "build",
  "IlluminateFirNative.Compile",
]);
run("lake", [
  "--keep-toolchain",
  `-KilluminateRoot=${illuminateRoot}`,
  "env",
  "lean",
  "Emit.lean",
]);

const wasm = readFileSync(generatedStem);
const baseWasm = readFileSync(baseStem);
const descriptorBytes = readFileSync(`${generatedStem}.json`);
const descriptor = JSON.parse(descriptorBytes);
const inventory = JSON.parse(readFileSync(`${generatedStem}.inventory.json`,
  "utf8"));
const lcnf = readFileSync(`${generatedStem}.lcnf`, "utf8");
const module = new WebAssembly.Module(wasm);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
const functionImports = imports.filter((item) => item.kind === "function");
const memoryImports = imports.filter((item) => item.kind === "memory");
const functionExports = exports.filter((item) => item.kind === "function")
  .map((item) => item.name);
const memoryExports = exports.filter((item) => item.kind === "memory")
  .map((item) => item.name);
const declarations = sourceDeclarations(lcnf);
const wasmHash = sha256(wasm);
const adapterBytes = readFileSync(join(directory,
  "illuminate-player-browser-adapter.mjs"));
const smokeBytes = readFileSync(join(directory, "package-smoke.mjs"));
const fir = sourceState(firRoot);
const illuminate = sourceState(illuminateRoot, illuminateSourceFiles);
const leanToolchain = readFileSync(join(directory, "lean-toolchain"), "utf8")
  .trim();
const leanVersion = capture("lake", ["--keep-toolchain", "env", "lean",
  "--version"]);

assert.deepEqual(imports, []);
assert.deepEqual(descriptor.imports, []);
assert.equal(memoryExports.includes("memory"), true);
assert.equal(functionExports.includes(descriptor.entry), true);
assert.deepEqual(functionExports, [
  descriptor.entry,
  "fir_heap_frontier",
  "fir_heap_set_frontier",
  "fir_heap_alloc",
]);
assert.deepEqual(inventory.publicFunctions, functionExports);
assert.equal(inventory.functions.length,
  inventory.sourceFunctions.length + inventory.residentHelpers.length);
assert.equal(inventory.internalFunctions.length,
  inventory.functions.length - functionExports.length);
assert.equal(descriptor.sourceEntry,
  "Illuminate.AnimationPlayer.replayTrace");
assert.deepEqual(descriptor.params, ["object", "tobject"]);
assert.equal(descriptor.result, "object");
assert.equal(declarations.length, expectedClosure.finalLcnfDeclarations,
  "Illuminate final-LCNF source declaration inventory changed");
assert.equal(sha256(JSON.stringify(declarations)),
  expectedClosure.finalLcnfDeclarationSha256,
  "Illuminate final-LCNF declaration names changed");
assert.equal(inventory.sourceFunctions.length,
  expectedClosure.retainedSourceFunctions);
assert.equal(sha256(JSON.stringify(inventory.sourceFunctions)),
  expectedClosure.retainedSourceFunctionSha256,
  "Illuminate retained source-function inventory changed");
assert.equal(inventory.residentHelpers.length, expectedClosure.residentHelpers);
assert.equal(sha256(JSON.stringify(inventory.residentHelpers)),
  expectedClosure.residentHelperSha256,
  "Illuminate resident-helper inventory changed");
assert.equal(baseWasm.byteLength, expectedClosure.baseWasmBytes,
  "Illuminate base Wasm size changed");
assert.equal(wasm.byteLength, expectedClosure.completeWasmBytes,
  "Illuminate complete-runtime Wasm size changed");

const build = {
  schemaVersion: "fir.illuminate-player.build/v1",
  sources: { fir, illuminate },
  toolchain: { leanToolchain, leanVersion },
  entry: {
    sourceName: descriptor.sourceEntry,
    exportName: descriptor.entry,
    parameters: [
      { name: "animation", lean: "Illuminate.PlayerAnimation", fir: "object" },
      { name: "events", lean: "List PlayerEvent", fir: "tobject" },
    ],
    result: {
      lean: "Except String (Array FrameAction)",
      fir: "object",
    },
  },
  wasm: {
    file: "illuminate-player.wasm",
    byteLength: wasm.byteLength,
    sha256: wasmHash,
    base: {
      byteLength: baseWasm.byteLength,
      sha256: sha256(baseWasm),
    },
    functionImportCount: functionImports.length,
    memoryImportCount: memoryImports.length,
    memoryOwner: "module",
    memoryExports,
    functionExportCount: functionExports.length,
  },
  capabilities: {
    completeRuntime: {
      version: "fir.illuminate-player.complete-runtime/v1",
      selfContained: true,
      unresolvedRuntimeOperations: imports,
    },
    browserAdapter: {
      apiVersion: ILLUMINATE_PLAYER_ADAPTER_API_VERSION,
      phases: ["prepare", "execute", "decode", "replayTrace"],
      timing: {
        projectMs: "browser animation to SVG-free PlayerAnimation object",
        encodeMs: "PlayerAnimation and event graph encoding into Wasm memory",
        prepareMs: "frontier sync, projection, encoding, and argument preparation",
        executeMs: "only the exported Wasm replayTrace call",
        decodeMs: "Except and FrameAction decoding into copied JavaScript values",
        totalMs: "independent wall interval around replayTrace",
        overheadMs: "total minus project, encode, execute, and decode intervals",
      },
      result: "normalized FrameAction objects",
    },
    inputLayout: {
      version: ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION,
      leanType: "Illuminate.PlayerAnimation",
      projection: "compact browser animation projected exactly once",
      svg: "segment sync SVG is omitted and never transferred",
      naturals: "validated once as uint32-safe JavaScript integers and retained as Lean Nat",
      floatBoundary: "IEEE-754 binary64, little-endian, bit-exact",
      events: ["advance", "pause", "seek", "playTo", "loopAt", "tick"],
    },
    ownership: {
      version: ILLUMINATE_PLAYER_OWNERSHIP_VERSION,
      memoryOwner: "Wasm module",
      input: "fresh persistent Lean graph transferred into module memory",
      output: "decoded JavaScript copy; no raw address escapes the adapter",
      reclamation: "instance-lifetime monotonic arena; discard instance to reclaim",
      repeatedCalls: "frontier synchronized monotonically before and after every phase",
    },
  },
  runtime: {
    sourceDeclarationCount: declarations.length,
    sourceDeclarations: declarations,
    sourceDeclarationSha256: sha256(JSON.stringify(declarations)),
    functionCount: inventory.functions.length,
    publicFunctions: functionExports,
    internalFunctionCount: inventory.internalFunctions.length,
    retainedSourceFunctionCount: inventory.sourceFunctions.length,
    retainedSourceFunctions: inventory.sourceFunctions,
    retainedSourceFunctionSha256:
      sha256(JSON.stringify(inventory.sourceFunctions)),
    residentHelperCount: inventory.residentHelpers.length,
    residentHelpers: inventory.residentHelpers,
    residentHelperSha256: sha256(JSON.stringify(inventory.residentHelpers)),
    helperFamilies: [
      "object projections and scalar projections",
      "module-owned allocation and scalar stores",
      "constructors, setters, increments, releases, and cache setters",
      "small and big Nat operations",
      "Float subtraction, division, multiplication, comparison, round, and toUInt64",
      "Array allocation, size/usize, Nat/USize reads, and push",
      "USize comparison and addition",
      "Nat.mod and bounded Nat.shiftRight",
      "resident UTF-8 string literals",
    ],
    capturedSourceSpecializations: inventory.sourceFunctions.filter((name) =>
      name.includes(".spec_")),
  },
};

const buildBytes = Buffer.from(`${JSON.stringify(build, null, 2)}\n`);
const packageFingerprint = sha256(Buffer.concat([
  wasm, descriptorBytes, adapterBytes, buildBytes, smokeBytes,
]));
const packageId = `${fir.commit.slice(0, 12)}-${illuminate.commit.slice(0, 12)}-` +
  packageFingerprint.slice(0, 20);
const packages = join(buildDirectory, "illuminate-player-packages");
const destination = join(packages, packageId);
const staging = join(packages, `.staging-${packageId}-${process.pid}`);
mkdirSync(packages, { recursive: true });
rmSync(staging, { recursive: true, force: true });
mkdirSync(staging);
copyFileSync(generatedStem, join(staging, "illuminate-player.wasm"));
copyFileSync(`${generatedStem}.json`,
  join(staging, "illuminate-player.wasm.json"));
writeFileSync(join(staging, "illuminate-player-browser-adapter.mjs"),
  adapterBytes);
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
  packageId,
  directory: destination,
  wasmBytes: wasm.byteLength,
  wasmSha256: wasmHash,
  functionImports: functionImports.length,
  memoryImports: memoryImports.length,
  sourceDeclarations: declarations.length,
  publicFunctions: functionExports.length,
  internalFunctions: inventory.internalFunctions.length,
  residentHelpers: inventory.residentHelpers.length,
}));
