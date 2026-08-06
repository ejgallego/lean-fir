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
const generatedStem = join(buildDirectory, "illuminate-player-resident.wasm");
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

function sourceState(root) {
  return {
    commit: capture("git", ["-C", root, "rev-parse", "HEAD"]),
    dirty: capture("git", ["-C", root, "status", "--porcelain"]) !== "",
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
const descriptorBytes = readFileSync(`${generatedStem}.json`);
const descriptor = JSON.parse(descriptorBytes);
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
const illuminate = sourceState(illuminateRoot);
const leanToolchain = readFileSync(join(directory, "lean-toolchain"), "utf8")
  .trim();
const leanVersion = capture("lake", ["--keep-toolchain", "env", "lean",
  "--version"]);

assert.deepEqual(imports, []);
assert.deepEqual(descriptor.imports, []);
assert.equal(memoryExports.includes("memory"), true);
assert.equal(functionExports.includes(descriptor.entry), true);
assert.equal(declarations.length, 84,
  "Illuminate final-LCNF source declaration inventory changed");

const build = {
  schemaVersion: "fir.illuminate-player.build/v1",
  sources: { fir, illuminate },
  toolchain: { leanToolchain, leanVersion },
  entry: {
    sourceName: descriptor.sourceEntry,
    exportName: descriptor.entry,
    parameters: [
      { name: "animation", lean: "Illuminate.CompiledAnimation", fir: "object" },
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
      result: "normalized FrameAction objects",
    },
    inputLayout: {
      version: ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION,
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
    residentHelperCount: functionExports.length - 1,
    residentHelpers: functionExports.filter((name) => name !== descriptor.entry),
    helperFamilies: [
      "object projections and scalar projections",
      "module-owned allocation and scalar stores",
      "constructors, setters, increments, releases, and cache setters",
      "Nat and Int small/big numeric operations",
      "Float subtraction, division, multiplication, comparison, round, and toUInt64",
      "Array allocation, size, reads, and push",
      "Nat.mod",
      "Illuminate findSegment, parameterUpdates, option equality, and pause traversal",
      "resident UTF-8 string literals",
    ],
    illuminateSpecializations: functionExports.filter((name) =>
      name.startsWith("fir_illuminate_")),
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
  residentHelpers: functionExports.length - 1,
}));
