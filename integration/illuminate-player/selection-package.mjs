import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
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
  ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-selection-player-browser-adapter.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const illuminateRoot = realpathSync(process.env.ILLUMINATE_ROOT ??
  join(directory, ".illuminate"));
const buildDirectory = join(directory, "_build");
const baseStem = join(buildDirectory, "illuminate-selection-player-base.wasm");
const generatedStem = join(buildDirectory,
  "illuminate-selection-player-resident.wasm");
const expectedIlluminateSource = Object.freeze(JSON.parse(readFileSync(
  join(directory, "illuminate-source.json"), "utf8")));
const illuminateSourceFiles = [
  "src/Illuminate/Animation/Types.lean",
  "src/Illuminate/Animation/Player.lean",
  "src/Illuminate/Animation/FirLive.lean",
  "src/Illuminate/Animation/FirSelection.lean",
];
const expectedClosure = Object.freeze({
  finalLcnfDeclarations: 127,
  finalLcnfDeclarationSha256:
    "0ee1e73c21173216a80746bd2432944e42ca0d439f6ba178e3713b112c56b32b",
  retainedSourceFunctions: 82,
  retainedSourceFunctionSha256:
    "fdf43ab9f6c0bd8d85ea8bd951c25af8189aa13739cf419110f31d05c85dd471",
  residentHelpers: 167,
  residentHelperSha256:
    "f37cef4296f3fdcb4005c9a964ad98ac1c447f4e4c5481f211a125f8ad876532",
  baseWasmBytes: 20761,
  completeWasmBytes: 56156,
});
const outputNames = [
  "BUILD.json",
  "illuminate-selection-player-browser-adapter.mjs",
  "illuminate-selection-player.wasm",
  "illuminate-selection-player.wasm.json",
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

function assertExpectedIlluminateSource() {
  assert.equal(capture("git", ["-C", illuminateRoot, "rev-parse", "HEAD"]),
    expectedIlluminateSource.revision,
    "Illuminate source revision does not match illuminate-source.json");
  assert.equal(capture("git", ["-C", illuminateRoot, "status", "--porcelain"]),
    "", "Illuminate source checkout must be clean");
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
  const current = join(buildDirectory, "illuminate-selection-player-current");
  const temporary = join(buildDirectory,
    `.illuminate-selection-player-current-${process.pid}`);
  rmSync(temporary, { force: true });
  symlinkSync(relative(buildDirectory, targetDirectory), temporary);
  renameSync(temporary, current);
  assert.equal(lstatSync(current).isSymbolicLink(), true);
  assert.equal(realpathSync(current), realpathSync(targetDirectory));
}

assertExpectedIlluminateSource();
mkdirSync(buildDirectory, { recursive: true });
run("lake", [
  "--keep-toolchain",
  `-KilluminateRoot=${illuminateRoot}`,
  "build",
  "IlluminateFirNative.SelectionCompile",
]);
run("lake", [
  "--keep-toolchain",
  `-KilluminateRoot=${illuminateRoot}`,
  "env",
  "lean",
  "SelectionEmit.lean",
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
  "illuminate-selection-player-browser-adapter.mjs"));
const smokeBytes = readFileSync(join(directory, "selection-package-smoke.mjs"));
const fir = sourceState(firRoot);
const illuminate = sourceState(illuminateRoot, illuminateSourceFiles);
const leanToolchain = readFileSync(join(directory, "lean-toolchain"), "utf8")
  .trim();
const leanVersion = capture("lake", ["--keep-toolchain", "env", "lean",
  "--version"]);

assert.deepEqual(imports, []);
assert.deepEqual(descriptor.imports, []);
assert.deepEqual(memoryExports, ["memory"]);
assert.deepEqual(functionExports, [
  "Illuminate.AnimationPlayer.initialSelectionLive",
  "Illuminate.AnimationPlayer.transitionSelectionLive",
  "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact",
  "fir_heap_frontier",
  "fir_heap_set_frontier",
  "fir_heap_rewind",
  "fir_heap_alloc",
]);
assert.deepEqual(inventory.publicFunctions, functionExports);
assert.equal(inventory.functions.length,
  inventory.sourceFunctions.length + inventory.residentHelpers.length);
assert.equal(inventory.internalFunctions.length,
  inventory.functions.length - functionExports.length);
assert.equal(descriptor.sourceEntry,
  "Illuminate.AnimationPlayer.initialSelectionLive");
assert.deepEqual(descriptor.params, ["object"]);
assert.equal(descriptor.result, "object");
assert.deepEqual(inventory.publicSignatures.find((entry) =>
  entry.name === "Illuminate.AnimationPlayer.initialSelectionLive"), {
  name: "Illuminate.AnimationPlayer.initialSelectionLive",
  params: ["object"],
  results: ["object"],
});
assert.deepEqual(inventory.publicSignatures.find((entry) =>
  entry.name === "Illuminate.AnimationPlayer.transitionSelectionLive"), {
  name: "Illuminate.AnimationPlayer.transitionSelectionLive",
  params: ["object", "object", "tobject"],
  results: ["object"],
});
assert.deepEqual(inventory.publicSignatures.find((entry) =>
  entry.name ===
    "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact"), {
  name: "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact",
  params: ["object", "object", "uint64"],
  results: ["object"],
});
assert.equal(inventory.lazyCacheInitializers, 0);
assert.equal(inventory.residentGlobals, 1);
assert.equal(inventory.runtimeOperations, 0);
assert.equal(declarations.length, expectedClosure.finalLcnfDeclarations,
  "selection final-LCNF source declaration inventory changed");
assert.equal(sha256(JSON.stringify(declarations)),
  expectedClosure.finalLcnfDeclarationSha256,
  "selection final-LCNF declaration names changed");
assert.equal(inventory.sourceFunctions.length,
  expectedClosure.retainedSourceFunctions);
assert.equal(sha256(JSON.stringify(inventory.sourceFunctions)),
  expectedClosure.retainedSourceFunctionSha256,
  "selection retained source-function inventory changed");
assert.equal(inventory.residentHelpers.length, expectedClosure.residentHelpers);
assert.equal(sha256(JSON.stringify(inventory.residentHelpers)),
  expectedClosure.residentHelperSha256,
  "selection resident-helper inventory changed");
assert.equal(baseWasm.byteLength, expectedClosure.baseWasmBytes,
  "selection base Wasm size changed");
assert.equal(wasm.byteLength, expectedClosure.completeWasmBytes,
  "selection complete-runtime Wasm size changed");

const build = {
  schemaVersion: "fir.illuminate-selection-player.build/v1",
  sources: { fir, illuminate },
  toolchain: { leanToolchain, leanVersion },
  entries: [
    {
      sourceName: "Illuminate.AnimationPlayer.initialSelectionLive",
      exportName: "Illuminate.AnimationPlayer.initialSelectionLive",
      parameters: [{
        name: "animation",
        lean: "SelectionAnimation",
        fir: "object",
        physicalRepresentation:
          "single-field wrapper erased to its PlayerAnimation timeline",
      }],
      result: { lean: "Except String LiveSelectionTransition", fir: "object" },
    },
    {
      sourceName: "Illuminate.AnimationPlayer.transitionSelectionLive",
      exportName: "Illuminate.AnimationPlayer.transitionSelectionLive",
      parameters: [
        {
          name: "animation",
          lean: "SelectionAnimation",
          fir: "object",
          physicalRepresentation:
            "single-field wrapper erased to its PlayerAnimation timeline",
        },
        { name: "state", lean: "PlayerState", fir: "object" },
        { name: "event", lean: "PlayerEvent", fir: "tobject" },
      ],
      result: { lean: "LiveSelectionTransition", fir: "object" },
    },
    {
      sourceName: "IlluminateFirNative.transitionSelectionTickLive",
      exportName:
        "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact",
      parameters: [
        {
          name: "animation",
          lean: "SelectionAnimation",
          fir: "object",
          physicalRepresentation:
            "single-field wrapper erased to its PlayerAnimation timeline",
        },
        { name: "state", lean: "PlayerState", fir: "object" },
        {
          name: "timestampBits",
          lean: "Float",
          fir: "uint64",
          physicalRepresentation:
            "bit-exact binary64 payload reinterpreted to f64 inside Wasm",
        },
      ],
      result: { lean: "LiveSelectionTransition", fir: "object" },
    },
  ],
  wasm: {
    file: "illuminate-selection-player.wasm",
    byteLength: wasm.byteLength,
    sha256: wasmHash,
    base: { byteLength: baseWasm.byteLength, sha256: sha256(baseWasm) },
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
      apiVersion: ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
      methods: ["createPlayer", "dispatch", "dispatchTick", "disposePlayer",
        "replayTrace"],
      phases: ["project", "selectionEncode", "eventEncode", "execute",
        "decode", "rewind"],
      timing: {
        creation: ["instantiateMs", "projectMs", "selectionEncodeMs",
          "stateSlotMs", "executeMs", "decodeMs", "rewindMs", "totalMs"],
        dispatch: ["encodeMs", "executeMs", "decodeMs", "rewindMs", "totalMs"],
        dispatchTick:
          ["encodeMs", "executeMs", "decodeMs", "rewindMs", "totalMs"],
        intervals: "non-overlapping; totalMs is independently measured",
      },
      result:
        "copied FrameSelection exposed as action plus Lean scheduling decision; no updates array",
    },
    hotEvent: {
      version: ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION,
      method: "dispatchTick(player, timestamp)",
      semanticOracle: "dispatch(player, { kind: 'tick', timestamp })",
      sourceEntry: "IlluminateFirNative.transitionSelectionTickLive",
      wasmExport:
        "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact",
      transport: "IEEE-754 binary64 bits over a Wasm i64 parameter",
      eventConstruction: "PlayerEvent.tick is constructed inside Wasm",
      hostScratch: "zero bytes and zero resident allocation calls",
    },
    inputLayout: {
      version: ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
      leanType: "Illuminate.AnimationPlayer.SelectionAnimation",
      physicalType:
        "PlayerAnimation timeline (SelectionAnimation wrapper erased by Lean)",
      projection:
        "fps, totalFrames, segment bounds, and steps projected once per player",
      hostOwned: ["segment sync SVG", "parameter bindings", "frame parameter strings"],
      naturals:
        "validated once as uint32-safe JavaScript integers and retained as Lean Nat",
      floatBoundary: "IEEE-754 binary64, little-endian, bit-exact",
      events: ["advance", "pause", "seek", "playTo", "loopAt", "tick"],
    },
    ownership: {
      version: ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
      memoryOwner: "Wasm module",
      instance:
        "one Wasm instance per opaque player; one shared compiled WebAssembly.Module",
      selection:
        "one measured contiguous resident graph retained below the checkpoint",
      state:
        "fixed persistent Wasm slot below the checkpoint; never exposed to application JavaScript",
      scratch: "event and transition bytes are cleared and exactly rewound",
      roots:
        "lazy-cache globals disabled; allocator frontier is the only mutable heap root",
      output:
        "decoded JavaScript selection copy; no raw address or updates array escapes",
      hostMaterialization:
        "JavaScript indexes original animation pmap/params using Lean-selected segment/localFrame",
      failure:
        "execution/decoding/rewind failure poisons and drops the player instance",
      reclamation: "disposePlayer invalidates the handle and drops its Wasm instance",
      repeatedCalls: "every successful dispatch restores the persistent checkpoint",
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
    lazyCacheInitializerCount: inventory.lazyCacheInitializers,
    residentGlobalCount: inventory.residentGlobals,
    unresolvedRuntimeOperationCount: inventory.runtimeOperations,
    helperFamilies: [
      "object projections and scalar projections",
      "module-owned allocation and scalar stores",
      "bit-exact Float32 and Float packed-scalar stores",
      "constructors, setters, increments, releases, and cache setters",
      "small and big Nat operations",
      "Float subtraction, division, multiplication, comparison, round, and toUInt64",
      "Array allocation, size/usize, Nat/USize reads, update, replicate, and push",
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
const packages = join(buildDirectory, "illuminate-selection-player-packages");
const destination = join(packages, packageId);
const staging = join(packages, `.staging-${packageId}-${process.pid}`);
mkdirSync(packages, { recursive: true });
rmSync(staging, { recursive: true, force: true });
mkdirSync(staging);
copyFileSync(generatedStem,
  join(staging, "illuminate-selection-player.wasm"));
copyFileSync(`${generatedStem}.json`,
  join(staging, "illuminate-selection-player.wasm.json"));
writeFileSync(join(staging, "illuminate-selection-player-browser-adapter.mjs"),
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
  baseWasmBytes: baseWasm.byteLength,
  baseWasmSha256: sha256(baseWasm),
  functionImports: functionImports.length,
  memoryImports: memoryImports.length,
  sourceDeclarations: declarations.length,
  publicFunctions: functionExports.length,
  internalFunctions: inventory.internalFunctions.length,
  residentHelpers: inventory.residentHelpers.length,
}));
