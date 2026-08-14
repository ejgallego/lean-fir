import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import test from "node:test";

import {
  binaryenOptimizerName,
  definedFunctionOrdinal,
  injectFunctionIdentities,
  inspectFunction,
  makeCapture,
  makeSidecar,
  moduleShape,
  parseFunctionMap,
  restampCapture,
  validateSidecar,
} from "./function-index-lib.mjs";
import {
  boundedDisassembly,
  extractedFunctionWat,
  instructionSummary,
  makeFunctionView,
} from "./function-view-lib.mjs";

const binaryen = process.env.FIR_BINARYEN_DIR;
assert.equal(typeof binaryen, "string",
  "FIR_BINARYEN_DIR must name the pinned Binaryen bin directory");
const fixture = resolve(import.meta.dirname, "test/fixture.wat");
const importedFixture = resolve(import.meta.dirname,
  "test/imported-fixture.wat");
const functionTool = resolve(import.meta.dirname, "function-index.mjs");
const features = ["--all-features"];

function run(tool, args, options = {}) {
  return execFileSync(join(binaryen, tool), args, {
    encoding: options.encoding,
    stdio: options.stdio,
  });
}

test("captures final optimized indices without changing release bytes",
  () => {
    const directory = mkdtempSync(join(tmpdir(), "fir-function-index-"));
    try {
      const input = join(directory, "input.wasm");
      const named = join(directory, "named.wasm");
      const baselineStage = join(directory, "baseline-stage.wasm");
      const namedStage = join(directory, "named-stage.wasm");
      const mapCopy = join(directory, "map-copy.wasm");
      const restamped = join(directory, "restamped.wasm");
      const baseline = join(directory, "baseline.wasm");
      const release = join(directory, "release.wasm");
      const graphCopy = join(directory, "graph-copy.wasm");
      run("wasm-as", [...features, fixture, "-o", input]);
      const inputBytes = readFileSync(input);
      const inventory = {
        functions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
        sourceFunctions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
        residentHelpers: [],
      };
      const capture = makeCapture(inputBytes, inventory, "input.wasm");
      writeFileSync(named, injectFunctionIdentities(inputBytes,
        capture.identities));

      run("wasm-opt", [...features, "--reorder-functions", input,
        "-o", baselineStage]);
      run("wasm-opt", [...features, "--reorder-functions", "--debuginfo",
        named, "-o", namedStage]);
      const stageMap = run("wasm-opt", [...features,
        "--print-function-map", namedStage, "-o", mapCopy], {
        encoding: "utf8",
      });
      const stageBytes = readFileSync(namedStage);
      const stageCapture = restampCapture(stageBytes, capture, stageMap,
        "named-stage.wasm");
      writeFileSync(restamped, injectFunctionIdentities(stageBytes,
        stageCapture.identities));

      const optimization = [...features, "-O3", "--closed-world",
        "--remove-unused-module-elements", "--vacuum", "--strip-debug",
        "--strip-dwarf"];
      run("wasm-opt", [...optimization, baselineStage, "-o", baseline]);
      const functionMap = run("wasm-opt", [...optimization,
        "--print-function-map", restamped, "-o", release], {
        encoding: "utf8",
      });
      assert.deepEqual(readFileSync(release), readFileSync(baseline),
        "Binaryen-default numeric identities must not perturb release bytes");

      const callGraph = run("wasm-opt", [...features, "--print-call-graph",
        release, "-o", graphCopy], { encoding: "utf8" });
      assert.equal(moduleShape(readFileSync(graphCopy)).functionCount,
        moduleShape(readFileSync(release)).functionCount,
        "call-graph inspection must preserve function order and count");
      const sidecar = makeSidecar(readFileSync(release), stageCapture,
        functionMap, callGraph, { artifactFile: "release.wasm" });
      validateSidecar(readFileSync(release), sidecar);
      assert.equal(sidecar.functions.length, moduleShape(readFileSync(release))
        .functionCount);
      const entry = inspectFunction(sidecar, "fixture.entry");
      assert.equal(entry.name, "Fixture.entry");
      assert.deepEqual(entry.exportedAs, ["fixture.entry"]);
      assert.equal(sidecar.functions.some(({ name }) =>
        name === "Fixture.dead"), false, "dead function must not survive");
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  });

test("resolves imported functions across final maps and call graphs",
  () => {
    const directory = mkdtempSync(join(tmpdir(), "fir-function-imports-"));
    try {
      const input = join(directory, "input.wasm");
      const named = join(directory, "named.wasm");
      const baseline = join(directory, "baseline.wasm");
      const release = join(directory, "release.wasm");
      const graphCopy = join(directory, "graph-copy.wasm");
      const extracted = join(directory, "entry.wat");
      const sidecarPath = join(directory, "release.wasm.functions.json");
      const capturePath = join(directory, "capture.json");
      const optimizerArgsPath = join(directory, "optimizer-args.json");
      const commandRelease = join(directory, "command-release.wasm");
      const commandSidecarPath = join(directory,
        "command-release.wasm.functions.json");

      run("wasm-as", [...features, importedFixture, "-o", input]);
      const inputBytes = readFileSync(input);
      const capture = makeCapture(inputBytes, {
        functions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
        sourceFunctions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
      });
      writeFileSync(named, injectFunctionIdentities(inputBytes,
        capture.identities));

      const optimization = [...features, "-O3", "--closed-world",
        "--remove-unused-module-elements", "--vacuum",
        "--minify-imports-and-exports-and-modules", "--strip-debug",
        "--strip-dwarf"];
      writeFileSync(capturePath, `${JSON.stringify(capture, null, 2)}\n`);
      writeFileSync(optimizerArgsPath,
        `${JSON.stringify(optimization, null, 2)}\n`);
      run("wasm-opt", [...optimization, input, "-o", baseline]);
      const identityMapSource = run("wasm-opt", [...optimization,
        "--print-function-map", named, "-o", release], {
        encoding: "utf8",
      });
      assert(identityMapSource.includes("fixture.entry =>"),
        "fixture must exercise minifier rename diagnostics");
      assert.deepEqual(readFileSync(release), readFileSync(baseline),
        "import identity capture must not perturb release bytes");

      const callGraph = run("wasm-opt", [...features,
        "--print-function-map", "--print-call-graph", release,
        "-o", graphCopy], { encoding: "utf8" });
      const releaseBytes = readFileSync(release);
      const shape = moduleShape(releaseBytes);
      assert.deepEqual({
        imports: shape.functionImportCount,
        definitions: shape.definedFunctionCount,
        functions: shape.functionCount,
      }, { imports: 2, definitions: 1, functions: 3 });
      assert.deepEqual(parseFunctionMap(callGraph).map(({ index,
        optimizerName }) => [index, optimizerName]), [
        [0, "fimport$0"],
        [1, "fimport$1"],
        [2, "0"],
      ]);
      assert.equal(binaryenOptimizerName(2, 2), "0");
      assert.equal(definedFunctionOrdinal(2, 2), 0);
      assert.throws(() => definedFunctionOrdinal(1, 2), /imported/);

      const sidecar = makeSidecar(releaseBytes, capture,
        identityMapSource, callGraph, { artifactFile: "release.wasm" });
      writeFileSync(sidecarPath, `${JSON.stringify(sidecar, null, 2)}\n`);
      assert.deepEqual(sidecar.functions.map(({ index, name, optimizerName,
        imported, directCallees }) => ({ index, name, optimizerName,
        imported, directCallees })), [
        { index: 0, name: "host.sink", optimizerName: "fimport$0",
          imported: true, directCallees: [] },
        { index: 1, name: "host.identity", optimizerName: "fimport$1",
          imported: true, directCallees: [] },
        { index: 2, name: "Fixture.entry", optimizerName: "0",
          imported: false, directCallees: [0, 1] },
      ]);

      execFileSync(process.execPath, [functionTool, "optimize",
        "--binaryen-dir", binaryen, "--input", named,
        "--wasm", commandRelease, "--capture", capturePath,
        "--wasm-opt-args", optimizerArgsPath, "--output",
        commandSidecarPath], { encoding: "utf8" });
      assert.deepEqual(readFileSync(commandRelease), readFileSync(baseline),
        "optimize command must preserve imported-module release bytes");
      const commandSidecar = JSON.parse(readFileSync(commandSidecarPath,
        "utf8"));
      validateSidecar(readFileSync(commandRelease), commandSidecar);
      assert.deepEqual(commandSidecar.functions, sidecar.functions,
        "optimize command must use the same imported-function namespace");

      // Selection uses the absolute Wasm index. The extracted WAT body and
      // its direct targets use Binaryen's final optimizer-name namespace.
      run("wasm-opt", [...features, "--quiet", release,
        "--extract-function-index=2", "--emit-text", "-o", extracted]);
      const view = makeFunctionView(sidecar, "Fixture.entry",
        readFileSync(extracted, "utf8"), 40);
      assert.equal(view.function.index, 2);
      assert.equal(view.function.optimizerName, "0");
      assert.deepEqual(view.calls.targets, [
        { index: 0, name: "host.sink", origin: "function-import",
          family: null, callSites: 1 },
        { index: 1, name: "host.identity", origin: "function-import",
          family: null, callSites: 1 },
      ]);
      assert.throws(() => makeFunctionView(sidecar, "host.sink", "", 40),
        /imported and has no local body/);

      const releaseBeforeView = readFileSync(release);
      const commandView = JSON.parse(execFileSync(process.execPath, [
        functionTool, "view", "--binaryen-dir", binaryen,
        "--wasm", release, "--sidecar", sidecarPath,
        "--function", "Fixture.entry", "--max-lines", "40", "--json",
      ], { encoding: "utf8" }));
      assert.equal(commandView.function.index, 2,
        "view command must select by the absolute Wasm index");
      assert.deepEqual(commandView.calls.targets, view.calls.targets);
      assert.deepEqual(readFileSync(release), releaseBeforeView,
        "view command must not rewrite the release artifact");
      assert.throws(() => execFileSync(process.execPath, [
        functionTool, "view", "--binaryen-dir", binaryen,
        "--wasm", release, "--sidecar", sidecarPath,
        "--function", "host.sink", "--json",
      ], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }),
      (error) => error.stderr.includes("is imported and has no local body"));
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  });

test("extracts a bounded function-local instruction view",
  () => {
    const directory = mkdtempSync(join(tmpdir(), "fir-function-view-"));
    try {
      const wasm = join(directory, "fixture.wasm");
      const wat = join(directory, "function.wat");
      run("wasm-as", [...features, fixture, "-o", wasm]);
      const bytes = readFileSync(wasm);
      const capture = makeCapture(bytes, {
        functions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
        sourceFunctions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
      });
      const map = capture.identities.map(({ index, token }) =>
        `${index}:${token}`).join("\n");
      const sidecar = makeSidecar(bytes, capture, map,
        "digraph call {\n  \"1\" -> \"0\";\n}\n");
      run("wasm-opt", [...features, "--quiet", wasm,
        "--extract-function-index=1", "--emit-text", "-o", wat]);
      const source = readFileSync(wat, "utf8");
      const view = makeFunctionView(sidecar, "Fixture.entry", source, 12);
      assert.equal(view.artifact.sha256, sidecar.artifact.sha256);
      assert.deepEqual(view.function.directCallees, [{
        index: 0,
        name: "Fixture.leaf",
        origin: "lean-source",
        family: null,
      }]);
      assert.equal(Object.fromEntries(view.instructions.opcodes.map(({ name,
        count }) => [name, count])).call, 1);
      assert.equal(view.calls.directCount, 1);
      assert.deepEqual(view.calls.byFamily, [{
        name: "lean-source",
        count: 1,
      }]);
      assert.deepEqual(view.calls.targets, [{
        index: 0,
        name: "Fixture.leaf",
        origin: "lean-source",
        family: null,
        callSites: 1,
      }]);
      assert(view.instructions.classes.some(({ name, count }) =>
        name === "local-global" && count > 0));
      assert.equal(view.disassembly.lines.length,
        Math.min(view.disassembly.lineCount, 12));
      assert.equal(instructionSummary(extractedFunctionWat(source, "1"))
        .instructionCount,
        view.instructions.instructionCount);
      assert.equal(boundedDisassembly(source, 1000).omittedLines, 0);
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  });

test("rejects a sidecar after the artifact changes",
  () => {
    const directory = mkdtempSync(join(tmpdir(), "fir-function-index-hash-"));
    try {
      const wasm = join(directory, "fixture.wasm");
      run("wasm-as", [...features, fixture, "-o", wasm]);
      const bytes = readFileSync(wasm);
      const capture = makeCapture(bytes, {
        functions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
        sourceFunctions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
      });
      const map = capture.identities.map(({ index, token }) =>
        `${index}:${token}`).join("\n");
      const sidecar = makeSidecar(bytes, capture, map, "digraph call {}\n");
      const changed = Buffer.concat([bytes, Buffer.from([0, 1, 0])]);
      assert(WebAssembly.validate(changed));
      assert.throws(() => validateSidecar(changed, sidecar), /SHA-256/);
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  });
