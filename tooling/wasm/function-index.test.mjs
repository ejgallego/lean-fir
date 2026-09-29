import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import test from "node:test";

import { makeToolingTemporaryDirectory } from "../worktree-temp.mjs";

import {
  assertSameNonCustomSections,
  binaryenOptimizerName,
  definedFunctionOrdinal,
  injectFunctionIdentities,
  inspectFunction,
  makeCapture,
  makeLinkCapture,
  makeNamedCompanion,
  makeSidecar,
  moduleShape,
  parseFunctionMap,
  restampCapture,
  sha256,
  validateSidecar,
  verifyNamedCompanion,
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

test("tracks all inputs through imported merge/metadce/O3 without changing bytes", () => {
  const directory = makeToolingTemporaryDirectory("fir-function-link-");
  const p = name => join(directory, name);
  const read = name => readFileSync(p(name));
  const json = (name, value) => writeFileSync(p(name), JSON.stringify(value));
  const command = args => execFileSync(process.execPath, [functionTool, ...args],
    { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] });
  try {
    const flags = ["--enable-nontrapping-float-to-int", "--enable-multivalue"];
    const opt = [...flags, "-O3", "--closed-world", "--remove-unused-module-elements",
      "--vacuum", "--strip-debug", "--strip-dwarf"];
    for (const name of ["app", "provider"]) run("wasm-as", [...flags,
      resolve(import.meta.dirname, `test/link-${name}.wat`), "-o", p(`${name}.wasm`)]);
    json("app.json", { functions: ["Fixture.entry", "Fixture.dead"],
      sourceFunctions: ["Fixture.entry", "Fixture.dead"] });
    json("provider.json", { functions: ["Provider.adjust"], residentHelpers: ["Provider.adjust"] });
    const inputs = ["app", "provider"].map(name => ({ wasm: `${name}.wasm`,
      inventory: `${name}.json`, namedWasm: `${name}.named.wasm`,
      wasmSha256: sha256(read(`${name}.wasm`)), inventorySha256: sha256(read(`${name}.json`)) }));
    json("inputs.json", inputs);
    json("opt.json", opt);
    command(["prepare-link", "--inputs", p("inputs.json"), "--capture", p("capture.json")]);
    const capture = JSON.parse(read("capture.json"));
    for (const name of ["app", "provider"])
      assertSameNonCustomSections(read(`${name}.wasm`), read(`${name}.named.wasm`));
    assert.equal(new Set(capture.identities.map(i => i.token)).size, 6);
    assert.equal(capture.inputArtifacts.length, 2);
    // Duplicate local indices are safe only inside separately tokenized inputs.
    const duplicated = makeLinkCapture([0, 1].map(() => ({ bytes: read("provider.wasm"),
      inventoryBytes: read("provider.json"), file: "provider.wasm",
      wasmSha256: inputs[1].wasmSha256, inventorySha256: inputs[1].inventorySha256 })));
    assert.equal(new Set(duplicated.capture.identities.map(i => i.token)).size, 4);
    json("bad-inputs.json", [{ ...inputs[0], namedWasm: "app.wasm" }]);
    assert.throws(() => command(["prepare-link", "--inputs", p("bad-inputs.json"),
      "--capture", p("bad.json")]), error => error.stderr.includes("overwrite inputs"));
    for (const key of ["wasmSha256", "inventorySha256"]) {
      json("bad-inputs.json", [{ ...inputs[0], [key]: "0".repeat(64) }]);
      assert.throws(() => command(["prepare-link", "--inputs", p("bad-inputs.json"),
        "--capture", p("bad.json")]), error => error.stderr.includes("SHA-256 mismatch"));
    }
    for (const mode of ["plain", "named"]) run("wasm-merge", [...flags,
      ...(mode === "named" ? ["--debuginfo"] : []),
      p(mode === "named" ? "app.named.wasm" : "app.wasm"), "app",
      p(mode === "named" ? "provider.named.wasm" : "provider.wasm"), "runtime",
      "-o", p(`${mode}.merged.wasm`)]);
    assertSameNonCustomSections(read("plain.merged.wasm"), read("named.merged.wasm"));
    const exports = WebAssembly.Module.exports(new WebAssembly.Module(read("plain.merged.wasm")));
    json("graph.json", exports.map((e, i) => ({ name: `export$${i}`, export: e.name,
      ...(e.name === "fixture.entry" ? { root: true } : {}) })));
    const restamp = (input, capture, named, output) => command(["restamp",
      "--binaryen-dir", binaryen, "--wasm", p(input), "--capture", p(capture),
      "--wasm-opt-args", p("opt.json"), "--named-wasm", p(named), "--output", p(output)]);
    restamp("named.merged.wasm", "capture.json", "merged.restamped.wasm", "merged.capture.json");
    assertSameNonCustomSections(read("named.merged.wasm"), read("merged.restamped.wasm"));
    const mergedCapture = JSON.parse(read("merged.capture.json"));
    assert(mergedCapture.identities.some(i => i.name === "Provider.adjust"));
    assert(mergedCapture.identities.some(i => i.name === "host.scale"));
    for (const mode of ["plain", "named"]) run("wasm-metadce", [...flags,
      ...(mode === "named" ? ["--debuginfo"] : []),
      p(mode === "named" ? "merged.restamped.wasm" : "plain.merged.wasm"),
      "--quiet", `--graph-file=${p("graph.json")}`, "-o", p(`${mode}.private.wasm`)]);
    assertSameNonCustomSections(read("plain.private.wasm"), read("named.private.wasm"));
    restamp("named.private.wasm", "merged.capture.json", "private.restamped.wasm", "private.capture.json");
    assertSameNonCustomSections(read("named.private.wasm"), read("private.restamped.wasm"));
    run("wasm-opt", [...opt, p("plain.private.wasm"), "-o", p("baseline.wasm")]);
    command(["optimize", "--binaryen-dir", binaryen, "--input", p("private.restamped.wasm"),
      "--capture", p("private.capture.json"), "--wasm-opt-args", p("opt.json"),
      "--wasm", p("release.wasm"), "--output", p("release.functions.json")]);
    assert.deepEqual(read("release.wasm"), read("baseline.wasm"),
      "multi-input name transport must not change release bytes");
    const sidecar = JSON.parse(read("release.functions.json"));
    assert.equal(sidecar.capture.inputArtifacts.length, 2);
    assert.equal(sidecar.capture.inputArtifacts[1].inventorySha256, inputs[1].inventorySha256);
    assert.equal(sidecar.functions[2].inputSource.module, 1);
    assert.equal(sidecar.functions[2].inputSource.index, 1);
    assert.equal(sidecar.functions[2].inputSource.sha256, capture.inputArtifacts[1].sha256);
    assert.deepEqual(sidecar.functions.map(f => [f.index, f.name, f.imported]), [
      [0, "host.scale", true], [1, "host.sink", true],
      [2, "Provider.adjust", false], [3, "Fixture.entry", false],
    ]);
    assert.equal(sidecar.functions.some(f => f.name === "Fixture.dead"), false);
    assert.deepEqual(sidecar.functions[0].finalImport, {module: "host", name: "scale"});
    const wrongImport = structuredClone(sidecar);
    wrongImport.functions[0].finalImport.name = "notScale";
    assert.throws(() => validateSidecar(read("release.wasm"), wrongImport,
      {strictNames: true}), /final import identity/);
    const instance = new WebAssembly.Instance(new WebAssembly.Module(read("release.wasm")),
      { host: { sink: n => n + 7, scale: n => n * 3 } });
    for (let n = 0; n <= 12; n++) assert.equal(instance.exports["fixture.entry"](n), 10 + 3*n*(n+1)/2);
    command(["companion", "--wasm", p("release.wasm"), "--sidecar", p("release.functions.json"),
      "--named-wasm", p("release.named.wasm")]);
    command(["verify-companion", "--wasm", p("release.wasm"), "--sidecar", p("release.functions.json"),
      "--named-wasm", p("release.named.wasm"), "--output", p("verification.json")]);
    const verification = JSON.parse(read("verification.json"));
    assert.equal(verification.nonCustomSectionsEqual, true);
    assert.equal(verification.functions.length, 4);
    assert.equal(verification.verifier.length, 2);
    command(["verify", "--wasm", p("release.wasm"), "--sidecar", p("release.functions.json"),
      "--strict-names"]);
    const withoutCapture = makeSidecar(read("release.wasm"),
      {...capture, identities: []}, sidecar.functions.map(f =>
        `${f.index}:${f.optimizerName}`).join("\n"), "digraph call {}\n");
    assert.deepEqual(withoutCapture.functions.slice(0, 2).map(f => [f.name, f.origin]),
      [["host.scale", "function-import"], ["host.sink", "function-import"]]);
    const differentExport = Buffer.from(read("release.named.wasm"));
    const exportOffset = differentExport.indexOf(Buffer.from("fixture.entry"));
    assert(exportOffset >= 0);
    differentExport[exportOffset] = "z".charCodeAt(0);
    assert(WebAssembly.validate(differentExport));
    assert.throws(() => verifyNamedCompanion(read("release.wasm"), differentExport, sidecar),
      /changed non-custom sections/);
    // Unknown origin is NOT proof of synthesis: ordinary sidecars allow it,
    // but strict acceptance and companion production must reject it.
    const unknown = structuredClone(sidecar);
    unknown.functions[2].name = null;
    unknown.functions[2].origin = "optimizer-or-linked-runtime";
    validateSidecar(read("release.wasm"), unknown);
    assert.throws(() => makeNamedCompanion(read("release.wasm"), unknown), /no proven final name/);
    json("unknown.json", unknown);
    assert.throws(() => command(["verify", "--wasm", p("release.wasm"),
      "--sidecar", p("unknown.json"), "--strict-names"]),
      error => error.stderr.includes("no proven final name"));
    const duplicateName = structuredClone(sidecar);
    duplicateName.functions[2].name = duplicateName.functions[3].name;
    assert.throws(() => makeNamedCompanion(read("release.wasm"), duplicateName), /ambiguous final name/);
    const wrong = injectFunctionIdentities(read("release.wasm"),
      sidecar.functions.map(f => ({index:f.index, token:`wrong${f.index}`})));
    assert.throws(() => verifyNamedCompanion(read("release.wasm"), wrong, sidecar),
      /must name every exact final index/);
    assert.throws(() => verifyNamedCompanion(read("release.wasm"), read("release.wasm"), sidecar),
      /exactly one name section/);
    const changed = structuredClone(sidecar); changed.artifact.sha256 = "0".repeat(64);
    assert.throws(() => makeNamedCompanion(read("release.wasm"), changed), /SHA-256/);
    const missing = structuredClone(sidecar); missing.functions.pop();
    assert.throws(() => makeNamedCompanion(read("release.wasm"), missing), /every final Wasm function/);
    const collision = structuredClone(capture); collision.identities[1].token = collision.identities[0].token;
    assert.throws(() => restampCapture(read("named.merged.wasm"), collision,
      mergedCapture.identities.map(i => `${i.index}:${i.upstreamOptimizerName}`).join("\n")),
      /unique across all link inputs/);
    const misassociated = structuredClone(capture);
    misassociated.identities[0].token += "$different-input";
    assert.throws(() => restampCapture(read("named.merged.wasm"), misassociated,
      mergedCapture.identities.map(i => `${i.index}:${i.upstreamOptimizerName}`).join("\n")),
      /does not belong to the supplied input capture/);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

function run(tool, args, options = {}) {
  return execFileSync(join(binaryen, tool), args, {
    encoding: options.encoding,
    stdio: options.stdio,
  });
}

test("captures final optimized indices without changing release bytes",
  () => {
    const directory = makeToolingTemporaryDirectory("fir-function-index-");
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

test("captures an exact emitter-final module without rewriting it", () => {
  const directory = makeToolingTemporaryDirectory("fir-function-direct-");
  try {
    const wasm = join(directory, "fixture.wasm");
    const inventoryPath = join(directory, "fixture.inventory.json");
    const sidecarPath = join(directory, "fixture.wasm.functions.json");
    run("wasm-as", [...features, fixture, "-o", wasm]);
    const inventory = {
      functions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
      sourceFunctions: ["Fixture.leaf", "Fixture.entry", "Fixture.dead"],
      residentHelpers: [],
    };
    writeFileSync(inventoryPath, `${JSON.stringify(inventory, null, 2)}\n`);
    const before = readFileSync(wasm);
    execFileSync(process.execPath, [functionTool, "direct",
      "--binaryen-dir", binaryen, "--wasm", wasm,
      "--inventory", inventoryPath, "--output", sidecarPath],
    { encoding: "utf8" });
    assert.deepEqual(readFileSync(wasm), before,
      "direct capture must not rewrite final emitter bytes");
    const sidecar = JSON.parse(readFileSync(sidecarPath, "utf8"));
    validateSidecar(before, sidecar);
    assert.equal(sidecar.capture.producer.identityBoundary,
      "exact-emitter-final-order/v1");
    assert.deepEqual(inspectFunction(sidecar, "Fixture.entry").directCallees,
      [0]);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

test("resolves imported functions across final maps and call graphs",
  () => {
    const directory = makeToolingTemporaryDirectory("fir-function-imports-");
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
    const directory = makeToolingTemporaryDirectory("fir-function-view-");
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
    const directory = makeToolingTemporaryDirectory(
      "fir-function-index-hash-");
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
