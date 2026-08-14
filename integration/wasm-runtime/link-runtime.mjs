import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync,
  writeFileSync } from "node:fs";
import { basename, dirname, join, resolve } from "node:path";
import { tmpdir } from "node:os";
import { fileURLToPath } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = resolve(directory, "../..");
const binaryen = join(firRoot,
  ".deps/lcnf-c-wasm/emsdk/upstream/bin");
const [frontierArg, mathArg, outputArg, ...optionalArgs] = process.argv.slice(2);
if (outputArg === undefined) {
  throw new Error("usage: node link-runtime.mjs FRONTIER EXTERNAL_RUNTIME OUTPUT " +
    "[--function-inventory INVENTORY --function-sidecar SIDECAR]");
}

function functionEvidenceOptions(args) {
  if (args.length === 0) return null;
  const values = new Map();
  for (let index = 0; index < args.length; index += 2) {
    const option = args[index];
    assert(option === "--function-inventory" || option === "--function-sidecar",
      `unknown runtime-link option ${option}`);
    assert(index + 1 < args.length, `${option} requires one value`);
    assert(!values.has(option), `duplicate runtime-link option ${option}`);
    values.set(option, resolve(args[index + 1]));
  }
  assert(values.has("--function-inventory") && values.has("--function-sidecar"),
    "function evidence requires both --function-inventory and --function-sidecar");
  return {
    inventory: values.get("--function-inventory"),
    sidecar: values.get("--function-sidecar"),
  };
}

const frontier = resolve(frontierArg);
const math = resolve(mathArg);
const output = resolve(outputArg);
const functionEvidence = functionEvidenceOptions(optionalArgs);
const temporary = mkdtempSync(join(tmpdir(), "fir-external-runtime-link-"));
const expectedExports = WebAssembly.Module.exports(new WebAssembly.Module(
  readFileSync(frontier)));
const expectedExportKinds = new Map(expectedExports.map(({ name, kind }) =>
  [name, kind]));
assert.equal(expectedExportKinds.size, expectedExports.length,
  "frontier export names must be unique");
const isExpectedExport = ({ name, kind }) =>
  expectedExportKinds.get(name) === kind;
const binaryenFeatures = [
  "--enable-nontrapping-float-to-int",
  "--enable-multivalue",
];
const finalOptimizerArgs = [
  ...binaryenFeatures,
  "-O3",
  "--closed-world",
  "--remove-unused-module-elements",
  "--vacuum",
  "--strip-debug",
  "--strip-dwarf",
];
const functionIndex = join(firRoot, "tooling/wasm/function-index.mjs");

function run(tool, args, { discardStdout = false } = {}) {
  execFileSync(join(binaryen, tool), args, {
    stdio: discardStdout ? ["ignore", "ignore", "inherit"] : "inherit",
  });
}

function runFunctionIndex(args) {
  execFileSync(process.execPath, [functionIndex, ...args], { stdio: "inherit" });
}

function replaceExactlyOnce(source, pattern, replacement, label) {
  const matches = source.match(new RegExp(pattern.source, pattern.flags +
    (pattern.flags.includes("g") ? "" : "g"))) ?? [];
  assert.equal(matches.length, 1, `${label}: expected one match`);
  return source.replace(pattern, replacement);
}

try {
  const mathWat = join(temporary, "math.wat");
  const normalizedMathWat = join(temporary, "math-unbounded.wat");
  const normalizedMath = join(temporary, "math-unbounded.wasm");
  const merged = join(temporary, "merged.wasm");
  const reachabilityGraph = join(temporary, "exports.json");
  const privateWasm = join(temporary, "private.wasm");

  run("wasm-dis", [math, "-o", mathWat]);
  let wat = readFileSync(mathWat, "utf8");
  wat = replaceExactlyOnce(wat,
    /\(import "env" "memory" \(memory (\$[^ ]+) 1 [0-9]+\)\)/,
    '(import "env" "memory" (memory $1 1))',
    "Emscripten memory import normalization");
  writeFileSync(normalizedMathWat, wat);
  run("wasm-as", [...binaryenFeatures, normalizedMathWat,
    "-o", normalizedMath]);

  run("wasm-merge", [...binaryenFeatures,
    frontier, "env", normalizedMath, "lean.extern", "-o", merged]);
  const mergedModule = new WebAssembly.Module(readFileSync(merged));
  assert.deepEqual(WebAssembly.Module.imports(mergedModule), [],
    "merged application module must be import-free");
  const mergedExports = WebAssembly.Module.exports(mergedModule);
  assert(mergedExports.some((export_) => !isExpectedExport(export_)),
    "expected private linker exports to remove");
  writeFileSync(reachabilityGraph, JSON.stringify(mergedExports.map(
    (export_, index) => ({
      name: `link$export$${index}`,
      export: export_.name,
      ...(isExpectedExport(export_) ? { root: true } : {}),
    }))));
  run("wasm-metadce", [...binaryenFeatures, merged,
    "--quiet", `--graph-file=${reachabilityGraph}`, "-o", privateWasm],
  { discardStdout: true });
  assert.deepEqual(WebAssembly.Module.exports(new WebAssembly.Module(
    readFileSync(privateWasm))), expectedExports,
  "meta-DCE must preserve exactly the frontier exports");
  run("wasm-opt", [...finalOptimizerArgs, privateWasm, "-o", output]);

  const finalModule = new WebAssembly.Module(readFileSync(output));
  assert.deepEqual(WebAssembly.Module.imports(finalModule), [],
    "final application module must be import-free");
  assert.deepEqual(WebAssembly.Module.exports(finalModule), expectedExports,
    "external-runtime linking must preserve exactly the frontier exports");

  if (functionEvidence !== null) {
    const optimizerArgs = join(temporary, "wasm-opt-args.json");
    const frontierNamed = join(temporary, "frontier-named.wasm");
    const frontierCapture = join(temporary, "frontier.capture.json");
    const mergedEvidence = join(temporary, "merged-evidence.wasm");
    const mergedNamed = join(temporary, "merged-evidence-named.wasm");
    const mergedCapture = join(temporary, "merged.capture.json");
    const privateEvidence = join(temporary, "private-evidence.wasm");
    const privateNamed = join(temporary, "private-evidence-named.wasm");
    const privateCapture = join(temporary, "private.capture.json");
    const evidenceDirectory = join(temporary, "evidence-release");
    const evidenceOutput = join(evidenceDirectory, basename(output));
    const evidenceSidecar = join(temporary, "release.functions.json");
    mkdirSync(evidenceDirectory);
    writeFileSync(optimizerArgs, `${JSON.stringify(finalOptimizerArgs)}\n`);

    runFunctionIndex(["prepare", "--wasm", frontier,
      "--inventory", functionEvidence.inventory,
      "--named-wasm", frontierNamed, "--capture", frontierCapture]);
    run("wasm-merge", [...binaryenFeatures, "--debuginfo",
      frontierNamed, "env", normalizedMath, "lean.extern",
      "-o", mergedEvidence]);
    runFunctionIndex(["restamp", "--binaryen-dir", binaryen,
      "--wasm", mergedEvidence, "--capture", frontierCapture,
      "--wasm-opt-args", optimizerArgs,
      "--named-wasm", mergedNamed, "--output", mergedCapture]);
    assert.deepEqual(WebAssembly.Module.imports(new WebAssembly.Module(
      readFileSync(mergedNamed))), [],
    "evidence-enabled merged application module must be import-free");

    run("wasm-metadce", [...binaryenFeatures, "--debuginfo", mergedNamed,
      "--quiet", `--graph-file=${reachabilityGraph}`, "-o", privateEvidence],
    { discardStdout: true });
    assert.deepEqual(WebAssembly.Module.exports(new WebAssembly.Module(
      readFileSync(privateEvidence))), expectedExports,
    "evidence-enabled meta-DCE must preserve exactly the frontier exports");
    runFunctionIndex(["restamp", "--binaryen-dir", binaryen,
      "--wasm", privateEvidence, "--capture", mergedCapture,
      "--wasm-opt-args", optimizerArgs,
      "--named-wasm", privateNamed, "--output", privateCapture]);
    runFunctionIndex(["optimize", "--binaryen-dir", binaryen,
      "--input", privateNamed, "--wasm", evidenceOutput,
      "--capture", privateCapture, "--wasm-opt-args", optimizerArgs,
      "--output", evidenceSidecar]);
    assert.deepEqual(readFileSync(evidenceOutput), readFileSync(output),
      "function evidence changed stripped runtime-linked release bytes");
    runFunctionIndex(["verify", "--wasm", output,
      "--sidecar", evidenceSidecar]);
    copyFileSync(evidenceSidecar, functionEvidence.sidecar);
  }
  if (process.env.FIR_WASM_RUNTIME_LINK_DEBUG_DIR !== undefined) {
    const debugDirectory = resolve(process.env.FIR_WASM_RUNTIME_LINK_DEBUG_DIR);
    mkdirSync(debugDirectory, { recursive: true });
    copyFileSync(merged, join(debugDirectory, "merged.wasm"));
    copyFileSync(privateWasm, join(debugDirectory, "private.wasm"));
    copyFileSync(reachabilityGraph,
      join(debugDirectory, "exports.json"));
  }
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
