import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync,
  writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { tmpdir } from "node:os";
import { fileURLToPath } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = resolve(directory, "../..");
const binaryen = join(firRoot,
  ".deps/lcnf-c-wasm/emsdk/upstream/bin");
const [frontierArg, mathArg, outputArg] = process.argv.slice(2);
if (outputArg === undefined) {
  throw new Error("usage: node link-runtime.mjs FRONTIER EXTERNAL_RUNTIME OUTPUT");
}
const frontier = resolve(frontierArg);
const math = resolve(mathArg);
const output = resolve(outputArg);
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

function run(tool, args, { discardStdout = false } = {}) {
  execFileSync(join(binaryen, tool), args, {
    stdio: discardStdout ? ["ignore", "ignore", "inherit"] : "inherit",
  });
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
  run("wasm-opt", [...binaryenFeatures, "-O3",
    "--closed-world", "--remove-unused-module-elements", "--vacuum",
    "--strip-debug", "--strip-dwarf", privateWasm, "-o", output]);

  const finalModule = new WebAssembly.Module(readFileSync(output));
  assert.deepEqual(WebAssembly.Module.imports(finalModule), [],
    "final application module must be import-free");
  assert.deepEqual(WebAssembly.Module.exports(finalModule), expectedExports,
    "external-runtime linking must preserve exactly the frontier exports");
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
