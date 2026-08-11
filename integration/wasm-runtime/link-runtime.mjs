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
const allowedExports = new Set(expectedExports.map(({ name }) => name));

function run(tool, args) {
  execFileSync(join(binaryen, tool), args, { stdio: "inherit" });
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
  const mergedWat = join(temporary, "merged.wat");
  const privateWat = join(temporary, "private.wat");
  const privateWasm = join(temporary, "private.wasm");

  run("wasm-dis", [math, "-o", mathWat]);
  let wat = readFileSync(mathWat, "utf8");
  wat = replaceExactlyOnce(wat,
    /\(import "env" "memory" \(memory (\$[^ ]+) 1 [0-9]+\)\)/,
    '(import "env" "memory" (memory $1 1))',
    "Emscripten memory import normalization");
  writeFileSync(normalizedMathWat, wat);
  run("wasm-as", ["--enable-nontrapping-float-to-int", normalizedMathWat,
    "-o", normalizedMath]);

  run("wasm-merge", ["--enable-nontrapping-float-to-int",
    frontier, "env", normalizedMath, "lean.extern", "-o", merged]);
  const mergedModule = new WebAssembly.Module(readFileSync(merged));
  assert.deepEqual(WebAssembly.Module.imports(mergedModule), [],
    "merged application module must be import-free");

  run("wasm-dis", [merged, "-o", mergedWat]);
  wat = readFileSync(mergedWat, "utf8");
  let removed = 0;
  wat = wat.replace(/^ \(export "([^"]+)" .*\)\n/gm,
    (line, name) => {
      if (allowedExports.has(name)) return line;
      removed += 1;
      return "";
    });
  assert(removed > 0, "expected private linker exports to remove");
  writeFileSync(privateWat, wat);
  run("wasm-as", ["--enable-nontrapping-float-to-int", privateWat,
    "-o", privateWasm]);
  run("wasm-opt", ["--enable-nontrapping-float-to-int", "-O3",
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
    copyFileSync(mergedWat, join(debugDirectory, "merged.wat"));
    copyFileSync(privateWasm, join(debugDirectory, "private.wasm"));
    copyFileSync(privateWat, join(debugDirectory, "private.wat"));
  }
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
