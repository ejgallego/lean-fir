#!/usr/bin/env node

import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = resolve(directory, "../..");
const wasmOpt = join(firRoot,
  ".deps/lcnf-c-wasm/emsdk/upstream/bin/wasm-opt");
const [inputArg, outputArg, ...extraArgs] = process.argv.slice(2);

if (inputArg === undefined || outputArg === undefined || extraArgs.length !== 0) {
  throw new Error(
    "usage: optimize-closed-module.mjs INPUT.wasm OUTPUT.wasm");
}

const input = resolve(inputArg);
const output = resolve(outputArg);
assert.notEqual(input, output, "closed-module optimizer requires distinct paths");

const before = new WebAssembly.Module(readFileSync(input));
const expectedExports = WebAssembly.Module.exports(before);
assert.deepEqual(WebAssembly.Module.imports(before), [],
  "closed-module optimizer input must have zero imports");

execFileSync(wasmOpt, [
  "--enable-nontrapping-float-to-int",
  "--enable-multivalue",
  "-O3",
  "--closed-world",
  "--remove-unused-module-elements",
  "--vacuum",
  "--strip-debug",
  "--strip-dwarf",
  input,
  "-o",
  output,
], { stdio: "inherit" });

const after = new WebAssembly.Module(readFileSync(output));
assert.deepEqual(WebAssembly.Module.imports(after), [],
  "optimized closed module must have zero imports");
assert.deepEqual(WebAssembly.Module.exports(after), expectedExports,
  "closed-module optimization must preserve the exact export surface");
