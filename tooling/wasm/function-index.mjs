#!/usr/bin/env node

import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync, rmSync, writeFileSync } from "node:fs";
import { basename, join, resolve } from "node:path";

import { makeToolingTemporaryDirectory } from "../worktree-temp.mjs";

import {
  binaryenOptimizerName,
  injectFunctionIdentities,
  inspectFunction,
  makeCapture,
  makeSidecar,
  moduleShape,
  parseFunctionMap,
  restampCapture,
  validateSidecar,
} from "./function-index-lib.mjs";
import { makeFunctionView } from "./function-view-lib.mjs";

function usage() {
  return `usage:
  function-index.mjs prepare --wasm FILE --inventory FILE --named-wasm FILE --capture FILE
  function-index.mjs restamp --binaryen-dir DIR --wasm FILE --capture FILE --wasm-opt-args FILE --named-wasm FILE --output FILE
  function-index.mjs optimize --binaryen-dir DIR --input FILE --wasm FILE --capture FILE --wasm-opt-args FILE --output FILE
  function-index.mjs finalize --wasm FILE --capture FILE --function-map FILE --call-graph FILE --output FILE
  function-index.mjs verify --wasm FILE --sidecar FILE
  function-index.mjs inspect --wasm FILE --sidecar FILE --function INDEX_OR_NAME [--json]
  function-index.mjs view --binaryen-dir DIR --wasm FILE --sidecar FILE --function INDEX_OR_NAME [--max-lines N] [--json]`;
}

function arguments_(items) {
  const result = new Map();
  for (let index = 0; index < items.length; index += 1) {
    const name = items[index];
    assert(name.startsWith("--"), `unexpected argument ${name}\n${usage()}`);
    if (name === "--json") {
      result.set(name, true);
      continue;
    }
    index += 1;
    assert(index < items.length, `missing value for ${name}\n${usage()}`);
    assert(!result.has(name), `duplicate argument ${name}`);
    result.set(name, items[index]);
  }
  return result;
}

function required(args, name) {
  const value = args.get(name);
  assert.equal(typeof value, "string", `missing ${name}\n${usage()}`);
  return resolve(value);
}

function readJson(path) {
  return JSON.parse(readFileSync(path, "utf8"));
}

function writeJson(path, value) {
  writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`);
}

function run(binaryenDirectory, tool, args, options = {}) {
  return execFileSync(join(binaryenDirectory, tool), args, {
    encoding: options.encoding,
    stdio: options.encoding === undefined ? "inherit" :
      ["ignore", "pipe", "pipe"],
  });
}

function optimizerArgs(args) {
  const result = readJson(required(args, "--wasm-opt-args"));
  assert(Array.isArray(result) && result.every((item) =>
    typeof item === "string"), "--wasm-opt-args must name a JSON string array");
  return result;
}

function featureArgs(items) {
  return items.filter((item) => item === "--all-features" ||
    item.startsWith("--enable-") ||
    item.startsWith("--disable-"));
}

function label(sidecar, index) {
  const function_ = sidecar.functions[index];
  return function_.name ?? function_.optimizerName ?? `wasm-function[${index}]`;
}

function textInspection(sidecar, function_) {
  const lines = [
    `${function_.index}: ${function_.name ?? function_.optimizerName}`,
    `  origin: ${function_.origin}`,
    `  compiler shape: ${function_.compilerShape}`,
    `  body bytes: ${function_.bodyBytes ?? "import"}`,
    `  exports: ${function_.exportedAs.join(", ") || "none"}`,
    `  direct callees: ${function_.directCallees.map((index) =>
      `${index}:${label(sidecar, index)}`).join(", ") || "none"}`,
    `  direct callers: ${function_.directCallers.map((index) =>
      `${index}:${label(sidecar, index)}`).join(", ") || "none"}`,
  ];
  if (function_.unresolvedCallTargets.length !== 0) {
    lines.push(`  unresolved call targets: ${function_.unresolvedCallTargets.join(", ")}`);
  }
  return `${lines.join("\n")}\n`;
}

function textFunctionView(view) {
  const lines = [
    `${view.function.index}: ${view.function.name ?? view.function.optimizerName}`,
    `  artifact: ${view.artifact.sha256}`,
    `  body bytes: ${view.function.bodyBytes}`,
    `  instructions: ${view.instructions.instructionCount}`,
    "  classes: " + view.instructions.classes.map(({ name, count }) =>
      `${name}=${count}`).join(", "),
    "  opcodes: " + view.instructions.opcodes.map(({ name, count }) =>
      `${name}=${count}`).join(", "),
    `  direct call sites: ${view.calls.directCount}`,
    "  call families: " + view.calls.byFamily.map(({ name, count }) =>
      `${name}=${count}`).join(", "),
    "  direct call targets:",
    ...view.calls.targets.map(({ index, name, family, origin, callSites }) =>
      `    ${index}: ${name ?? "unattributed"} x${callSites} ` +
      `[${family ?? origin}]`),
    `  disassembly: ${view.disassembly.lineCount} line(s), ` +
      `${view.disassembly.omittedLines} omitted`,
    ...view.disassembly.lines,
  ];
  return `${lines.join("\n")}\n`;
}

const [command, ...rest] = process.argv.slice(2);
assert(command !== undefined, usage());
const args = arguments_(rest);

if (command === "prepare") {
  const wasmPath = required(args, "--wasm");
  const inventoryPath = required(args, "--inventory");
  const namedPath = required(args, "--named-wasm");
  const capturePath = required(args, "--capture");
  const wasm = readFileSync(wasmPath);
  const capture = makeCapture(wasm, readJson(inventoryPath),
    basename(wasmPath));
  writeFileSync(namedPath, injectFunctionIdentities(wasm,
    capture.identities));
  writeJson(capturePath, capture);
} else if (command === "restamp") {
  const binaryenDirectory = required(args, "--binaryen-dir");
  const wasmPath = required(args, "--wasm");
  const wasm = readFileSync(wasmPath);
  const temporary = makeToolingTemporaryDirectory("fir-function-restamp-");
  let functionMap;
  try {
    functionMap = run(binaryenDirectory, "wasm-opt", [
      ...featureArgs(optimizerArgs(args)),
      "--print-function-map",
      wasmPath,
      "-o",
      join(temporary, "map-copy.wasm"),
    ], { encoding: "utf8" });
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
  const capture = restampCapture(wasm,
    readJson(required(args, "--capture")), functionMap, basename(wasmPath));
  writeFileSync(required(args, "--named-wasm"),
    injectFunctionIdentities(wasm, capture.identities));
  writeJson(required(args, "--output"), capture);
} else if (command === "optimize") {
  const binaryenDirectory = required(args, "--binaryen-dir");
  const inputPath = required(args, "--input");
  const wasmPath = required(args, "--wasm");
  const capture = readJson(required(args, "--capture"));
  const optimizationArgs = optimizerArgs(args);
  const functionMap = run(binaryenDirectory, "wasm-opt", [
    ...optimizationArgs,
    "--print-function-map",
    inputPath,
    "-o",
    wasmPath,
  ], { encoding: "utf8" });
  const temporary = makeToolingTemporaryDirectory("fir-function-graph-");
  let callGraph;
  try {
    const graphCopy = join(temporary, "graph-copy.wasm");
    callGraph = run(binaryenDirectory, "wasm-opt", [
      ...featureArgs(optimizationArgs),
      "--print-function-map",
      "--print-call-graph",
      wasmPath,
      "-o",
      graphCopy,
    ], { encoding: "utf8" });
    const graphFunctionMap = parseFunctionMap(callGraph);
    const shape = moduleShape(readFileSync(wasmPath));
    assert.equal(graphFunctionMap.length, shape.functionCount,
      "call-graph read did not preserve the final function count");
    assert.deepEqual(graphFunctionMap.map(({ index, optimizerName }) =>
      [index, optimizerName]), Array.from({ length: shape.functionCount },
      (_, index) => [index, binaryenOptimizerName(index,
        shape.functionImportCount)]),
    "stripped release function order changed during call-graph read");
    assert.equal(moduleShape(readFileSync(graphCopy)).functionCount,
      shape.functionCount,
      "call-graph read changed the discarded copy's function count");
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
  const sidecar = makeSidecar(readFileSync(wasmPath), capture, functionMap,
    callGraph, {
      artifactFile: basename(wasmPath),
      producer: {
        tool: "tooling/wasm/function-index.mjs optimize",
        binaryenVersion: run(binaryenDirectory, "wasm-opt", ["--version"],
          { encoding: "utf8" }).trim(),
        optimizerArgs: optimizationArgs,
      },
    });
  writeJson(required(args, "--output"), sidecar);
} else if (command === "finalize") {
  const wasmPath = required(args, "--wasm");
  const wasm = readFileSync(wasmPath);
  const sidecar = makeSidecar(wasm, readJson(required(args, "--capture")),
    readFileSync(required(args, "--function-map"), "utf8"),
    readFileSync(required(args, "--call-graph"), "utf8"), {
      artifactFile: basename(wasmPath),
      producer: { tool: "tooling/wasm/function-index.mjs" },
    });
  writeJson(required(args, "--output"), sidecar);
} else if (command === "verify") {
  validateSidecar(readFileSync(required(args, "--wasm")),
    readJson(required(args, "--sidecar")));
  process.stdout.write("function sidecar: OK\n");
} else if (command === "inspect") {
  const wasm = readFileSync(required(args, "--wasm"));
  const sidecar = readJson(required(args, "--sidecar"));
  validateSidecar(wasm, sidecar);
  const selector = args.get("--function");
  assert.equal(typeof selector, "string", `missing --function\n${usage()}`);
  const function_ = inspectFunction(sidecar, selector);
  process.stdout.write(args.get("--json") === true ?
    `${JSON.stringify(function_, null, 2)}\n` :
    textInspection(sidecar, function_));
} else if (command === "view") {
  const binaryenDirectory = required(args, "--binaryen-dir");
  const wasmPath = required(args, "--wasm");
  const wasm = readFileSync(wasmPath);
  const sidecar = readJson(required(args, "--sidecar"));
  validateSidecar(wasm, sidecar);
  const selector = args.get("--function");
  assert.equal(typeof selector, "string", `missing --function\n${usage()}`);
  const function_ = inspectFunction(sidecar, selector);
  assert.equal(function_.imported, false,
    `function ${function_.index} is imported and has no local body`);
  const maxLines = Number(args.get("--max-lines") ?? 160);
  assert(Number.isSafeInteger(maxLines) && maxLines >= 8,
    "--max-lines must be an integer of at least eight");
  const temporary = makeToolingTemporaryDirectory("fir-function-view-");
  let wat;
  try {
    const watPath = join(temporary, "function.wat");
    run(binaryenDirectory, "wasm-opt", [
      "--all-features",
      "--quiet",
      wasmPath,
      `--extract-function-index=${function_.index}`,
      "--emit-text",
      "-o",
      watPath,
    ], { encoding: "utf8" });
    wat = readFileSync(watPath, "utf8");
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
  const view = makeFunctionView(sidecar, selector, wat, maxLines);
  process.stdout.write(args.get("--json") === true ?
    `${JSON.stringify(view, null, 2)}\n` : textFunctionView(view));
} else {
  throw new Error(`unknown command ${command}\n${usage()}`);
}
