import assert from "node:assert/strict";
import test from "node:test";

import {
  binaryenOptimizerName,
  definedFunctionOrdinal,
  inspectFunction,
  parseCallGraph,
  parseFunctionMap,
} from "./function-index-lib.mjs";
import {
  boundedDisassembly,
  extractedFunctionWat,
  instructionSummary,
  makeFunctionView,
} from "./function-view-lib.mjs";
import { residentHelperFamily } from "../runtime-classification.mjs";

test("distinguishes absolute indices from Binaryen definition ordinals", () => {
  assert.equal(binaryenOptimizerName(0, 2), "fimport$0");
  assert.equal(binaryenOptimizerName(1, 2), "fimport$1");
  assert.equal(binaryenOptimizerName(2, 2), "0");
  assert.equal(binaryenOptimizerName(17, 2), "15");
  assert.equal(definedFunctionOrdinal(2, 2), 0);
  assert.equal(definedFunctionOrdinal(17, 2), 15);
  assert.throws(() => binaryenOptimizerName(-1, 2), /invalid absolute/);
  assert.throws(() => binaryenOptimizerName(0, -1), /invalid function import/);
  assert.throws(() => definedFunctionOrdinal(1, 2), /imported/);
});

test("parses complete function maps beside Binaryen diagnostics", () => {
  const source = [
    "fixture.entry => a",
    "2:0",
    "0:fimport$0",
    "1:fimport$1",
    "module => b",
  ].join("\n");
  assert.deepEqual(parseFunctionMap(source), [
    { index: 0, optimizerName: "fimport$0" },
    { index: 1, optimizerName: "fimport$1" },
    { index: 2, optimizerName: "0" },
  ]);
  assert.throws(() => parseFunctionMap("0:a\n2:c\n"), /every final index/);
  assert.throws(() => parseFunctionMap("0:a\n1:a\n"), /must be unique/);
  assert.throws(() => parseFunctionMap("0:\n"), /empty Binaryen/);
});

test("resolves call graphs through final optimizer names", () => {
  const functionMap = [
    { index: 0, optimizerName: "fimport$0" },
    { index: 1, optimizerName: "fimport$1" },
    { index: 2, optimizerName: "0" },
  ];
  const source = [
    "0:fimport$0",
    "1:fimport$1",
    "2:0",
    "digraph call {",
    "  \"0\" -> \"fimport$1\";",
    "  \"0\" -> \"fimport$0\";",
    "  \"0\" -> \"fimport$1\";",
    "  \"0\" -> \"linked.helper\";",
    "  \"unknown\" -> \"0\";",
    "}",
  ].join("\n");
  assert.deepEqual(parseCallGraph(source, functionMap), {
    calls: [[], [], [0, 1]],
    unresolved: [[], [], ["linked.helper"]],
  });
});

test("selects functions without confusing names, exports, and indices", () => {
  const sidecar = {
    functions: [
      { index: 0, name: "host.sink", optimizerName: "fimport$0",
        exportedAs: [], directCallees: [] },
      { index: 1, name: "Example.leaf", optimizerName: "0",
        exportedAs: [], directCallees: [] },
      { index: 2, name: "Example.entry", optimizerName: "1",
        exportedAs: ["entry"], directCallees: [0, 1] },
    ],
  };
  assert.equal(inspectFunction(sidecar, "2").name, "Example.entry");
  assert.equal(inspectFunction(sidecar, "Example.entry").index, 2);
  assert.equal(inspectFunction(sidecar, "entry").index, 2);
  assert.deepEqual(inspectFunction(sidecar, "Example.leaf").directCallers,
    [2]);
  assert.throws(() => inspectFunction(sidecar, "missing"), /not found/);
  const ambiguous = structuredClone(sidecar);
  ambiguous.functions[1].name = "duplicate";
  ambiguous.functions[2].name = "duplicate";
  assert.throws(() => inspectFunction(ambiguous, "duplicate"), /ambiguous/);
});

test("classifies resident helper families without merging boxing into allocation",
  () => {
    assert.equal(residentHelperFamily("fir_float_box"), "resident/boxing");
    assert.equal(residentHelperFamily("fir_unbox_uint64"), "resident/boxing");
    assert.equal(residentHelperFamily("fir_heap_alloc"),
      "resident/allocation");
    assert.equal(residentHelperFamily("fir_dec_once"),
      "resident/reference-counting");
    assert.equal(residentHelperFamily("fir_ext_Array_getInternalBorrowed"),
      "resident/array");
    assert.equal(residentHelperFamily("fir_string_utf8_size"),
      "resident/string");
    assert.equal(residentHelperFamily("fir_big_Nat_add"),
      "resident/numeric");
    assert.equal(residentHelperFamily("fir_proj_ctor"),
      "resident/projection-update");
  });

test("builds a bounded import-aware view from one function body", () => {
  const wat = `(module
  (import "host" "sink" (func $fimport$0 (param i32)))
  ;; (func $0 (call $ignored))
  (func $0 (param i32) (result i32)
    (drop (i32.const 0))
    (drop (i32.const 1))
    (drop (i32.const 2))
    (drop (i32.const 3))
    (drop (i32.const 4))
    (drop (i32.const 5))
    (drop (i32.const 6))
    (call $fimport$0 (i32.const 1))
    (return (i32.const 2)))
  (func $1 (result i32)
    (i32.const 3)))`;
  const sidecar = {
    artifact: { sha256: "0".repeat(64) },
    functions: [
      { index: 0, name: "host.sink", optimizerName: "fimport$0",
        origin: "function-import", compilerShape: "ordinary", imported: true,
        bodyBytes: null, exportedAs: [], directCallees: [],
        unresolvedCallTargets: [] },
      { index: 1, name: "Example.entry", optimizerName: "0",
        origin: "lean-source", compilerShape: "ordinary", imported: false,
        bodyBytes: 17, exportedAs: ["entry"], directCallees: [0],
        unresolvedCallTargets: [] },
      { index: 2, name: "Example.other", optimizerName: "1",
        origin: "lean-source", compilerShape: "ordinary", imported: false,
        bodyBytes: 4, exportedAs: [], directCallees: [],
        unresolvedCallTargets: [] },
    ],
  };
  const functionWat = extractedFunctionWat(wat, "0");
  assert(functionWat.includes("call $fimport$0"));
  assert(!functionWat.includes("func $1"));
  const view = makeFunctionView(sidecar, "Example.entry", wat, 8);
  assert.equal(view.schemaVersion, "fir.wasm.function-view/v1");
  assert.equal(view.function.index, 1);
  assert.equal(view.calls.directCount, 1);
  assert.deepEqual(view.calls.targets, [{
    index: 0,
    name: "host.sink",
    origin: "function-import",
    family: null,
    callSites: 1,
  }]);
  assert.equal(Object.fromEntries(view.instructions.opcodes.map(({ name,
    count }) => [name, count])).call, 1);
  assert.equal(view.disassembly.lines.length, 8);
  assert(view.disassembly.omittedLines > 0);
  assert.throws(() => makeFunctionView(sidecar, "host.sink", wat, 8),
    /imported and has no local body/);
  assert.equal(boundedDisassembly(functionWat, 100).omittedLines, 0);
  assert.throws(() => boundedDisassembly(functionWat, 7), /at least eight/);
});

test("rejects malformed or inconsistent function-local WAT", () => {
  assert.throws(() => extractedFunctionWat("(module (func $0)", "0"),
    /unbalanced WAT opening/);
  assert.throws(() => extractedFunctionWat("(module \"unterminated)", "0"),
    /unterminated WAT string/);
  assert.throws(() => extractedFunctionWat("(module (; comment)", "0"),
    /unterminated WAT block comment/);
  assert.throws(() => extractedFunctionWat("(module (func $1))", "0"),
    /does not define/);
  const summary = instructionSummary(
    "(func $0 ;; (call $ignored)\n (i32.const 1))");
  assert.equal(summary.instructionCount, 1);
  assert.equal(summary.opcodes[0].name, "i32.const");
});
