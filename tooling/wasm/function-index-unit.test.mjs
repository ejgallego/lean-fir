import assert from "node:assert/strict";
import test from "node:test";

import {
  binaryenOptimizerName,
  definedFunctionOrdinal,
  inspectFunction,
  parseCallGraph,
  parseFunctionMap,
} from "./function-index-lib.mjs";

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
