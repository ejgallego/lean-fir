import assert from "node:assert/strict";
import test from "node:test";

import {
  residentHelperFamily,
  summarizeCpuProfile,
} from "./node-profile-lib.mjs";

function frame(id, functionName, url = "wasm://fixture") {
  return { id, callFrame: { functionName, url } };
}

test("groups cropped self samples by retained identity and helper family",
  () => {
    const sidecar = {
      functions: [
        { name: "Example.run", origin: "lean-source",
          compilerShape: "ordinary" },
        { name: "fir_heap_alloc", origin: "resident-helper",
          compilerShape: "ordinary" },
        { name: "fir_dec_once", origin: "resident-helper",
          compilerShape: "ordinary" },
      ],
    };
    const profile = {
      startTime: 0,
      endTime: 100,
      nodes: [
        frame(1, "wasm-function[0]"),
        frame(2, "wasm-function[1]"),
        frame(3, "wasm-function[2]"),
        frame(4, "dispatch", "file:///driver.mjs"),
      ],
      samples: [1, 2, 2, 3, 4],
      timeDeltas: [10, 20, 20, 20, 30],
    };
    const summary = summarizeCpuProfile(profile, sidecar);
    assert.equal(summary.totalSampleMicros, 100);
    assert.deepEqual(Object.fromEntries(summary.groups.map(({ name,
      selfMicros }) => [name, selfMicros])), {
      "resident/allocation": 40,
      "host-or-runtime/unattributed": 30,
      "resident/reference-counting": 20,
      "lean-source/function": 10,
    });
    const cropped = summarizeCpuProfile(profile, sidecar, {
      startMicros: 30,
      durationMicros: 40,
    });
    assert.equal(cropped.totalSampleMicros, 40);
    assert.deepEqual(cropped.groups, [
      { name: "resident/allocation", selfMicros: 20 },
      { name: "resident/reference-counting", selfMicros: 20 },
    ]);
  });

test("keeps unresolved Wasm and host frames explicit", () => {
  const profile = {
    startTime: 0,
    endTime: 30,
    nodes: [
      frame(1, "wasm-function[8]"),
      frame(2, "dispatch", "file:///driver.mjs"),
    ],
    samples: [1, 2],
  };
  const summary = summarizeCpuProfile(profile, { functions: [] }, {
    startMicros: 5,
    durationMicros: 20,
  });
  assert.equal(summary.window.rawProfileMicros, 30);
  assert.equal(summary.totalSampleMicros, 20);
  assert.equal(summary.unresolvedWasmMicros, 10);
  assert.equal(summary.hostMicros, 10);
  assert.deepEqual(summary.groups, [
    { name: "host-or-runtime/unattributed", selfMicros: 10 },
    { name: "wasm/unattributed", selfMicros: 10 },
  ]);
});

test("attributes Wasm self samples to immediate recursive, Wasm, and host callers",
  () => {
    const sidecar = {
      functions: [
        { name: "Example.run", origin: "lean-source",
          compilerShape: "ordinary" },
        { name: "fir_dec_once", origin: "resident-helper",
          compilerShape: "ordinary" },
        { name: "fir_alloc_ctor_10", origin: "resident-helper",
          compilerShape: "ordinary" },
      ],
    };
    const withChildren = (node, children) => ({ ...node, children });
    const profile = {
      startTime: 0,
      endTime: 60,
      nodes: [
        withChildren(frame(1, "(root)", ""), [2, 5, 9]),
        withChildren(frame(2, "wasm-function[0]"), [3, 4]),
        withChildren(frame(3, "wasm-function[1]"), [8]),
        withChildren(frame(4, "wasm-function[2]"), [6]),
        withChildren(frame(5, "callback", "file:///driver.mjs"), [7]),
        frame(6, "wasm-function[1]"),
        frame(7, "wasm-function[1]"),
        frame(8, "wasm-function[1]"),
        frame(9, "wasm-function[1]"),
      ],
      samples: [3, 8, 4, 6, 7, 9],
      timeDeltas: [10, 10, 10, 10, 10, 10],
    };
    const summary = summarizeCpuProfile(profile, sidecar, {
      strictFunctionIndices: true,
    });
    assert.equal(summary.callerAttribution.attributedWasmSelfSamples, 6);
    const releaseCallers = summary.callerEdges.filter(({ targetIndex }) =>
      targetIndex === 1);
    assert.deepEqual(releaseCallers.map(({ caller, selfSamples }) => ({
      kind: caller.kind,
      index: caller.index,
      name: caller.name,
      selfSamples,
    })), [
      { kind: "host-or-runtime", index: null, name: "callback",
        selfSamples: 1 },
      { kind: "root", index: null, name: null, selfSamples: 1 },
      { kind: "wasm", index: 0, name: "Example.run", selfSamples: 1 },
      { kind: "wasm", index: 1, name: "fir_dec_once", selfSamples: 1 },
      { kind: "wasm", index: 2, name: "fir_alloc_ctor_10", selfSamples: 1 },
    ]);
    const constructor = summary.callerEdges.find(({ targetIndex }) =>
      targetIndex === 2);
    assert.equal(constructor.caller.index, 0);
    assert.equal(constructor.caller.name, "Example.run");
  });

test("rejects malformed CPU profile parent graphs", () => {
  const sidecar = { functions: [] };
  const base = {
    startTime: 0,
    endTime: 1,
    samples: [1],
    timeDeltas: [1],
  };
  assert.throws(() => summarizeCpuProfile({
    ...base,
    nodes: [frame(1, "host"), frame(1, "host-again")],
  }, sidecar), /duplicate node ids/);
  assert.throws(() => summarizeCpuProfile({
    ...base,
    nodes: [{ ...frame(1, "host"), children: [2] }],
  }, sidecar), /missing child 2/);
  assert.throws(() => summarizeCpuProfile({
    ...base,
    nodes: [
      { ...frame(1, "host"), children: [3] },
      { ...frame(2, "host"), children: [3] },
      frame(3, "host"),
    ],
  }, sidecar), /multiple parents/);
  assert.throws(() => summarizeCpuProfile({
    ...base,
    nodes: [
      { ...frame(1, "host"), children: [2] },
      { ...frame(2, "host"), children: [1] },
    ],
  }, sidecar), /parent graph contains a cycle/);
});

test("classifies boxing separately and rejects malformed profiles", () => {
  assert.equal(residentHelperFamily("fir_float_box"), "resident/boxing");
  assert.equal(residentHelperFamily("fir_float_unbox"), "resident/boxing");
  assert.equal(residentHelperFamily("fir_heap_alloc"),
    "resident/allocation");
  assert.equal(residentHelperFamily("fir_ext_Array_getInternalBorrowed"),
    "resident/array");
  assert.equal(residentHelperFamily("fir_ext_USize_ofNat"),
    "resident/numeric");
  assert.equal(residentHelperFamily("Illuminate._fir_bit_exact"),
    "resident/other");
  const valid = {
    startTime: 0,
    endTime: 1,
    nodes: [frame(1, "dispatch", "file:///driver.mjs")],
    samples: [1],
    timeDeltas: [1],
  };
  assert.throws(() => summarizeCpuProfile({ ...valid, samples: [] },
    { functions: [] }), /contains no samples/);
  assert.throws(() => summarizeCpuProfile({ ...valid, samples: [2] },
    { functions: [] }), /missing node 2/);
  assert.throws(() => summarizeCpuProfile({ ...valid, timeDeltas: [-1] },
    { functions: [] }), /invalid sample delta/);
  assert.throws(() => summarizeCpuProfile(valid, { functions: [] }, {
    startMicros: -1,
  }), /nonnegative finite offset/);
});
