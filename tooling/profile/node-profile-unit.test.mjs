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

test("classifies boxing separately and rejects malformed profiles", () => {
  assert.equal(residentHelperFamily("fir_float_box"), "resident/boxing");
  assert.equal(residentHelperFamily("fir_float_unbox"), "resident/boxing");
  assert.equal(residentHelperFamily("fir_heap_alloc"),
    "resident/allocation");
  assert.equal(residentHelperFamily("fir_ext_Array_getInternalBorrowed"),
    "resident/array");
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
