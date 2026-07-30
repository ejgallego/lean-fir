import assert from "node:assert/strict";

import {
  assessTiming,
  buildSchedule,
  distribution,
  expectedAggregate,
  median,
  summarizePhase,
} from "./benchmark-report.mjs";
import { inspectSingleImportedMemory } from "./wasm-memory.mjs";

assert.equal(median([9, 1, 5]), 5);
assert.equal(median([9, 1, 5, 3]), 4);
assert.deepEqual(distribution([1, 3, 5]), {
  count: 3,
  min: 1,
  median: 3,
  max: 5,
  mean: 3,
  medianAbsoluteDeviation: 2,
});
assert.deepEqual(buildSchedule(4), [
  { pass: 0, sequence: "native-emscripten", position: 0, profile: "native" },
  {
    pass: 0,
    sequence: "native-emscripten",
    position: 1,
    profile: "emscripten",
  },
  {
    pass: 1,
    sequence: "emscripten-native",
    position: 0,
    profile: "emscripten",
  },
  { pass: 1, sequence: "emscripten-native", position: 1, profile: "native" },
  { pass: 2, sequence: "native-emscripten", position: 0, profile: "native" },
  {
    pass: 2,
    sequence: "native-emscripten",
    position: 1,
    profile: "emscripten",
  },
  {
    pass: 3,
    sequence: "emscripten-native",
    position: 0,
    profile: "emscripten",
  },
  { pass: 3, sequence: "emscripten-native", position: 1, profile: "native" },
]);
assert.throws(() => buildSchedule(3), /even integer/);
assert.equal(
  expectedAggregate(0xffffffffffffffffn, 3).toString(),
  "0",
);

const rows = buildSchedule(4).map((scheduled) => {
  const emscripten = scheduled.profile === "emscripten";
  return {
    ...scheduled,
    phase: "steady",
    processElapsedNs: String(emscripten ? 400 : 200),
    child: {
      subjectElapsedNs: String(emscripten ? 300 : 100),
      runtime: {
        maxRssBytes: emscripten ? 2000 : 1000,
        processThreadCount: emscripten ? 8 : 1,
        declaredMemory: emscripten ? { initialByteLength: 65536 } : null,
      },
    },
  };
});
const summary = summarizePhase(rows, "steady", 1000);
assert.equal(summary.comparison.subjectMedianRatio, 3);
assert.equal(summary.comparison.processMedianRatio, 2);
assert.equal(summary.comparison.pairedSubjectRatios.median, 3);
assert.equal(summary.native.logicalElementsPerSecond.median, 10_000_000_000);
assert.equal(summary.emscripten.processThreadCount.median, 8);
assert.deepEqual(assessTiming({ steady: summary }), {
  status: "baseline",
  thresholds: {
    maximumRelativeMedianAbsoluteDeviationPercent: 10,
    maximumAbsoluteOrderEffectPercent: 10,
  },
  warnings: [],
});
const noisySummary = structuredClone(summary);
noisySummary.comparison.orderEffect.emscripten.secondVsFirstPercent = 12.5;
const noisyAssessment = assessTiming({ steady: noisySummary });
assert.equal(noisyAssessment.status, "inconclusive");
assert.match(noisyAssessment.warnings[0], /12.50% second-vs-first/);

const minimalSharedMemoryImport = Uint8Array.from([
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x02, 0x09,
  0x01,
  0x01, 0x61,
  0x01, 0x62,
  0x02,
  0x03, 0x02, 0x0a,
]);
assert.deepEqual(inspectSingleImportedMemory(minimalSharedMemoryImport), {
  module: "a",
  name: "b",
  shared: true,
  memory64: false,
  initialPages: "2",
  maximumPages: "10",
  initialByteLength: 131072,
  maximumByteLength: 655360,
});
assert.throws(
  () =>
    inspectSingleImportedMemory(
      Uint8Array.from([
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
        0x02, 0x08,
        0x01,
        0x01, 0x61,
        0x01, 0x62,
        0x02,
        0x02, 0x02,
      ]),
    ),
  /shared memory has no declared maximum/,
);
assert.throws(
  () => inspectSingleImportedMemory(Uint8Array.from([0, 1, 2, 3])),
  /invalid Wasm header|unexpected end/,
);

console.log("PASS LCNF C/Wasm benchmark report unit checks");
