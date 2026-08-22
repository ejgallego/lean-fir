import assert from "node:assert/strict";

import {
  loadEmscriptenIlluminateSelectionPlayerAdapter,
} from "./illuminate-selection-player-emscripten-adapter.mjs";

const adapter = await loadEmscriptenIlluminateSelectionPlayerAdapter(
  new URL("./illuminate-selection-player.manifest.json", import.meta.url),
);

const animation = {
  fps: 10,
  totalFrames: 6,
  segments: [
    { sf: 0, fc: 2, sync: "not transferred", pmap: [], params: [] },
    { sf: 2, fc: 4, sync: "not transferred", pmap: [], params: [] },
  ],
  steps: [
    { frame: 0, pause: false, loop: false },
    { frame: 2, pause: false, loop: true },
    { frame: 4, pause: false, loop: false },
  ],
};

function requireOk(result, label, diagnostics = true) {
  assert.equal(result.ok, true, `${label}: ${result.error ?? "unknown error"}`);
  if (!diagnostics) return result;
  for (const phase of ["encodeMs", "executeMs", "decodeMs", "totalMs"]) {
    assert.ok(Number.isFinite(result.timings?.[phase]) && result.timings[phase] >= 0, `${label} ${phase}`);
  }
  assert.ok(result.memory.currentBytes >= 0, `${label} current memory`);
  assert.ok(result.memory.peakBytes >= result.memory.currentBytes, `${label} peak memory`);
  return result;
}

function adjacentFloat(value, direction) {
  const storage = new ArrayBuffer(8);
  const view = new DataView(storage);
  view.setFloat64(0, value, true);
  view.setBigUint64(0, view.getBigUint64(0, true) + BigInt(direction), true);
  return view.getFloat64(0, true);
}

const created = requireOk(adapter.createPlayer(animation), "create");
assert.ok(created.timings.projectMs >= 0);
const events = [
  { kind: "advance" },
  { kind: "pause" },
  { kind: "seek", frame: 3 },
  { kind: "playTo", frame: 1, loopAfter: false },
  { kind: "loopAt", frame: 2 },
  { kind: "tick", timestamp: adjacentFloat(50, -1) },
];
for (const event of events) requireOk(adapter.dispatch(created.player, event), event.kind);

const generic = requireOk(adapter.createPlayer(animation), "generic create");
const scalar = requireOk(adapter.createPlayer(animation), "scalar create");
requireOk(adapter.dispatch(generic.player, { kind: "advance" }), "generic advance");
requireOk(adapter.dispatch(scalar.player, { kind: "advance" }), "scalar advance");
const exactTimestamp = adjacentFloat(50, 1);
const genericTick = requireOk(
  adapter.dispatch(generic.player, { kind: "tick", timestamp: exactTimestamp }),
  "generic tick",
);
const scalarTick = requireOk(adapter.dispatchTick(scalar.player, exactTimestamp), "scalar tick");
assert.deepEqual(scalarTick.action, genericTick.action, "scalar tick changed binary64 semantics");

const left = requireOk(adapter.createPlayer(animation), "left create");
const right = requireOk(adapter.createPlayer(animation), "right create");
requireOk(adapter.dispatch(left.player, { kind: "seek", frame: 3 }), "left seek");
assert.equal(requireOk(adapter.dispatch(right.player, { kind: "pause" }), "right pause").action.frame, 0);

const replay = requireOk(adapter.replayTrace(animation, events), "replay", false);
assert.equal(replay.actions.length, events.length + 1);
assert.equal(adapter.createPlayer({ ...animation, fps: 0 }).ok, false, "invalid animation passed");

adapter.disposePlayer(left.player);
adapter.disposePlayer(left.player);
adapter.disposePlayer(right.player);
adapter.disposePlayer(generic.player);
adapter.disposePlayer(scalar.player);
adapter.disposePlayer(created.player);

let longRun = requireOk(adapter.createPlayer(animation), "long-run create");
requireOk(adapter.dispatch(longRun.player, { kind: "advance" }), "long-run advance");
let warmBytes = 0;
for (let index = 0; index < 10_000; index += 1) {
  const result = requireOk(adapter.dispatchTick(longRun.player, index * 16.25), `tick ${index}`);
  if (index === 999) warmBytes = result.memory.currentBytes;
  if (index >= 999) assert.equal(result.memory.currentBytes, warmBytes, "linear memory grew after warmup");
}
adapter.disposePlayer(longRun.player);

let cycleBytes = 0;
for (let index = 0; index < 100; index += 1) {
  const result = requireOk(adapter.createPlayer(animation), `cycle ${index}`);
  if (index === 9) cycleBytes = result.memory.currentBytes;
  if (index >= 9) assert.equal(result.memory.currentBytes, cycleBytes, "create/dispose retained memory");
  adapter.disposePlayer(result.player);
}

console.log("LLVM/Emscripten Illuminate selection-player smoke passed");
