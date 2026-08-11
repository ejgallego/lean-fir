import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import {
  createIlluminatePlayerAdapter,
  ILLUMINATE_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-player-browser-adapter.mjs";

const bytes = await readFile("_build/illuminate-player-complete.wasm");
const manifest = JSON.parse(await readFile(
  "_build/illuminate-player-complete.wasm.json", "utf8"));
const build = {
  capabilities: {
    completeRuntime: { externalRuntime: manifest.externalRuntime },
    browserAdapter: { apiVersion: ILLUMINATE_PLAYER_ADAPTER_API_VERSION },
    inputLayout: { version: ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION },
    ownership: { version: ILLUMINATE_PLAYER_OWNERSHIP_VERSION },
  },
};

const animation = {
  fps: 10,
  totalFrames: 6,
  segments: [{
    sf: 0,
    fc: 3,
    sync: "<svg>λ</svg>",
    pmap: [{ e: 0, a: "textContent" }, { e: 1, a: "fill" }],
    params: [["α", "red"], ["β", "blue"], ["γ", "green"]],
  }, {
    sf: 3,
    fc: 3,
    sync: "<svg>δ</svg>",
    pmap: [{ e: 7, a: "opacity" }],
    params: [["0.25"], ["0.5"], ["1"]],
  }],
  steps: [
    { frame: 0, pause: false, loop: false },
    { frame: 2, pause: false, loop: true },
    { frame: 4, pause: false, loop: false },
  ],
};

const adapter = await createIlluminatePlayerAdapter({ bytes, manifest, build });
const created = adapter.createPlayer(animation);
assert.equal(created.ok, true);
assert.equal(JSON.stringify(created.player), "{}");
assert.equal(created.action.updates[0].a, "textContent");
assert.deepEqual(created.action.updates[1],
  { e: 1, a: "fill", v: "red" });
assert.equal(created.scheduleNextFrame, false);
assert.equal(created.memory.postRewindFrontier,
  created.memory.persistentCheckpoint);
assert.equal(created.memory.animationBytes,
  created.memory.frontierAfterAnimation - created.memory.frontierBefore);
assert.ok(created.memory.animationObjectCount > 1);
assert.equal(created.memory.animationAllocationCalls, 1);
assert.equal(created.memory.stateSlotBytes,
  created.memory.persistentCheckpoint - created.memory.frontierAfterAnimation);
assert.equal(created.memory.stateSlotObjectCount,
  created.memory.stateSlotAllocationCalls);
assert.equal(created.memory.persistentObjectCount,
  created.memory.animationObjectCount + created.memory.stateSlotObjectCount);
assert.equal(created.memory.persistentAllocationCalls,
  created.memory.animationAllocationCalls +
    created.memory.stateSlotAllocationCalls);

const events = [
  { kind: "pause" },
  { kind: "playTo", frame: 3, loopAfter: true },
  { kind: "tick", timestamp: 0.125 },
  { kind: "loopAt", frame: 3 },
  { kind: "advance" },
  { kind: "seek", frame: 5 },
];
for (const event of events) {
  const dispatched = adapter.dispatch(created.player, event);
  assert.equal(dispatched.ok, true, dispatched.error);
  assert.equal(dispatched.memory.frontierBefore,
    created.memory.persistentCheckpoint);
  assert.equal(dispatched.memory.postRewindFrontier,
    created.memory.persistentCheckpoint);
}

const malformed = adapter.dispatch(created.player, { kind: "unknown" });
assert.equal(malformed.ok, false);
assert.equal(malformed.memory.postRewindFrontier,
  created.memory.persistentCheckpoint);
assert.equal(adapter.dispatch(created.player, { kind: "seek", frame: 1 }).ok,
  true, "an encode-only failure must not poison the player");

let pending = () => adapter.dispatch(created.player,
  { kind: "tick", timestamp: 12.5 });
adapter.disposePlayer(created.player);
adapter.disposePlayer(created.player);
assert.throws(() => pending(), /player is disposed/);
pending = undefined;

const trace = adapter.replayTrace(animation, events);
assert.equal(trace.ok, true);
assert.equal(trace.actions.length, events.length + 1);
assert.equal(trace.memory.postRewindFrontier,
  trace.memory.persistentCheckpoint);

const unreadSync = { ...animation.segments[0] };
Object.defineProperty(unreadSync, "sync", {
  enumerable: true,
  get() { throw new Error("sync SVG must remain browser-owned"); },
});
assert.equal(adapter.createPlayer({
  ...animation,
  segments: [unreadSync, animation.segments[1]],
}).ok, true);

assert.deepEqual(adapter.createPlayer({ ...animation, totalFrames: 0 })
  .error, "animation must contain at least one frame");
assert.equal(adapter.createPlayer({ ...animation, fps: 1.5 }).ok, false);

const first = adapter.createPlayer(animation);
const second = adapter.createPlayer(animation);
assert.equal(first.ok && second.ok, true);
assert.equal(adapter.dispatch(first.player, { kind: "seek", frame: 5 })
  .action.frame, 5);
assert.equal(adapter.dispatch(second.player, { kind: "seek", frame: 1 })
  .action.frame, 1);
adapter.disposePlayer(first.player);
adapter.disposePlayer(second.player);

for (let index = 0; index < 32; ++index) {
  const cycle = adapter.createPlayer(animation);
  assert.equal(cycle.ok, true);
  assert.equal(cycle.memory.frontierBefore,
    manifest.externalRuntime.reservedMemoryBytes);
  adapter.disposePlayer(cycle.player);
}

const steadyAnimation = {
  fps: 60,
  totalFrames: 2,
  segments: [{ sf: 0, fc: 2, pmap: [], params: [[], []] }],
  steps: [{ frame: 0, pause: false, loop: false }],
};
const steady = adapter.createPlayer(steadyAnimation);
assert.equal(steady.ok, true);
assert.equal(adapter.dispatch(steady.player, { kind: "advance" }).ok, true);
let steadyPeak = steady.memory.persistentCheckpoint;
for (let index = 0; index < 10_000; ++index) {
  const tick = adapter.dispatch(steady.player,
    { kind: "tick", timestamp: index / 7 });
  assert.equal(tick.ok, true, tick.error);
  assert.equal(tick.memory.postRewindFrontier,
    steady.memory.persistentCheckpoint);
  steadyPeak = Math.max(steadyPeak, tick.memory.peakFrontier);
}
assert.equal(steadyPeak - steady.memory.persistentCheckpoint, 704);
adapter.disposePlayer(steady.player);

const decodeFailureAdapter = await createIlluminatePlayerAdapter({
  bytes,
  manifest,
  build,
  maximumNodes: 1,
});
const decodeFailureAnimation = {
  fps: 10,
  totalFrames: 2,
  segments: [
    { sf: 0, fc: 1, pmap: [], params: [[]] },
    {
      sf: 1,
      fc: 1,
      pmap: [{ e: 0, a: "textContent" }, { e: 1, a: "fill" }],
      params: [["copied", "blue"]],
    },
  ],
  steps: [{ frame: 0, pause: false, loop: false }],
};
const decodeFailure = decodeFailureAdapter.createPlayer(decodeFailureAnimation);
assert.equal(decodeFailure.ok, true);
const poisoned = decodeFailureAdapter.dispatch(decodeFailure.player,
  { kind: "seek", frame: 1 });
assert.equal(poisoned.ok, false);
assert.equal(poisoned.memory.postRewindFrontier,
  decodeFailure.memory.persistentCheckpoint);
assert.throws(() => decodeFailureAdapter.dispatch(decodeFailure.player,
  { kind: "advance" }), /player is poisoned/);

let clock = 0;
const timedAdapter = await createIlluminatePlayerAdapter({
  bytes,
  manifest,
  build,
  now: () => clock++,
});
const timed = timedAdapter.createPlayer(steadyAnimation);
assert.equal(timed.ok, true);
for (const phase of ["instantiateMs", "projectMs", "animationEncodeMs",
  "stateSlotMs", "executeMs", "decodeMs", "rewindMs"]) {
  assert.equal(timed.timings[phase], 1);
}
assert.ok(timed.timings.totalMs >= 7);
assert.equal(timed.timings.overheadMs,
  timed.timings.totalMs - 7);
const timedDispatch = timedAdapter.dispatch(timed.player,
  { kind: "tick", timestamp: 0.125 });
for (const phase of ["encodeMs", "executeMs", "decodeMs", "rewindMs"]) {
  assert.equal(timedDispatch.timings[phase], 1);
}
assert.equal(timedDispatch.timings.overheadMs,
  timedDispatch.timings.totalMs - 4);
timedAdapter.disposePlayer(timed.player);

assert.deepEqual(WebAssembly.Module.imports(new WebAssembly.Module(bytes)), []);
assert.deepEqual(WebAssembly.Module.exports(new WebAssembly.Module(bytes)), [
  { name: "Illuminate.AnimationPlayer.initialLive", kind: "function" },
  { name: "Illuminate.AnimationPlayer.transitionLive", kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);

console.log(JSON.stringify({
  ok: true,
  liveEvents: events.length,
  steadyTicks: 10_000,
  steadyCheckpoint: steady.memory.persistentCheckpoint,
  steadyPeak,
  animationObjects: created.memory.animationObjectCount,
  animationAllocationCalls: created.memory.animationAllocationCalls,
  functionImports: 0,
  memoryImports: 0,
}));
