import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import { createIlluminatePlayerAdapter } from
  "./illuminate-player-browser-adapter.mjs";

const here = new URL("./", import.meta.url);
const bytes = await readFile(new URL("illuminate-player.wasm", here));
const manifest = JSON.parse(await readFile(
  new URL("illuminate-player.wasm.json", here), "utf8"));
const build = JSON.parse(await readFile(new URL("BUILD.json", here), "utf8"));
assert.equal(build.schemaVersion, "fir.illuminate-player.build/v2");
assert.deepEqual(build.capabilities.completeRuntime.residentRuntime,
  manifest.residentRuntime);
assert.equal(manifest.residentRuntime.provider, "none");
assert.deepEqual(manifest.residentRuntime.externalDeclarations, []);
assert.deepEqual(manifest.residentRuntime.sourceCompiledDeclarations,
  ["Float.ofNat", "Float.ofScientific"]);
await assert.rejects(createIlluminatePlayerAdapter({
  bytes,
  manifest: {
    ...manifest,
    residentRuntime: {
      ...manifest.residentRuntime,
      heapBase: manifest.residentRuntime.heapBase - 8,
    },
  },
  build,
}), /resident-runtime heap bases disagree/);
const adapter = await createIlluminatePlayerAdapter({ bytes, manifest, build });

const animation = {
  fps: 10,
  totalFrames: 6,
  segments: [{
    sf: 0,
    fc: 3,
    pmap: [{ e: 0, a: "textContent" }, { e: 1, a: "fill" }],
    params: [["α", "red"], ["β", "blue"], ["γ", "green"]],
  }, {
    sf: 3,
    fc: 3,
    pmap: [{ e: 7, a: "opacity" }],
    params: [["0.25"], ["0.5"], ["1"]],
  }],
  steps: [
    { frame: 0, pause: false, loop: false },
    { frame: 2, pause: false, loop: true },
    { frame: 4, pause: false, loop: false },
  ],
};

const allEvents = [
  { kind: "pause" },
  { kind: "playTo", frame: 3, loopAfter: true },
  { kind: "tick", timestamp: 0.125 },
  { kind: "tick", timestamp: 300.125 },
  { kind: "loopAt", frame: 3 },
  { kind: "advance" },
  { kind: "seek", frame: 5 },
];
const trace = adapter.replayTrace(animation, allEvents);
assert.equal(trace.ok, true);
assert.equal(trace.actions.length, allEvents.length + 1);
assert.equal(trace.actions[0].updates[0].a, "textContent");
assert.deepEqual(trace.actions[0].updates[1],
  { e: 1, a: "fill", v: "red" });
assert.equal(trace.actions.at(-1).frame, 5);

const live = adapter.createPlayer(animation);
assert.equal(live.ok, true);
assert.equal(JSON.stringify(live.player), "{}");
assert.equal(live.memory.animationBytes,
  live.memory.frontierAfterAnimation - live.memory.frontierBefore);
assert.ok(live.memory.animationObjectCount > 1);
assert.equal(live.memory.animationAllocationCalls, 1);
assert.equal(live.memory.frontierBefore, manifest.residentRuntime.heapBase);
assert.equal(live.memory.heapBase, manifest.residentRuntime.heapBase);
assert.equal(live.memory.stateSlotBytes,
  live.memory.persistentCheckpoint - live.memory.frontierAfterAnimation);
assert.equal(live.memory.stateSlotObjectCount,
  live.memory.stateSlotAllocationCalls);
assert.equal(live.memory.persistentAllocationCalls,
  live.memory.animationAllocationCalls + live.memory.stateSlotAllocationCalls);
for (const event of allEvents) {
  const result = adapter.dispatch(live.player, event);
  assert.equal(result.ok, true, result.error);
  assert.equal(result.memory.frontierBefore,
    live.memory.persistentCheckpoint);
  assert.equal(result.memory.postRewindFrontier,
    live.memory.persistentCheckpoint);
}
adapter.disposePlayer(live.player);
adapter.disposePlayer(live.player);
assert.throws(() => adapter.dispatch(live.player, { kind: "advance" }),
  /player is disposed/);

const steadyAnimation = {
  fps: 60,
  totalFrames: 2,
  segments: [{ sf: 0, fc: 2, pmap: [], params: [[], []] }],
  steps: [{ frame: 0, pause: false, loop: false }],
};
const steady = adapter.createPlayer(steadyAnimation);
assert.equal(steady.ok, true);
assert.equal(adapter.dispatch(steady.player, { kind: "advance" }).ok, true);
let peakFrontier = steady.memory.persistentCheckpoint;
for (let index = 0; index < 10_000; ++index) {
  const tick = adapter.dispatch(steady.player,
    { kind: "tick", timestamp: index / 7 });
  assert.equal(tick.ok, true, tick.error);
  assert.equal(tick.memory.postRewindFrontier,
    steady.memory.persistentCheckpoint);
  peakFrontier = Math.max(peakFrontier, tick.memory.peakFrontier);
}
// Source-compiled Float construction is allocation-faithful and rewound.
assert.equal(peakFrontier - steady.memory.persistentCheckpoint, 4232);
adapter.disposePlayer(steady.player);

const first = adapter.createPlayer(animation);
const second = adapter.createPlayer(animation);
assert.equal(first.ok && second.ok, true);
assert.equal(adapter.dispatch(first.player, { kind: "seek", frame: 5 })
  .action.frame, 5);
assert.equal(adapter.dispatch(second.player, { kind: "seek", frame: 1 })
  .action.frame, 1);
adapter.disposePlayer(first.player);
adapter.disposePlayer(second.player);

const invalid = adapter.createPlayer({ ...animation, totalFrames: 0 });
assert.deepEqual({ ok: invalid.ok, error: invalid.error }, {
  ok: false,
  error: "animation must contain at least one frame",
});

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
  events: allEvents.length,
  steadyTicks: 10_000,
  checkpoint: steady.memory.persistentCheckpoint,
  peakFrontier,
  animationObjects: live.memory.animationObjectCount,
  animationAllocationCalls: live.memory.animationAllocationCalls,
  functionImports: 0,
  memoryImports: 0,
}));
