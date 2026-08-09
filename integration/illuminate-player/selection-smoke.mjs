import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import {
  createIlluminateSelectionPlayerAdapter,
  ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-selection-player-browser-adapter.mjs";

const bytes = await readFile("_build/illuminate-selection-player-resident.wasm");
const manifest = JSON.parse(await readFile(
  "_build/illuminate-selection-player-resident.wasm.json", "utf8"));
const build = { capabilities: {
  browserAdapter: { apiVersion:
    ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION },
  inputLayout: { version: ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION },
  ownership: { version: ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION },
} };

const animation = {
  fps: 20,
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

function materialize(action) {
  const segment = animation.segments[action.segment];
  return segment.pmap.map((binding, index) => ({
    e: binding.e,
    a: binding.a,
    v: segment.params[action.localFrame][index],
  }));
}

const adapter = await createIlluminateSelectionPlayerAdapter({
  bytes, manifest, build,
});
const created = adapter.createPlayer(animation);
assert.equal(created.ok, true, created.error);
assert.equal(JSON.stringify(created.player), "{}");
assert.equal(Object.hasOwn(created.action, "updates"), false);
assert.deepEqual(materialize(created.action), [
  { e: 0, a: "textContent", v: "α" },
  { e: 1, a: "fill", v: "red" },
]);
assert.equal(created.memory.selectionBytes,
  created.memory.frontierAfterSelection - created.memory.frontierBefore);
assert.ok(created.memory.selectionBytes <= 16 * 1024);
assert.equal(created.memory.selectionAllocationCalls, 1);
assert.ok(created.memory.persistentAllocationCalls <= 400);
assert.equal(created.memory.pagesAfter, 1);
assert.equal(created.memory.postRewindFrontier,
  created.memory.persistentCheckpoint);

const events = [
  { kind: "pause" },
  { kind: "playTo", frame: 3, loopAfter: true },
  { kind: "tick", timestamp: 49.99999999999999 },
  { kind: "tick", timestamp: 50.00000000000001 },
  { kind: "loopAt", frame: 3 },
  { kind: "advance" },
  { kind: "seek", frame: 5 },
];
for (const event of events) {
  const result = adapter.dispatch(created.player, event);
  assert.equal(result.ok, true, result.error);
  assert.equal(Object.hasOwn(result.action, "updates"), false);
  assert.equal(result.memory.frontierBefore,
    created.memory.persistentCheckpoint);
  assert.equal(result.memory.postRewindFrontier,
    created.memory.persistentCheckpoint);
}
adapter.disposePlayer(created.player);
adapter.disposePlayer(created.player);
assert.throws(() => adapter.dispatch(created.player, { kind: "advance" }),
  /player is disposed/);

const unread = {
  sf: 0,
  fc: 1,
  get sync() { throw new Error("selection projection read sync"); },
  get pmap() { throw new Error("selection projection read pmap"); },
  get params() { throw new Error("selection projection read params"); },
};
const hostOnly = adapter.createPlayer({
  fps: 20,
  totalFrames: 1,
  segments: [unread],
  steps: [{ frame: 0, pause: false, loop: false }],
});
assert.equal(hostOnly.ok, true, hostOnly.error);
adapter.disposePlayer(hostOnly.player);

const first = adapter.createPlayer(animation);
const second = adapter.createPlayer(animation);
assert.equal(first.ok && second.ok, true);
assert.equal(adapter.dispatch(first.player, { kind: "seek", frame: 5 })
  .action.frame, 5);
assert.equal(adapter.dispatch(second.player, { kind: "seek", frame: 1 })
  .action.frame, 1);
adapter.disposePlayer(first.player);
adapter.disposePlayer(second.player);

const steady = adapter.createPlayer({
  fps: 60,
  totalFrames: 2,
  segments: [{ sf: 0, fc: 2 }],
  steps: [{ frame: 0, pause: false, loop: false }],
});
assert.equal(steady.ok, true, steady.error);
assert.equal(adapter.dispatch(steady.player, { kind: "advance" }).ok, true);
let peak = steady.memory.persistentCheckpoint;
for (let index = 0; index < 10_000; ++index) {
  const tick = adapter.dispatch(steady.player,
    { kind: "tick", timestamp: index / 7 });
  assert.equal(tick.ok, true, tick.error);
  assert.equal(tick.memory.postRewindFrontier,
    steady.memory.persistentCheckpoint);
  peak = Math.max(peak, tick.memory.peakFrontier);
}
adapter.disposePlayer(steady.player);

assert.deepEqual(WebAssembly.Module.imports(new WebAssembly.Module(bytes)), []);
assert.deepEqual(WebAssembly.Module.exports(new WebAssembly.Module(bytes)), [
  { name: "Illuminate.AnimationPlayer.initialSelectionLive", kind: "function" },
  { name: "Illuminate.AnimationPlayer.transitionSelectionLive", kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);

console.log(JSON.stringify({
  ok: true,
  selectionBytes: created.memory.selectionBytes,
  selectionObjects: created.memory.selectionObjectCount,
  persistentAllocations: created.memory.persistentAllocationCalls,
  pages: created.memory.pagesAfter,
  ticks: 10_000,
  checkpoint: steady.memory.persistentCheckpoint,
  peak,
}));
