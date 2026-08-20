import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import {
  createIlluminateSelectionPlayerAdapter,
  ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-selection-player-browser-adapter.mjs";

const bytes = await readFile("_build/illuminate-selection-player-complete.wasm");
const manifest = JSON.parse(await readFile(
  "_build/illuminate-selection-player-complete.wasm.json", "utf8"));
const build = { capabilities: {
  completeRuntime: { residentRuntime: manifest.residentRuntime },
  browserAdapter: { apiVersion:
    ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION },
  hotEvent: { version: ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION },
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

function adjacentFloat(value, direction) {
  const storage = new ArrayBuffer(8);
  const view = new DataView(storage);
  view.setFloat64(0, value, true);
  const bits = view.getBigUint64(0, true);
  view.setBigUint64(0, bits + (direction > 0 ? 1n : -1n), true);
  return view.getFloat64(0, true);
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
assert.equal(created.memory.heapBase, manifest.residentRuntime.heapBase);
assert.ok(created.memory.pagesAfter >= 1);
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

const genericTickPlayer = adapter.createPlayer(animation);
const scalarTickPlayer = adapter.createPlayer(animation);
const diagnosticTickPlayer = adapter.createPlayer(animation);
assert.equal(genericTickPlayer.ok && scalarTickPlayer.ok &&
  diagnosticTickPlayer.ok, true);
for (const timestamp of [adjacentFloat(50, -1), 50,
  adjacentFloat(50, 1), 300.125]) {
  const generic = adapter.dispatch(genericTickPlayer.player,
    { kind: "tick", timestamp });
  const scalar = adapter.dispatchTick(scalarTickPlayer.player, timestamp);
  const diagnostic = adapter.dispatchTickTimed(
    diagnosticTickPlayer.player, timestamp);
  assert.equal(generic.ok && scalar.ok && diagnostic.ok, true,
    generic.error ?? scalar.error ?? diagnostic.error);
  assert.deepEqual(scalar.action, generic.action);
  assert.deepEqual(diagnostic.action, generic.action);
  assert.equal(scalar.scheduleNextFrame, generic.scheduleNextFrame);
  assert.equal(diagnostic.scheduleNextFrame, generic.scheduleNextFrame);
  assert.ok(generic.memory.scratchBytes > 0);
  assert.ok(generic.memory.scratchAllocationCalls > 0);
  assert.equal(Object.hasOwn(scalar, "timings"), false);
  assert.equal(Object.hasOwn(scalar, "memory"), false);
  assert.equal(diagnostic.memory.scratchBytes, 0);
  assert.equal(diagnostic.memory.scratchAllocationCalls, 0);
  assert.equal(diagnostic.memory.frontierAfterEncode,
    diagnostic.memory.persistentCheckpoint);
  assert.equal(diagnostic.memory.postRewindFrontier,
    diagnostic.memory.persistentCheckpoint);
}
adapter.disposePlayer(genericTickPlayer.player);
adapter.disposePlayer(scalarTickPlayer.player);
adapter.disposePlayer(diagnosticTickPlayer.player);
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
const malformedTick = adapter.dispatchTick(steady.player, Number.NaN);
assert.equal(malformedTick.ok, false);
assert.match(malformedTick.error, /timestamp must be finite/);
assert.equal(Object.hasOwn(malformedTick, "timings"), false);
assert.equal(Object.hasOwn(malformedTick, "memory"), false);
const checkpoint = steady.memory.persistentCheckpoint;
for (let index = 0; index < 10_000; ++index) {
  const tick = adapter.dispatchTick(steady.player, index / 7);
  assert.equal(tick.ok, true, tick.error);
  assert.equal(Object.hasOwn(tick, "timings"), false);
  assert.equal(Object.hasOwn(tick, "memory"), false);
}
const auditedTick = adapter.dispatchTickTimed(steady.player, 10_000 / 7);
assert.equal(auditedTick.ok, true, auditedTick.error);
assert.equal(auditedTick.memory.frontierBefore, checkpoint);
assert.equal(auditedTick.memory.scratchBytes, 0);
assert.equal(auditedTick.memory.scratchAllocationCalls, 0);
assert.equal(auditedTick.memory.postRewindFrontier, checkpoint);
const peak = auditedTick.memory.peakFrontier;
adapter.disposePlayer(steady.player);

assert.deepEqual(WebAssembly.Module.imports(new WebAssembly.Module(bytes)), []);
assert.deepEqual(WebAssembly.Module.exports(new WebAssembly.Module(bytes)), [
  { name: "Illuminate.AnimationPlayer.initialSelectionLive", kind: "function" },
  { name: "Illuminate.AnimationPlayer.transitionSelectionLive", kind: "function" },
  { name: "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact", kind: "function" },
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
  hotEventScratchBytes: 0,
  checkpoint: steady.memory.persistentCheckpoint,
  peak,
}));
