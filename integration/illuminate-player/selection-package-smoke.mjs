import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";

import {
  createIlluminateSelectionPlayerAdapter,
  ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-selection-player-browser-adapter.mjs";

const bytes = await readFile("illuminate-selection-player.wasm");
const manifest = JSON.parse(await readFile(
  "illuminate-selection-player.wasm.json", "utf8"));
const build = JSON.parse(await readFile("BUILD.json", "utf8"));
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

assert.equal(build.schemaVersion, "fir.illuminate-selection-player.build/v1");
assert.equal(build.wasm.sha256, sha256(bytes));
assert.equal(build.capabilities.browserAdapter.apiVersion,
  ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION);
assert.equal(build.capabilities.inputLayout.version,
  ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION);
assert.equal(build.capabilities.ownership.version,
  ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION);

const module = new WebAssembly.Module(bytes);
assert.deepEqual(WebAssembly.Module.imports(module), []);
assert.deepEqual(WebAssembly.Module.exports(module), [
  { name: "Illuminate.AnimationPlayer.initialSelectionLive", kind: "function" },
  { name: "Illuminate.AnimationPlayer.transitionSelectionLive", kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);

const animation = {
  fps: 20,
  totalFrames: 6,
  segments: [{
    sf: 0,
    fc: 3,
    sync: "<svg>host-owned-zero</svg>",
    pmap: [{ e: 0, a: "textContent" }, { e: 1, a: "fill" }],
    params: [["α", "red"], ["β", "blue"], ["γ", "green"]],
  }, {
    sf: 3,
    fc: 3,
    sync: "<svg>host-owned-one</svg>",
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
  const row = segment.params[action.localFrame] ?? [];
  return segment.pmap.flatMap((binding, index) => row[index] === undefined
    ? []
    : [{ e: binding.e, a: binding.a, v: row[index] }]);
}

function adjacentFloat(value, direction) {
  const storage = new ArrayBuffer(8);
  const floats = new Float64Array(storage);
  const bits = new BigUint64Array(storage);
  floats[0] = value;
  bits[0] += direction > 0 ? 1n : -1n;
  return floats[0];
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
assert.ok(created.memory.selectionBytes <= 16 * 1024);
assert.ok(created.memory.persistentAllocationCalls <= 400);
assert.equal(created.memory.selectionAllocationCalls, 1);
assert.equal(created.memory.pagesAfter, 1);

const events = [
  { kind: "advance" },
  { kind: "pause" },
  { kind: "seek", frame: 3 },
  { kind: "playTo", frame: 1, loopAfter: true },
  { kind: "loopAt", frame: 2 },
  { kind: "tick", timestamp: adjacentFloat(50, -1) },
  { kind: "tick", timestamp: adjacentFloat(50, 1) },
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

const left = adapter.createPlayer(animation);
const right = adapter.createPlayer(animation);
assert.equal(left.ok && right.ok, true);
assert.equal(adapter.dispatch(left.player, { kind: "seek", frame: 5 })
  .action.frame, 5);
assert.equal(adapter.dispatch(right.player, { kind: "seek", frame: 1 })
  .action.frame, 1);
adapter.disposePlayer(left.player);
adapter.disposePlayer(right.player);

const invalid = adapter.createPlayer({ ...animation, totalFrames: 0 });
assert.equal(invalid.ok, false);
assert.match(invalid.error, /animation must contain at least one frame/);
assert.equal(invalid.memory.postRewindFrontier,
  invalid.memory.persistentCheckpoint);

const steady = adapter.createPlayer({
  fps: 60,
  totalFrames: 2,
  segments: [{ sf: 0, fc: 2 }],
  steps: [{ frame: 0, pause: false, loop: false }],
});
assert.equal(steady.ok, true, steady.error);
assert.equal(adapter.dispatch(steady.player, { kind: "advance" }).ok, true);
const checkpoint = steady.memory.persistentCheckpoint;
let peak = checkpoint;
for (let index = 0; index < 10_000; ++index) {
  const tick = adapter.dispatch(steady.player,
    { kind: "tick", timestamp: index / 7 });
  assert.equal(tick.ok, true, tick.error);
  assert.equal(tick.memory.postRewindFrontier, checkpoint);
  peak = Math.max(peak, tick.memory.peakFrontier);
}
adapter.disposePlayer(steady.player);

let clock = 0;
const timed = await createIlluminateSelectionPlayerAdapter({
  bytes,
  manifest,
  build,
  now: () => ++clock,
});
const measured = timed.createPlayer(animation);
assert.equal(measured.ok, true, measured.error);
assert.deepEqual(measured.timings, {
  instantiateMs: 1,
  projectMs: 1,
  selectionEncodeMs: 1,
  stateSlotMs: 1,
  executeMs: 1,
  decodeMs: 1,
  rewindMs: 1,
  totalMs: 15,
  overheadMs: 8,
});
timed.disposePlayer(measured.player);

console.log(JSON.stringify({
  ok: true,
  wasmBytes: bytes.byteLength,
  wasmSha256: sha256(bytes),
  selectionBytes: created.memory.selectionBytes,
  selectionObjects: created.memory.selectionObjectCount,
  persistentAllocations: created.memory.persistentAllocationCalls,
  pages: created.memory.pagesAfter,
  ticks: 10_000,
  checkpoint,
  peak,
}));
