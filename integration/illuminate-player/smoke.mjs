import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import {
  createIlluminatePlayerAdapter,
  ILLUMINATE_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-player-browser-adapter.mjs";

const bytes = await readFile("_build/illuminate-player-resident.wasm");
const manifest = JSON.parse(await readFile(
  "_build/illuminate-player-resident.wasm.json", "utf8"));
const build = {
  capabilities: {
    browserAdapter: { apiVersion: ILLUMINATE_PLAYER_ADAPTER_API_VERSION },
    inputLayout: { version: ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION },
    ownership: { version: ILLUMINATE_PLAYER_OWNERSHIP_VERSION },
  },
};

const adapter = await createIlluminatePlayerAdapter({ bytes, manifest, build });
const animation = {
  fps: 10,
  totalFrames: 3,
  segments: [{
    sf: 0,
    fc: 3,
    sync: "<svg>λ</svg>",
    pmap: [{ e: 0, a: "textContent" }, { e: 1, a: "fill" }],
    params: [["α", "red"], ["β", "blue"], ["γ", "green"]],
  }],
  steps: [{ frame: 0, pause: false, loop: false }],
};

const result = adapter.replayTrace(animation, [
  { kind: "seek", frame: 2 },
]);
assert.equal(result.ok, true);
assert.deepEqual(result.actions, [
  {
    frame: 0,
    step: 0,
    segment: 0,
    localFrame: 0,
    segmentChanged: true,
    updates: [
      { e: 0, a: "textContent", v: "α" },
      { e: 1, a: "fill", v: "red" },
    ],
    playback: "paused",
  },
  {
    frame: 2,
    step: 0,
    segment: 0,
    localFrame: 2,
    segmentChanged: false,
    updates: [
      { e: 0, a: "textContent", v: "γ" },
      { e: 1, a: "fill", v: "green" },
    ],
    playback: "finished",
  },
]);

const empty = adapter.replayTrace(animation, []);
assert.equal(empty.ok, true);
assert.equal(empty.actions.length, 1);

const unreadSyncSegment = { ...animation.segments[0] };
Object.defineProperty(unreadSyncSegment, "sync", {
  enumerable: true,
  get() { throw new Error("sync SVG must not be read during projection"); },
});
const withoutSvg = adapter.replayTrace({
  ...animation,
  segments: [unreadSyncSegment],
}, []);
assert.equal(withoutSvg.ok, true);
assert.equal(withoutSvg.memory.inputBytes, empty.memory.inputBytes);

let fpsReads = 0;
const countedAnimation = { ...animation };
Object.defineProperty(countedAnimation, "fps", {
  enumerable: true,
  get() { fpsReads += 1; return 10; },
});
assert.equal(adapter.replayTrace(countedAnimation, []).ok, true);
assert.equal(fpsReads, 1, "projection must read and validate fps once per replay");

const frontierBeforeInvalid = adapter.synchronizeFrontier();
assert.throws(() => adapter.replayTrace({ ...animation, fps: 1.5 }, []),
  /animation\.fps must be a uint32 safe integer/);
assert.equal(adapter.synchronizeFrontier(), frontierBeforeInvalid,
  "projection failure must occur before Wasm allocation");

const prepared = adapter.prepare(animation, [{ kind: "tick", timestamp: 0.125 }]);
assert.equal("args" in prepared, false, "prepared handles must hide raw words");
const executed = adapter.execute(prepared);
assert.equal("physicalResult" in executed, false,
  "execution handles must hide raw result words");
assert.throws(() => adapter.execute(prepared), /fresh prepared handle/);
assert.equal(adapter.decode(executed).ok, true);
assert.throws(() => adapter.decode(executed), /fresh execution handle/);

let clockValue = 0;
const fakeNow = () => clockValue++;
const timedAdapter = await createIlluminatePlayerAdapter({
  bytes,
  manifest,
  build,
  now: fakeNow,
});
const timed = timedAdapter.replayTrace(animation, []);
assert.deepEqual(timed.timings, {
  projectMs: 1,
  encodeMs: 1,
  prepareMs: 5,
  executeMs: 1,
  decodeMs: 1,
  totalMs: 11,
  overheadMs: 7,
});
assert.ok(timed.timings.prepareMs >=
  timed.timings.projectMs + timed.timings.encodeMs);
assert.ok(timed.timings.totalMs >= timed.timings.prepareMs +
  timed.timings.executeMs + timed.timings.decodeMs);
assert.deepEqual(WebAssembly.Module.imports(
  new WebAssembly.Module(bytes)), []);
assert.deepEqual(WebAssembly.Module.exports(new WebAssembly.Module(bytes)), [
  { name: manifest.entry, kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);
console.log(JSON.stringify({
  ok: true,
  actions: result.actions.length,
  timings: result.timings,
  memory: result.memory,
}));
