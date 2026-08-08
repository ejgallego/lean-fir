import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import { createIlluminatePlayerAdapter } from
  "./illuminate-player-browser-adapter.mjs";

const here = new URL("./", import.meta.url);
const bytes = await readFile(new URL("illuminate-player.wasm", here));
const manifest = JSON.parse(await readFile(
  new URL("illuminate-player.wasm.json", here), "utf8"));
const build = JSON.parse(await readFile(new URL("BUILD.json", here), "utf8"));
const adapter = await createIlluminatePlayerAdapter({ bytes, manifest, build });

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

const allEvents = adapter.replayTrace(animation, [
  { kind: "pause" },
  { kind: "playTo", frame: 3, loopAfter: true },
  { kind: "tick", timestamp: 0.125 },
  { kind: "tick", timestamp: 300.125 },
  { kind: "loopAt", frame: 3 },
  { kind: "advance" },
  { kind: "seek", frame: 5 },
]);
assert.equal(allEvents.ok, true);
assert.equal(allEvents.actions.length, 8);
assert.equal(allEvents.actions.at(-1).frame, 5);
assert.equal(allEvents.actions.at(-1).playback, "finished");
assert.equal(allEvents.actions[0].updates[0].v, "α");
assert.equal(allEvents.actions[0].updates[0].a, "textContent");
assert.deepEqual(allEvents.actions[0].updates[1],
  { e: 1, a: "fill", v: "red" });

const roundingBoundary = adapter.replayTrace(animation, [
  { kind: "advance" },
  { kind: "tick", timestamp: 0 },
  { kind: "tick", timestamp: 49.999 },
  { kind: "tick", timestamp: 50.001 },
]);
assert.equal(roundingBoundary.ok, true);
assert.deepEqual(roundingBoundary.actions.slice(-2).map(({ frame }) => frame),
  [0, 1]);

const repeated = adapter.replayTrace(animation, [{ kind: "seek", frame: 3 }]);
assert.equal(repeated.ok, true);
assert.equal(repeated.actions.at(-1).segment, 1);
assert.ok(repeated.memory.frontierBefore >=
  roundingBoundary.memory.frontierAfterDecode);

const invalid = adapter.replayTrace({ ...animation, totalFrames: 0 }, []);
assert.deepEqual({ ok: invalid.ok, error: invalid.error }, {
  ok: false,
  error: "animation must contain at least one frame",
});
const emptySegments = adapter.replayTrace({ ...animation, segments: [] }, []);
assert.equal(emptySegments.ok, false);

assert.deepEqual(WebAssembly.Module.imports(new WebAssembly.Module(bytes)), []);
assert.deepEqual(WebAssembly.Module.exports(new WebAssembly.Module(bytes)), [
  { name: manifest.entry, kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);
console.log(JSON.stringify({
  ok: true,
  calls: 5,
  events: 11,
  functionImports: 0,
  memoryImports: 0,
  frontier: emptySegments.memory.frontierAfterDecode,
}));
