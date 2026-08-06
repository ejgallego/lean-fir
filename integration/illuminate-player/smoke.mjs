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
assert.deepEqual(WebAssembly.Module.imports(
  new WebAssembly.Module(bytes)), []);
console.log(JSON.stringify({
  ok: true,
  actions: result.actions.length,
  timings: result.timings,
  memory: result.memory,
}));
