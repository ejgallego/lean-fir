import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import path from "node:path";

import { createIlluminatePlayerAdapter } from
  "./illuminate-player-browser-adapter.mjs";
import {
  createIlluminateSelectionPlayerAdapter,
  ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-selection-player-browser-adapter.mjs";

const illuminateRoot = process.env.ILLUMINATE_ROOT ??
  path.resolve("../../../../../illuminate");
const html = await readFile(path.join(illuminateRoot,
  "test_output/anim-comparison.html"), "utf8");
const marker = "var examples = ";
const start = html.indexOf(marker);
assert.notEqual(start, -1, "comparison example payload is missing");
const jsonStart = start + marker.length;
const jsonEnd = html.indexOf(";\n", jsonStart);
const examples = JSON.parse(html.slice(jsonStart, jsonEnd));
assert.equal(examples.length, 16, "dashboard example inventory changed");

async function load(stem, create, build) {
  const bytes = await readFile(`_build/${stem}.wasm`);
  const manifest = JSON.parse(await readFile(`_build/${stem}.wasm.json`,
    "utf8"));
  return create({ bytes, manifest, build });
}

const v3Build = JSON.parse(await readFile(
  "_build/illuminate-player-current/BUILD.json", "utf8"));
const v3 = await load("illuminate-player-resident",
  createIlluminatePlayerAdapter, v3Build);
const v4 = await load("illuminate-selection-player-resident",
  createIlluminateSelectionPlayerAdapter, { capabilities: {
    browserAdapter: { apiVersion:
      ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION },
    inputLayout: { version: ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION },
    ownership: { version: ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION },
  } });

function materialize(animation, action) {
  const segment = animation.segments[action.segment];
  const values = segment.params[action.localFrame] ?? [];
  return {
    frame: action.frame,
    step: action.step,
    segment: action.segment,
    localFrame: action.localFrame,
    segmentChanged: action.segmentChanged,
    updates: segment.pmap.flatMap((binding, index) =>
      values[index] === undefined ? [] : [{
        e: binding.e,
        a: binding.a,
        v: values[index],
      }]),
    playback: action.playback,
  };
}

for (const { title, data } of examples) {
  const frames = new Set([0, data.totalFrames - 1]);
  for (const segment of data.segments) {
    frames.add(segment.sf);
    frames.add(segment.sf + segment.fc - 1);
  }
  for (const step of data.steps) frames.add(step.frame);
  const events = [...frames].sort((left, right) => left - right)
    .map((frame) => ({ kind: "seek", frame }));
  const full = v3.replayTrace(data, events);
  const compact = v4.replayTrace(data, events);
  assert.equal(full.ok, true, `${title} v3: ${full.error}`);
  assert.equal(compact.ok, true, `${title} v4: ${compact.error}`);
  assert.deepEqual(compact.actions.map((action) => materialize(data, action)),
    full.actions, title);
}

console.log(`${examples.length}/16 dashboard animations matched at every ` +
  "segment boundary, step, and final frame");
