import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import path from "node:path";
import vm from "node:vm";

import {
  createIlluminatePlayerAdapter,
  ILLUMINATE_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_PLAYER_OWNERSHIP_VERSION,
} from "./illuminate-player-browser-adapter.mjs";

const illuminateRoot = process.env.ILLUMINATE_ROOT ??
  path.resolve("../../../../../illuminate");
const coreSource = await readFile(
  path.join(illuminateRoot, "player_js/anim_core.js"), "utf8");
const core = vm.createContext({});
vm.runInContext(coreSource, core);

const {
  animCheckPauseSteps,
  animClampFrame,
  animComputeFrame,
  animFindCurrentStep,
  animFindSegment,
  animFindStepEnd,
  animWrapLoop,
} = core;

class LegacyPlayerOracle {
  constructor(data) {
    this.data = data;
    this.frame = 0;
    this.currentStep = 0;
    this.startTime = null;
    this.pauseFrame = 0;
    this.playing = false;
    this.waitingForClick = false;
    this.advancePending = false;
    this.finished = false;
    this.currentSegment = -1;
  }

  playback() {
    if (this.waitingForClick) return "waiting";
    if (this.finished) return "finished";
    if (!this.playing) return "paused";
    if (this.advancePending) return "finishingLoop";
    if (this.data.steps[this.currentStep]?.loop) return "looping";
    return "playing";
  }

  action() {
    this.frame = animClampFrame(this.frame, this.data.totalFrames);
    const segmentValue = animFindSegment(this.data.segments, this.frame);
    const segment = this.data.segments.indexOf(segmentValue);
    const localFrame = this.frame - segmentValue.sf;
    const segmentChanged = segment !== this.currentSegment;
    this.currentSegment = segment;
    const values = segmentValue.params[localFrame] ?? [];
    const updates = segmentValue.pmap.flatMap((binding, index) =>
      values[index] === undefined ? [] : [{
        e: binding.e,
        a: binding.a,
        v: values[index],
      }]);
    return {
      frame: this.frame,
      step: this.currentStep,
      segment,
      localFrame,
      segmentChanged,
      updates,
      playback: this.playback(),
    };
  }

  advance() {
    if (this.waitingForClick) {
      this.waitingForClick = false;
      this.startTime = null;
      this.playing = true;
      this.finished = false;
      return;
    }
    if (this.playing) {
      const step = this.data.steps[this.currentStep];
      if (step?.loop && this.currentStep + 1 < this.data.steps.length) {
        this.advancePending = true;
      } else {
        this.playing = false;
        this.pauseFrame = this.frame;
      }
      return;
    }
    if (this.pauseFrame >= this.data.totalFrames - 1) {
      this.pauseFrame = 0;
      this.currentStep = 0;
      this.frame = 0;
    }
    this.playing = true;
    this.startTime = null;
    this.finished = false;
  }

  seek(requested) {
    this.playing = false;
    this.waitingForClick = false;
    this.advancePending = false;
    this.frame = animClampFrame(requested, this.data.totalFrames);
    this.pauseFrame = this.frame;
    this.currentStep = animFindCurrentStep(this.data.steps, this.frame);
    this.finished = this.frame === this.data.totalFrames - 1;
  }

  tick(timestamp) {
    if (!this.playing || this.waitingForClick) return;
    if (this.startTime === null) this.startTime = timestamp;
    let frame = animComputeFrame(
      this.startTime, timestamp, this.data.fps, this.pauseFrame);
    const stepInfo = this.data.steps[this.currentStep];
    let isLooping = Boolean(stepInfo?.loop);
    if (isLooping) {
      const stepStart = stepInfo.frame;
      const stepEnd = animFindStepEnd(
        this.data.steps, this.currentStep, this.data.totalFrames);
      const loop = animWrapLoop(frame, stepStart, stepEnd);
      if (loop.didCycle) {
        if (this.advancePending) {
          this.advancePending = false;
          if (this.currentStep + 1 < this.data.steps.length) {
            this.currentStep += 1;
            frame = this.data.steps[this.currentStep].frame;
            this.pauseFrame = frame;
            this.startTime = null;
            isLooping = false;
          }
        } else {
          frame = loop.wrapped;
          this.startTime = timestamp;
          this.pauseFrame = stepStart;
        }
      }
    }
    if (frame >= this.data.totalFrames) {
      frame = this.data.totalFrames - 1;
      this.pauseFrame = frame;
      this.playing = false;
      this.finished = true;
    }
    if (!isLooping) {
      const pause = animCheckPauseSteps(
        this.data.steps, this.currentStep, frame);
      if (pause !== null) {
        frame = pause.pauseAtFrame;
        this.pauseFrame = frame;
        this.waitingForClick = true;
        this.currentStep = pause.pauseAtStep;
        this.frame = frame;
        return;
      }
      this.currentStep = animFindCurrentStep(this.data.steps, frame);
    }
    this.frame = frame;
  }

  dispatch(event) {
    if (event.kind === "advance") this.advance();
    else if (event.kind === "seek") this.seek(event.frame);
    else if (event.kind === "tick") this.tick(event.timestamp);
    else throw new Error(`unknown oracle event ${event.kind}`);
    return this.action();
  }
}

function segment(start, count, binding = { e: 2, a: "opacity" }) {
  return {
    sf: start,
    fc: count,
    sync: `<svg data-segment="${start}"><text data-e="${binding.e}"></text></svg>`,
    pmap: [binding],
    params: Array.from({ length: count }, (_, frame) => [`${start + frame}`]),
  };
}

function animation(totalFrames, steps, segments = [segment(0, totalFrames)]) {
  return { fps: 10, totalFrames, segments, steps };
}

const cases = [
  {
    name: "exact pause boundary",
    data: animation(12, [
      { frame: 0, pause: false, loop: false },
      { frame: 5, pause: true, loop: false },
    ]),
    events: [
      { kind: "advance" },
      { kind: "tick", timestamp: 100 },
      { kind: "tick", timestamp: 599.9 },
    ],
  },
  {
    name: "large timestamp jump",
    data: animation(10, [{ frame: 0, pause: false, loop: false }]),
    events: [
      { kind: "advance" },
      { kind: "tick", timestamp: 0 },
      { kind: "tick", timestamp: 5000 },
    ],
  },
  {
    name: "loop overshoot and exit",
    data: animation(20, [
      { frame: 0, pause: false, loop: true },
      { frame: 10, pause: false, loop: false },
    ]),
    events: [
      { kind: "advance" },
      { kind: "tick", timestamp: 0 },
      { kind: "tick", timestamp: 1150 },
      { kind: "advance" },
      { kind: "tick", timestamp: 2150 },
    ],
  },
  {
    name: "end seek and replay",
    data: animation(10, [{ frame: 0, pause: false, loop: false }]),
    events: [
      { kind: "seek", frame: 99 },
      { kind: "advance" },
      { kind: "tick", timestamp: 1000 },
      { kind: "tick", timestamp: 1100 },
    ],
  },
  {
    name: "segment and text patches",
    data: animation(4, [{ frame: 0, pause: false, loop: false }], [
      segment(0, 2), segment(2, 2, { e: 7, a: "textContent" }),
    ]),
    events: [
      { kind: "seek", frame: 1 },
      { kind: "seek", frame: 2 },
      { kind: "seek", frame: 3 },
    ],
  },
];

let randomState = 0x1_11_04_28;
function random() {
  randomState = (Math.imul(randomState, 1_664_525) + 1_013_904_223) >>> 0;
  return randomState / 0x1_0000_0000;
}

function randomCuts(totalFrames, maximumCuts) {
  const values = new Set([0]);
  const count = Math.min(maximumCuts, totalFrames);
  while (values.size < count) values.add(Math.floor(random() * totalFrames));
  return [...values].sort((left, right) => left - right);
}

for (let caseIndex = 0; caseIndex < 100; caseIndex += 1) {
  const totalFrames = 1 + Math.floor(random() * 30);
  const segmentCuts = randomCuts(totalFrames, 1 + Math.floor(random() * 5));
  const segments = segmentCuts.map((start, index) => {
    const end = segmentCuts[index + 1] ?? totalFrames;
    const binding = index % 2 === 0
      ? { e: index + 1, a: "opacity" }
      : { e: index + 1, a: "textContent" };
    return segment(start, end - start, binding);
  });
  const stepCuts = randomCuts(totalFrames, 1 + Math.floor(random() * 6));
  const steps = stepCuts.map((frame) => {
    const flag = Math.floor(random() * 4);
    return { frame, pause: flag === 1, loop: flag === 2 };
  });
  const events = [];
  let timestamp = Math.floor(random() * 1000);
  for (let eventIndex = 0; eventIndex < 30; eventIndex += 1) {
    const choice = random();
    if (choice < 0.25) events.push({ kind: "advance" });
    else if (choice < 0.45) {
      events.push({ kind: "seek",
        frame: Math.floor(random() * (totalFrames + 8)) });
    } else {
      timestamp += random() * 2000;
      events.push({ kind: "tick", timestamp });
    }
  }
  cases.push({
    name: `generated trace ${caseIndex}`,
    data: animation(totalFrames, steps, segments),
    events,
  });
}

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

for (const testCase of cases) {
  const oracle = new LegacyPlayerOracle(testCase.data);
  const expected = [oracle.action(),
    ...testCase.events.map((event) => oracle.dispatch(event))];
  const result = adapter.replayTrace(testCase.data, testCase.events);
  assert.equal(result.ok, true, `${testCase.name}: ${result.error ?? "failed"}`);
  assert.deepEqual(result.actions, expected, testCase.name);
}

console.log(`${cases.length} legacy/FIR-native player traces matched`);
