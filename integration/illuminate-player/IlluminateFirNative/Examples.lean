import Illuminate.Animation.FirLive

namespace IlluminateFirNative.Examples

open Illuminate
open Illuminate.AnimationPlayer

def animation : PlayerAnimation := {
  fps := 10
  totalFrames := 3
  segments := #[{
    startFrame := 0
    frameCount := 3
    paramMap := #[
      { element := 0, target := .textContent },
      { element := 1, target := .attribute "fill" }]
    params := #[#["α", "red"], #["β", "blue"], #["γ", "green"]]
  }]
  steps := #[{ frame := 0, pause := false, loop := false }]
}

def expectedSeek : Array FrameAction := #[
  {
    frame := 0
    step := 0
    segment := 0
    localFrame := 0
    segmentChanged := true
    updates := #[
      { element := 0, target := .textContent, value := "α" },
      { element := 1, target := .attribute "fill", value := "red" }]
    playback := .paused
  },
  {
    frame := 2
    step := 0
    segment := 0
    localFrame := 2
    segmentChanged := false
    updates := #[
      { element := 0, target := .textContent, value := "γ" },
      { element := 1, target := .attribute "fill", value := "green" }]
    playback := .finished
  }]

#guard match Illuminate.AnimationPlayer.replayTrace animation [.seek 2] with
  | .ok actions => actions == expectedSeek
  | .error _ => false

#guard match Illuminate.AnimationPlayer.initialLive animation with
  | .ok initial =>
      initial.action == expectedSeek[0]! && !initial.scheduleNextFrame &&
        let seek := Illuminate.AnimationPlayer.transitionLive animation
          initial.state (.seek 2)
        seek.action == expectedSeek[1]! && !seek.scheduleNextFrame
  | .error _ => false

#guard match Illuminate.AnimationPlayer.initialLive
    { animation with totalFrames := 0 } with
  | .error _ => true
  | .ok _ => false

end IlluminateFirNative.Examples
