import Illuminate.Animation.FirSelection

namespace IlluminateFirNative.SelectionExamples

open Illuminate.AnimationPlayer

def animation : SelectionAnimation := { timeline := {
  fps := 20
  totalFrames := 3
  segments := #[{
    startFrame := 0
    frameCount := 3
    paramMap := #[]
    params := #[]
  }]
  steps := #[{ frame := 0, pause := false, loop := false }]
} }

#guard match initialSelectionLive animation with
  | .ok initial =>
      initial.selection.frame == 0 &&
        initial.selection.localFrame == 0 &&
        initial.selection.segmentChanged &&
        initial.selection.playback == .paused &&
        !initial.scheduleNextFrame
  | .error _ => false

#guard match initialSelectionLive animation with
  | .ok initial =>
      let seek := transitionSelectionLive animation initial.state (.seek 2)
      seek.selection.frame == 2 &&
        seek.selection.localFrame == 2 &&
        seek.selection.playback == .finished &&
        !seek.scheduleNextFrame
  | .error _ => false

#guard match initialSelectionLive
    { animation with timeline := {
        animation.timeline with
        segments := #[{
          startFrame := 0
          frameCount := 3
          paramMap := #[{ element := 0, target := .textContent }]
          params := #[]
        }]
      } } with
  | .error _ => true
  | .ok _ => false

end IlluminateFirNative.SelectionExamples
