import Illuminate.Animation.Player

namespace Illuminate.Animation.Native

open Illuminate.AnimationPlayer

private def replayEvents
    (animation : Illuminate.CompiledAnimation)
    (state : PlayerState)
    (actions : Array FrameAction) :
    List PlayerEvent → Except String (Array FrameAction)
  | [] => pure actions
  | event :: events => do
      let next ← transition animation state event
      replayEvents animation next.state (actions.push next.action) events

/--
Replay one complete pure animation trace without crossing a JSON or DOM
boundary. The animation state machine remains owned by Illuminate; this
facade only selects the structured whole-trace compilation boundary. A list
avoids exposing Lean's generated higher-order `Array.forIn` specialization at
the compiler boundary; the JavaScript adapter still accepts an ordinary event
array and encodes it as this list.
-/
def replayTraceNative
    (animation : Illuminate.CompiledAnimation)
    (events : List PlayerEvent) : Except String (Array FrameAction) := do
  let initial ← initialTransition animation
  replayEvents animation initial.state #[initial.action] events

end Illuminate.Animation.Native
