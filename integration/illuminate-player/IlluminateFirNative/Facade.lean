import Illuminate.Animation.Player

namespace Illuminate.Animation.Native

open Illuminate.AnimationPlayer

/--
Aliases Illuminate's prepared whole-trace entry without reproducing its loop,
validation, or state-machine logic.
-/
def replayTraceNative
    (animation : PlayerAnimation)
    (events : List PlayerEvent) : Except String (Array FrameAction) :=
  Illuminate.AnimationPlayer.replayTrace animation events

end Illuminate.Animation.Native
