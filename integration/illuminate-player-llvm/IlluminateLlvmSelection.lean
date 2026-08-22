import Illuminate.Animation.FirSelection

namespace Fir.LlvmSelection

open Illuminate AnimationPlayer

private def maximumCollectionLength : Nat := 1_000_000

private structure Cursor where
  input : ByteArray
  position : Nat := 0

private abbrev Parser (alpha : Type) := StateT Cursor (Except String) alpha

private def parseError (message : String) : Parser alpha :=
  throw message

private def readByte : Parser UInt8 := do
  let cursor <- get
  if h : cursor.position < cursor.input.size then
    let byte := cursor.input[cursor.position]
    set { cursor with position := cursor.position + 1 }
    pure byte
  else
    parseError "unexpected end of Illuminate selection-player request"

private def expectByte (expected : UInt8) (label : String) : Parser Unit := do
  let actual <- readByte
  unless actual == expected do
    parseError s!"invalid Illuminate selection-player {label}"

private def readUInt32 : Parser Nat := do
  let byte0 <- readByte
  let byte1 <- readByte
  let byte2 <- readByte
  let byte3 <- readByte
  pure (byte0.toNat +
    byte1.toNat * 256 +
    byte2.toNat * 65536 +
    byte3.toNat * 16777216)

private def readBool (label : String) : Parser Bool := do
  match <- readByte with
  | 0 => pure false
  | 1 => pure true
  | _ => parseError s!"{label} is not a Boolean"

private def readFloat : Parser Float := do
  let low <- readUInt32
  let high <- readUInt32
  let bits := UInt64.ofNat (low + high * 4294967296)
  pure (Float.ofBits bits)

private def checkCount (count : Nat) (label : String) : Parser Unit := do
  if count > maximumCollectionLength then
    parseError s!"{label} exceeds the collection limit"

private def finish : Parser Unit := do
  let cursor <- get
  unless cursor.position == cursor.input.size do
    parseError "Illuminate selection-player request has trailing bytes"

private def readAnimation : Parser SelectionAnimation := do
  expectByte 0x46 "animation magic"
  expectByte 0x49 "animation magic"
  expectByte 0x41 "animation magic"
  expectByte 0x31 "animation wire version"
  let fps <- readUInt32
  let totalFrames <- readUInt32
  let segmentCount <- readUInt32
  checkCount segmentCount "segment count"
  let mut segments := Array.mkEmpty segmentCount
  for _ in [:segmentCount] do
    let startFrame <- readUInt32
    let frameCount <- readUInt32
    segments := segments.push {
      startFrame
      frameCount
      paramMap := #[]
      params := #[]
    }
  let stepCount <- readUInt32
  checkCount stepCount "step count"
  let mut steps := Array.mkEmpty stepCount
  for _ in [:stepCount] do
    let frame <- readUInt32
    let pause <- readBool "step pause flag"
    let loop <- readBool "step loop flag"
    steps := steps.push { frame, pause, loop }
  finish
  pure { timeline := { fps, totalFrames, segments, steps } }

private def readEvent : Parser PlayerEvent := do
  expectByte 0x46 "event magic"
  expectByte 0x49 "event magic"
  expectByte 0x45 "event magic"
  expectByte 0x31 "event wire version"
  let event <- match <- readByte with
    | 0 => pure .advance
    | 1 => pure .pause
    | 2 => pure (.seek (← readUInt32))
    | 3 => pure (.playTo (← readUInt32) (← readBool "playTo loopAfter flag"))
    | 4 => pure (.loopAt (← readUInt32))
    | 5 => pure (.tick (← readFloat))
    | _ => parseError "unknown Illuminate player event tag"
  finish
  pure event

private def pushUInt32 (output : ByteArray) (value : Nat) : ByteArray :=
  output
    |>.push (UInt8.ofNat value)
    |>.push (UInt8.ofNat (value / 256))
    |>.push (UInt8.ofNat (value / 65536))
    |>.push (UInt8.ofNat (value / 16777216))

private def pushString (output : ByteArray) (value : String) : ByteArray := Id.run do
  let bytes := value.toUTF8
  let mut output := pushUInt32 output bytes.size
  for index in [0:bytes.size] do
    output := output.push bytes[index]!
  output

private def playbackTag : PlaybackStatus -> UInt8
  | .paused => 0
  | .playing => 1
  | .waiting => 2
  | .looping => 3
  | .finishingLoop => 4
  | .finished => 5

private def responsePrefix (status : UInt8) : ByteArray :=
  ByteArray.empty
    |>.push 0x46
    |>.push 0x49
    |>.push 0x52
    |>.push 0x31
    |>.push status

private def errorResponse (message : String) : ByteArray :=
  pushString (responsePrefix 1) message

private def successResponse (transition : LiveSelectionTransition) : ByteArray :=
  let selection := transition.selection
  responsePrefix 0
    |> fun output => pushUInt32 output selection.frame
    |> fun output => pushUInt32 output selection.step
    |> fun output => pushUInt32 output selection.segment
    |> fun output => pushUInt32 output selection.localFrame
    |>.push (if selection.segmentChanged then 1 else 0)
    |>.push (playbackTag selection.playback)
    |>.push (if transition.scheduleNextFrame then 1 else 0)

/-- Animation and state retained by the C ownership shim between dispatches. -/
structure RetainedPlayer where
  animation : SelectionAnimation
  state : PlayerState

/-- Result inspected by the C shim; the wire payload is always copied to JavaScript. -/
inductive WireResult where
  | error (response : ByteArray)
  | ok (player : RetainedPlayer) (response : ByteArray)

private def successful
    (player : @& RetainedPlayer)
    (transition : LiveSelectionTransition) : WireResult :=
  .ok { player with state := transition.state } (successResponse transition)

/-- Construct and validate one retained selection player from the compact animation wire. -/
@[export fir_illuminate_selection_create_wire]
def createWire (input : ByteArray) : WireResult :=
  match readAnimation.run { input } with
  | .error message => .error (errorResponse message)
  | .ok (animation, _) =>
      match AnimationPlayer.initialSelectionLive animation with
      | .error message => .error (errorResponse message)
      | .ok transition =>
          .ok { animation, state := transition.state } (successResponse transition)

/-- Dispatch every `PlayerEvent` constructor through the real Illuminate transition. -/
@[export fir_illuminate_selection_dispatch_wire]
def dispatchWire (player : RetainedPlayer) (input : ByteArray) : WireResult :=
  match readEvent.run { input } with
  | .error message => .error (errorResponse message)
  | .ok (event, _) =>
      successful player <|
        AnimationPlayer.transitionSelectionLive player.animation player.state event

/-- Scalar hot path: binary64 enters as a Wasm `f64`, without a wire conversion. -/
@[export fir_illuminate_selection_dispatch_tick]
def dispatchTick (player : RetainedPlayer) (timestamp : Float) : WireResult :=
  successful player <|
    AnimationPlayer.transitionSelectionLive player.animation player.state (.tick timestamp)

end Fir.LlvmSelection
