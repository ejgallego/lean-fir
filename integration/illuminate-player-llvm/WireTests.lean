import IlluminateLlvmSelection

namespace Fir.LlvmSelection.WireTests

private def pushUInt32 (output : ByteArray) (value : Nat) : ByteArray :=
  output
    |>.push (UInt8.ofNat value)
    |>.push (UInt8.ofNat (value / 256))
    |>.push (UInt8.ofNat (value / 65536))
    |>.push (UInt8.ofNat (value / 16777216))

private def pushFloat (output : ByteArray) (value : Float) : ByteArray :=
  let bits := value.toBits.toNat
  pushUInt32 (pushUInt32 output bits) (bits / 4294967296)

private def animationWire : ByteArray :=
  ByteArray.empty
    |>.push 0x46 |>.push 0x49 |>.push 0x41 |>.push 0x31
    |> fun output => pushUInt32 output 10
    |> fun output => pushUInt32 output 6
    |> fun output => pushUInt32 output 2
    |> fun output => pushUInt32 output 0
    |> fun output => pushUInt32 output 2
    |> fun output => pushUInt32 output 2
    |> fun output => pushUInt32 output 4
    |> fun output => pushUInt32 output 3
    |> fun output => pushUInt32 output 0
    |>.push 0 |>.push 0
    |> fun output => pushUInt32 output 2
    |>.push 0 |>.push 1
    |> fun output => pushUInt32 output 4
    |>.push 0 |>.push 0

private def eventPrefix (tag : UInt8) : ByteArray :=
  ByteArray.empty
    |>.push 0x46 |>.push 0x49 |>.push 0x45 |>.push 0x31 |>.push tag

private def requireOk (label : String) : WireResult -> IO (RetainedPlayer × ByteArray)
  | .ok player response => pure (player, response)
  | .error _ => throw <| IO.userError s!"{label} unexpectedly failed"

private def requireError (label : String) : WireResult -> IO Unit
  | .error _ => pure ()
  | .ok _ _ => throw <| IO.userError s!"{label} unexpectedly succeeded"

private def requireEqual (label : String) (left right : ByteArray) : IO Unit :=
  unless left == right do
    throw <| IO.userError s!"{label} produced different wire responses"

def main : IO UInt32 := do
  let (initial, initialResponse) <- requireOk "initial" (createWire animationWire)
  if initialResponse.size != 24 then
    throw <| IO.userError "initial response has the wrong byte length"

  let events := #[
    eventPrefix 0,
    eventPrefix 1,
    pushUInt32 (eventPrefix 2) 3,
    (pushUInt32 (eventPrefix 3) 1).push 0,
    pushUInt32 (eventPrefix 4) 2,
    pushFloat (eventPrefix 5) (Float.ofBits 0x4049000000000001)]
  let mut player := initial
  for index in [:events.size] do
    let (next, _) <- requireOk s!"event {index}" (dispatchWire player events[index]!)
    player := next

  let tick := Float.ofBits 0x4048ffffffffffff
  let (_, genericResponse) <- requireOk "generic tick"
    (dispatchWire initial (pushFloat (eventPrefix 5) tick))
  let (_, scalarResponse) <- requireOk "scalar tick" (dispatchTick initial tick)
  requireEqual "bit-exact scalar tick" genericResponse scalarResponse

  requireError "malformed animation" (createWire (ByteArray.empty.push 0))
  requireError "malformed event" (dispatchWire initial (eventPrefix 255))
  IO.println "Illuminate LLVM selection wire tests passed"
  pure 0

end Fir.LlvmSelection.WireTests

def main : IO UInt32 :=
  Fir.LlvmSelection.WireTests.main
