import Std.Data.HashMap

namespace Fir.LcnfCWasm

private structure RuntimeState where
  values : Array UInt64
  table : Std.HashMap UInt64 UInt64
  next : UInt64

private partial def buildRuntimeState
    (remaining : UInt64)
    (state : RuntimeState) : RuntimeState :=
  if remaining == 0 then
    state
  else
    let next := state.next * 6364136223846793005 + 1442695040888963407
    let value := next ^^^ (remaining * 11400714819323198485)
    buildRuntimeState (remaining - 1) {
      values := state.values.push value
      table := state.table.insert remaining value
      next
    }

private def requireKey
    (table : Std.HashMap UInt64 UInt64)
    (key : UInt64) : Except String UInt64 :=
  match table[key]? with
  | some value => .ok value
  | none => .error s!"missing:{key}"

@[export fir_lcnf_c_runtime_checksum]
def runtimeChecksum (rounds seed : UInt64) : UInt64 :=
  let state := buildRuntimeState rounds {
    values := #[]
    table := {}
    next := seed
  }
  let arraySum := state.values.foldl (fun sum value => sum + value) 0
  let first :=
    match requireKey state.table rounds with
    | .ok value => value
    | .error message => message.utf8ByteSize.toUInt64
  let missing :=
    match requireKey state.table 0 with
    | .ok value => value
    | .error message => message.utf8ByteSize.toUInt64
  let transforms : Array (UInt64 → UInt64) :=
    #[fun value => value + seed, fun value => value ^^^ rounds]
  let closureValue := transforms.foldl (fun value transform => transform value) arraySum
  let label := s!"fir:{rounds}:{state.values.size}:{state.table.size}"
  closureValue + first + missing + label.utf8ByteSize.toUInt64

@[export fir_lcnf_c_runtime_probe]
def runtimeProbe : IO UInt32 := do
  IO.eprintln "fir-lcnf-c:init-std"
  pure 0

end Fir.LcnfCWasm
