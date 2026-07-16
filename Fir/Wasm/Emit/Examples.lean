import Fir.Wasm.Emit.Binary
import Fir.Wasm.Examples

namespace Fir.Wasm.Emit.Examples

open Fir.Wasm

structure CorpusFixture where
  name : String
  program : Fir.LeanIR.ImpureProgram

def initialFixtures : List CorpusFixture := [
  { name := "literal", program := abiLiteralProgram },
  { name := "ctor-projection", program := abiCtorProjectionProgram },
  { name := "case", program := abiCaseProgram },
  { name := "default-case", program := abiDefaultCaseProgram }]

def initialCorpus : Array Fir.LeanIR.ImpureProgram :=
  initialFixtures.toArray.map (·.program)

def encodeProgram (program : Fir.LeanIR.ImpureProgram) : Except String ByteArray := do
  let module ←
    match lowerSupported program with
    | .ok module => pure module
    | .error error => throw s!"lowering failed: {repr error}"
  match encode module with
  | .ok bytes => pure bytes
  | .error error => throw s!"encoding failed: {repr error}"

#guard initialCorpus.all fun program => (encodeProgram program).isOk

#guard match encodeProgram abiCaseProgram, encodeProgram abiCaseProgram with
  | .ok first, .ok second => first == second
  | _, _ => false

#guard match encodeProgram abiLiteralProgram with
  | .ok bytes => bytes.data.extract 0 header.size == header
  | .error _ => false

end Fir.Wasm.Emit.Examples
