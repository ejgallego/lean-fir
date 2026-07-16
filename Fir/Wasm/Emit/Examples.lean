import Fir.Wasm.Emit.Binary
import Fir.Wasm.Examples

namespace Fir.Wasm.Emit.Examples

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples

structure CorpusFixture where
  name : String
  program : Fir.LeanIR.ImpureProgram

def abiStringHeapProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.str "reachable"))) (.return x))] }

def abiNaturalHeapProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat (maxTaggedPayload + 1)))) (.return x))] }

def abiNestedHeapProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.str "reachable"))) <|
      .let (letDecl y tobjectType (.lit (.nat (maxTaggedPayload + 1)))) <|
      .let (letDecl p tobjectType (.ctor pairInfo #[.fvar x, .fvar y])) <|
      .return p)] }

def initialFixtures : List CorpusFixture := [
  { name := "literal", program := abiLiteralProgram },
  { name := "ctor-projection", program := abiCtorProjectionProgram },
  { name := "case", program := abiCaseProgram },
  { name := "default-case", program := abiDefaultCaseProgram },
  { name := "string-heap", program := abiStringHeapProgram },
  { name := "natural-heap", program := abiNaturalHeapProgram },
  { name := "nested-heap", program := abiNestedHeapProgram }]

def initialCorpus : Array Fir.LeanIR.ImpureProgram :=
  initialFixtures.toArray.map (·.program)

#guard
  let names := initialFixtures.map (·.name)
  names.eraseDups.length == names.length

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
