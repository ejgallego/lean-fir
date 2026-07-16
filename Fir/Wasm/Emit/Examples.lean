import Fir.Wasm.Emit.Binary
import Fir.Wasm.Examples

namespace Fir.Wasm.Emit.Examples

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples
open Lean.Compiler

structure CorpusFixture where
  name : String
  program : Fir.LeanIR.ImpureProgram
  args : Array Value := #[]

def abiDirectLiteralProgram (type : Lean.Expr) (literal : LCNF.LitValue) :
    Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] type (.code <|
      .let (letDecl x type (.lit literal)) (.return x))] }

def abiUInt8MaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram u8Type (.uint8 255)

def abiUInt16MaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram LCNF.ImpureType.uint16 (.uint16 65535)

def abiUInt32MaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram LCNF.ImpureType.uint32 (.uint32 4294967295)

def abiUInt64MaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram u64Type (.uint64 18446744073709551615)

def abiUSizeMaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram usizeType (.usize 18446744073709551615)

def abiIdentityProgram (type : Lean.Expr) : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x type] type (.code (.return x))] }

def abiFirstTaggedArgumentProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x tobjectType, param y tobjectType]
      tobjectType (.code (.return x))] }

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

def abiObjectProjectionFaultProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 7))) <|
      .let (letDecl y tobjectType (.lit (.nat 8))) <|
      .let (letDecl p objType (.ctor pairInfo #[.fvar x, .fvar y])) <|
      .let (letDecl r tobjectType (.oproj 2 p)) <|
      .return r)] }

def initialFixtures : List CorpusFixture := [
  { name := "literal", program := abiLiteralProgram },
  { name := "erased", program := abiErasedProgram },
  { name := "uint8-max", program := abiUInt8MaxProgram },
  { name := "uint16-max", program := abiUInt16MaxProgram },
  { name := "uint32-max", program := abiUInt32MaxProgram },
  { name := "uint64-max", program := abiUInt64MaxProgram },
  { name := "usize-max", program := abiUSizeMaxProgram },
  { name := "arg-erased", program := abiIdentityProgram erasedType, args := #[.erased] },
  { name := "arg-tagged-first", program := abiFirstTaggedArgumentProgram,
    args := #[.object (.tagged 11), .object (.tagged 22)] },
  { name := "arg-uint8-max", program := abiIdentityProgram u8Type,
    args := #[.scalar (.uint8 255)] },
  { name := "arg-uint16-max", program := abiIdentityProgram LCNF.ImpureType.uint16,
    args := #[.scalar (.uint16 65535)] },
  { name := "arg-uint32-max", program := abiIdentityProgram LCNF.ImpureType.uint32,
    args := #[.scalar (.uint32 4294967295)] },
  { name := "arg-uint64-max", program := abiIdentityProgram u64Type,
    args := #[.scalar (.uint64 18446744073709551615)] },
  { name := "arg-usize-max", program := abiIdentityProgram usizeType,
    args := #[.usize 18446744073709551615] },
  { name := "ctor-projection", program := abiCtorProjectionProgram },
  { name := "case", program := abiCaseProgram },
  { name := "default-case", program := abiDefaultCaseProgram },
  { name := "string-heap", program := abiStringHeapProgram },
  { name := "natural-heap", program := abiNaturalHeapProgram },
  { name := "nested-heap", program := abiNestedHeapProgram },
  { name := "projection-fault", program := abiObjectProjectionFaultProgram }]

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
