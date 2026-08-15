import Fir.Wasm.Emit.ExternalRuntime
import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentLibm

open Fir.Wasm
open Lean

/-!
# Standard libm frontier

Lean deliberately leaves these six `Float` declarations opaque and implements
them with the platform C math library.  This module describes that boundary
without assigning stronger, core-Wasm semantics to it.  The exported bit-lane
probes make the boundary executable and preserve every binary64 input bit.

`integration/wasm-runtime/libm-runtime.c` supplies the imports.  The generic
external-runtime linker then removes the boundary and produces a zero-import
module with the exact exports declared here.
-/

def declarations : Array Name := ExternalRuntime.compiledDeclarations

private def valueParam : FVarId := ⟨`value⟩
private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩

def signature (declaration : Name) : Option Signature :=
  if declaration == `Float.atan2 then
    some { params := #[.float, .float], results := #[.float] }
  else if declarations.contains declaration then
    some { params := #[.float], results := #[.float] }
  else
    none

private def externalTypes (signature : Signature) : ExternalTypes := {
  params := signature.params.map fun _ => Compiler.LCNF.ImpureType.float
  result := Compiler.LCNF.ImpureType.float }

def externalImport (declaration : Name) : Import :=
  let signature := (signature declaration).get!
  {
    key := .external declaration
    moduleName := "lean.extern"
    itemName := declaration.toString
    signature
    externalTypes? := some (externalTypes signature) }

def probeName (declaration : Name) : Name :=
  Name.mkSimple s!"resident_{declaration.toString.replace "." "_"}_bits"

private def unaryProbe (declaration : Name) : Function := {
  name := probeName declaration
  params := #[(valueParam, .uint64)]
  results := #[.uint64]
  locals := #[]
  body := [
    .localGet valueParam,
    .f64ReinterpretI64 .float,
    .call (.declaration declaration),
    .i64ReinterpretF64 .uint64,
    .ret] }

private def binaryProbe (declaration : Name) : Function := {
  name := probeName declaration
  params := #[(leftParam, .uint64), (rightParam, .uint64)]
  results := #[.uint64]
  locals := #[]
  body := [
    .localGet leftParam,
    .f64ReinterpretI64 .float,
    .localGet rightParam,
    .f64ReinterpretI64 .float,
    .call (.declaration declaration),
    .i64ReinterpretF64 .uint64,
    .ret] }

def probes : Array Function := declarations.map fun declaration =>
  if declaration == `Float.atan2 then binaryProbe declaration
  else unaryProbe declaration

/-- Imported libm frontier before the separately compiled runtime is linked. -/
def frontierModule : Module := {
  imports := declarations.map externalImport
  functions := probes
  exports := probes.map (·.name)
  initializers := #[]
  runtimeOperations := #[]
  memory := some ResidentRuntime.residentMemory }

def manifest : Json := Json.mkObj [
  ("entries", Json.arr <| declarations.map fun declaration =>
    Json.mkObj [
      ("sourceEntry", declaration.toString),
      ("entry", probeName declaration |>.toString)]),
  ("imports", Json.arr <| declarations.map fun declaration =>
    Json.mkObj [
      ("module", "lean.extern"),
      ("name", declaration.toString)]),
  ("runtime", "fir.standard-libm/v2"),
  ("numericContract", "platform-libm-special-values-and-bounded-error"),
  ("status", "generation-ready; W6 libm contract proofs pending")]

#guard declarations.size == 6
#guard declarations.contains `Float.atan2
#guard declarations.all fun declaration => (signature declaration).isSome
#guard frontierModule.imports.size == declarations.size
#guard frontierModule.functions.size == declarations.size
#guard frontierModule.runtimeOperations.isEmpty
#guard frontierModule.memory == some ResidentRuntime.residentMemory
#guard (Fir.Wasm.validateModule frontierModule).isOk
#guard (Fir.Wasm.Emit.encode frontierModule).isOk

end Fir.Wasm.Emit.ResidentLibm
