import Fir.Wasm.Emit.Binary
import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentPlatform

open Fir.Wasm
open Lean

/-!
# Wasm-resident target platform queries

The generated modules target wasm32 while explicitly transporting the 64-bit
scalar semantics of final-impure LCNF captured by FIR's x86_64 Lean toolchain.
`System.Platform.getNumBits` therefore returns the immediate natural `64` for
FIR's named `wasm32-lean64` contract. This deliberately differs from Lean's
native wasm32 runtime, where target `size_t` and the platform query are 32-bit;
see `FIR-BUG-wasm-none-usize-target-width-contract`.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | reservedDeclaration
  | missingExternal
  | incompatibleExternal
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

def declaration : Name := `System.Platform.getNumBits
def helperName : Name := `fir_ext_System_Platform_getNumBits

private def unitParam : FVarId := ⟨`unit⟩

def function : Function := {
  name := helperName
  params := #[(unitParam, .tagged)]
  results := #[.tobject]
  locals := #[]
  -- Immediate natural encoding is `(value << 1) | 1`.
  body := [.i32Const .tobject 129, .ret] }

private partial def rewriteInstruction : Instruction → Instruction
  | .call (.declaration candidate) =>
      if candidate == declaration then .call (.declaration helperName)
      else .call (.declaration candidate)
  | .block label body => .block label (body.map rewriteInstruction)
  | .loop label body => .loop label (body.map rewriteInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map rewriteInstruction) (elseBody.map rewriteInstruction)
  | instruction => instruction

def internalize (module : Module) (validate : Bool := true) : Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  if module.imports.any (·.declaration? == some helperName) ||
      module.functions.any (·.name == helperName) ||
      module.exports.contains helperName then
    throw .reservedDeclaration
  let imports := module.imports.filter (·.declaration? == some declaration)
  unless imports.size == 1 do
    throw .missingExternal
  unless imports[0]!.signature == {
      params := #[.tagged], results := #[.tobject] } do
    throw .incompatibleExternal
  let functions := module.functions.map fun candidate =>
    { candidate with body := candidate.body.map rewriteInstruction }
  let functions := functions.push function
  let result : Module := {
    module with
    imports := module.imports.filter (·.declaration? != some declaration)
    functions
    exports := Fir.Wasm.addUnique module.exports helperName
    runtimeOperations := Fir.Wasm.collectRuntimeOps functions }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

def internalizeAvailable (module : Module) (validate : Bool := true) : Except LinkError Module := do
  if module.imports.any (·.declaration? == some declaration) then
    internalize module validate
  else if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => return module
    | .error error => throw (.invalidInput error)
  else return module

private def externalImport : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := { params := #[.tagged], results := #[.tobject] }
  externalTypes? := some {
    params := #[Lean.Compiler.LCNF.ImpureType.tagged]
    result := Lean.Compiler.LCNF.ImpureType.tobject } }

def residentExampleModule : Except LinkError Module :=
  internalize {
    imports := #[externalImport]
    functions := #[]
    exports := #[]
    initializers := #[]
    runtimeOperations := #[]
    memory := some ResidentRuntime.residentMemory }

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr #[Json.mkObj [
      ("sourceEntry", declaration.toString),
      ("entry", helperName.toString)]]),
    ("imports", Json.arr #[]),
    ("target", "wasm32-lean64"),
    ("status", "generation-ready; W6 platform contract proof pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      module.exports.contains helperName &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentPlatform
