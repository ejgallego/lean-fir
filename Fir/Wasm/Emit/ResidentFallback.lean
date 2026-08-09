import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentFallback

open Fir.Wasm
open Lean
open Lean.Compiler

private def panicErasedParam : FVarId := ⟨`panicErased⟩
private def panicMessageParam : FVarId := ⟨`panicMessage⟩
private def panicDefaultParam : FVarId := ⟨`panicDefault⟩
private def inhabitedMonadParam : FVarId := ⟨`inhabitedMonad⟩
private def inhabitedDefaultParam : FVarId := ⟨`inhabitedDefault⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingExternal (declaration : Name)
  | incompatibleExternal (declaration : Name)
  | reservedDeclaration (name : Name)
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

/--
The two final declarations in the Lean 4.32 `prettyM` closure are failure
fallbacks. The accepted pretty-printer corpus never reaches either declaration;
keeping their resident definitions as unconditional traps preserves the
fail-closed behavior of the temporary JavaScript handlers while closing the
module's function-import surface.
-/
def externalDeclarations : Array Name := #[
  `panicCore,
  `instInhabitedOfMonad._redArg]

def externalName (declaration : Name) : Name :=
  ResidentNumeric.externalName declaration

def helperNames : Array Name := externalDeclarations.map externalName

private def expectedSignature? (declaration : Name) : Option Signature :=
  if declaration == `panicCore then
    some {
      params := #[.erased, .tobject, .object]
      results := #[.tobject] }
  else if declaration == `instInhabitedOfMonad._redArg then
    some {
      params := #[.object, .tobject]
      results := #[.tobject] }
  else
    none

private def externalTypes? (declaration : Name) : Option ExternalTypes :=
  let erased := LCNF.ImpureType.erased
  let object := LCNF.ImpureType.object
  let tobject := LCNF.ImpureType.tobject
  if declaration == `panicCore then
    some {
      params := #[erased, tobject, object]
      result := tobject }
  else if declaration == `instInhabitedOfMonad._redArg then
    some {
      params := #[object, tobject]
      result := tobject }
  else
    none

def panicFunction : Function := {
  name := externalName `panicCore
  params := #[
    (panicErasedParam, .erased),
    (panicMessageParam, .tobject),
    (panicDefaultParam, .object)]
  results := #[.tobject]
  locals := #[]
  body := [.unreachable] }

def inhabitedFunction : Function := {
  name := externalName `instInhabitedOfMonad._redArg
  params := #[
    (inhabitedMonadParam, .object),
    (inhabitedDefaultParam, .tobject)]
  results := #[.tobject]
  locals := #[]
  body := [.unreachable] }

def functions : Array Function := #[panicFunction, inhabitedFunction]

private partial def rewriteInstruction : Instruction → Instruction
  | .call (.declaration declaration) =>
      if externalDeclarations.contains declaration then
        .call (.declaration (externalName declaration))
      else
        .call (.declaration declaration)
  | .block label body =>
      .block label (body.map rewriteInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse
        (thenBody.map rewriteInstruction)
        (elseBody.map rewriteInstruction)
  | instruction => instruction

private def rewriteFunction (function : Function) : Function :=
  { function with body := function.body.map rewriteInstruction }

def internalize (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  for name in helperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) ||
        module.exports.contains name then
      throw (.reservedDeclaration name)
  for declaration in externalDeclarations do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.missingExternal declaration)
    let some signature := expectedSignature? declaration |
      throw (.incompatibleExternal declaration)
    unless imports[0]!.signature == signature do
      throw (.incompatibleExternal declaration)
  let imports := module.imports.filter fun import_ =>
    match import_.declaration? with
    | some declaration => !externalDeclarations.contains declaration
    | none => true
  let result : Module := {
    module with
    imports
    functions := module.functions.map rewriteFunction ++ functions
    exports := helperNames.foldl Fir.Wasm.addUnique module.exports }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

private def exampleImport (declaration : Name) : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := (expectedSignature? declaration).get!
  externalTypes? := externalTypes? declaration }

def exampleModule : Module := {
  imports := externalDeclarations.map exampleImport
  functions := #[]
  exports := #[]
  initializers := #[]
  runtimeOperations := #[] }

def residentExampleModule : Except LinkError Module :=
  internalize exampleModule

def manifest : Json :=
  Json.mkObj [
    ("sourceEntry", externalName `panicCore |>.toString),
    ("entry", externalName `panicCore |>.toString),
    ("params", Json.arr #["erased", "tobject", "object"]),
    ("result", "tobject"),
    ("closureDispatch", Json.arr #[]),
    ("closureDescriptors", Json.arr #[]),
    ("imports", Json.arr #[]),
    ("behavior", "fail-closed-unreachable"),
    ("status", "generation-only; W6 fallback contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      helperNames.all module.exports.contains &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentFallback
