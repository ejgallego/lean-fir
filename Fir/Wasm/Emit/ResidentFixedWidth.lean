import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentFixedWidth

open Fir.Wasm
open Lean
open Lean.Compiler

/-!
# Wasm-resident fixed-width integer operations

Lean's raw fixed-width externs are ordinary machine operations.  This module
internalizes the subset currently exercised by the generic ByteArray/DEFLATE
frontier.  The declarations and signatures are source-level Lean APIs; no
lean-zip declaration is named here.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingNumericHelper (name : Name)
  | reservedDeclaration (name : Name)
  | missingExternal (name : Name)
  | incompatibleExternal (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def valueParam : FVarId := ⟨`value⟩
private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def sumLocal : FVarId := ⟨`sum⟩
private def intersectionLocal : FVarId := ⟨`intersection⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def uint8ResultLocal : FVarId := ⟨`uint8Result⟩
private def uint16ResultLocal : FVarId := ⟨`uint16Result⟩

def externalDeclarations : Array Name := #[
  `UInt16.shiftRight,
  `UInt16.ofNat,
  `UInt16.toUInt8,
  `UInt16.land,
  `UInt16.xor]

def externalName (declaration : Name) : Name :=
  Name.mkSimple s!"fir_ext_{declaration.toString.replace "." "_"}"

def helperNames : Array Name := externalDeclarations.map externalName

private def retypeRaw (result : AbiKind) (resultLocal : FVarId) :
    List Instruction := [
  .localSet rawLocal,
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet rawLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load result 0,
  .localSet resultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet resultLocal,
  .ret]

def shiftRightFunction : Function := {
  name := externalName `UInt16.shiftRight
  params := #[(leftParam, .uint16), (rightParam, .uint16)]
  results := #[.uint16]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (uint16ResultLocal, .uint16)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i32Const .uint32 16,
    .i32RemU,
    .i32ShrU] ++ retypeRaw .uint16 uint16ResultLocal }

def ofNatFunction : Function := {
  name := externalName `UInt16.ofNat
  params := #[(valueParam, .tobject)]
  results := #[.uint16]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (uint16ResultLocal, .uint16)]
  body := [
    .localGet valueParam,
    .call (.declaration ResidentNumeric.validateNaturalName),
    .localGet valueParam,
    .call (.declaration ResidentNumeric.naturalLowName),
    .i32Const .uint32 0xffff,
    .i32And] ++ retypeRaw .uint16 uint16ResultLocal }

def toUInt8Function : Function := {
  name := externalName `UInt16.toUInt8
  params := #[(valueParam, .uint16)]
  results := #[.uint8]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (uint8ResultLocal, .uint8)]
  body := [
    .localGet valueParam,
    .i32Const .uint32 0xff,
    .i32And] ++ retypeRaw .uint8 uint8ResultLocal }

def landFunction : Function := {
  name := externalName `UInt16.land
  params := #[(leftParam, .uint16), (rightParam, .uint16)]
  results := #[.uint16]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (uint16ResultLocal, .uint16)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i32And] ++ retypeRaw .uint16 uint16ResultLocal }

/-- `a xor b = a + b - 2 * (a and b)` in the wasm32 bit ring. -/
def xorFunction : Function := {
  name := externalName `UInt16.xor
  params := #[(leftParam, .uint16), (rightParam, .uint16)]
  results := #[.uint16]
  locals := #[(rawLocal, .uint32), (sumLocal, .uint32),
    (intersectionLocal, .uint32), (savedScratchLocal, .uint32),
    (uint16ResultLocal, .uint16)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i32Add,
    .localSet sumLocal,
    .localGet leftParam,
    .localGet rightParam,
    .i32And,
    .localSet intersectionLocal,
    .localGet sumLocal,
    .localGet intersectionLocal,
    .localGet intersectionLocal,
    .i32Add,
    .i32Sub] ++ retypeRaw .uint16 uint16ResultLocal }

def functions : Array Function := #[
  shiftRightFunction,
  ofNatFunction,
  toUInt8Function,
  landFunction,
  xorFunction]

private def expectedSignature? (declaration : Name) : Option Signature :=
  if declaration == `UInt16.shiftRight || declaration == `UInt16.land ||
      declaration == `UInt16.xor then
    some { params := #[.uint16, .uint16], results := #[.uint16] }
  else if declaration == `UInt16.ofNat then
    some { params := #[.tobject], results := #[.uint16] }
  else if declaration == `UInt16.toUInt8 then
    some { params := #[.uint16], results := #[.uint8] }
  else none

private partial def rewriteInstruction (declarations : Array Name) :
    Instruction → Instruction
  | .call (.declaration declaration) =>
      if declarations.contains declaration then
        .call (.declaration (externalName declaration))
      else .call (.declaration declaration)
  | .block label body => .block label (body.map (rewriteInstruction declarations))
  | .loop label body => .loop label (body.map (rewriteInstruction declarations))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteInstruction declarations))
        (elseBody.map (rewriteInstruction declarations))
  | instruction => instruction

private def internalizeSelected (module : Module) (declarations : Array Name) :
    Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  if declarations.contains `UInt16.ofNat then
    for name in #[ResidentNumeric.validateNaturalName,
        ResidentNumeric.naturalLowName] do
      unless module.functions.any (·.name == name) do
        throw (.missingNumericHelper name)
  let selectedHelperNames := declarations.map externalName
  for name in selectedHelperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) || module.exports.contains name then
      throw (.reservedDeclaration name)
  for declaration in declarations do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.missingExternal declaration)
    let some signature := expectedSignature? declaration |
      throw (.incompatibleExternal declaration)
    unless imports[0]!.signature == signature do
      throw (.incompatibleExternal declaration)
  let linkedFunctions := module.functions.map fun function =>
    { function with body := function.body.map (rewriteInstruction declarations) }
  let linkedFunctions := linkedFunctions ++ functions.filter fun function =>
    selectedHelperNames.contains function.name
  let imports := module.imports.filter fun import_ =>
    match import_.declaration? with
    | some declaration => !declarations.contains declaration
    | none => true
  let result : Module := {
    module with
    functions := linkedFunctions
    imports
    exports := selectedHelperNames.foldl Fir.Wasm.addUnique module.exports
    runtimeOperations := Fir.Wasm.collectRuntimeOps linkedFunctions }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

/-- Internalize exactly the supported fixed-width operations present. -/
def internalizeAvailable (module : Module) : Except LinkError Module :=
  let declarations := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
  if declarations.isEmpty then pure module else internalizeSelected module declarations

private def externalTypes (declaration : Name) : ExternalTypes :=
  if declaration == `UInt16.ofNat then
    { params := #[LCNF.ImpureType.tobject], result := LCNF.ImpureType.uint16 }
  else if declaration == `UInt16.toUInt8 then
    { params := #[LCNF.ImpureType.uint16], result := LCNF.ImpureType.uint8 }
  else
    { params := #[LCNF.ImpureType.uint16, LCNF.ImpureType.uint16],
      result := LCNF.ImpureType.uint16 }

private def externalImport (declaration : Name) : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := (expectedSignature? declaration).get!
  externalTypes? := some (externalTypes declaration) }

def residentExampleModule : Except String Module := do
  let numeric ← ResidentNumeric.residentExampleModule
  let module : Module := {
    numeric with
    imports := numeric.imports ++ externalDeclarations.map externalImport }
  internalizeSelected module externalDeclarations
    |>.mapError fun error => s!"fixed-width: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <| externalDeclarations.map fun declaration =>
      Json.mkObj [
        ("sourceEntry", declaration.toString),
        ("entry", externalName declaration |>.toString)]),
    ("imports", Json.arr #[]),
    ("status", "generation-ready; W6 fixed-width contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      externalDeclarations.all fun declaration =>
        module.exports.contains (externalName declaration) &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentFixedWidth
