import Fir.Wasm.Emit.ResidentString

namespace Fir.Wasm.Emit.ResidentHash

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean
open Lean.Compiler

/-!
# Wasm-resident Lean hashing primitives

These helpers mirror Lean's runtime `lean_uint64_mix_hash` and
`lean_string_hash` implementations.  The latter is MurmurHash64A over the
exact UTF-8 bytes with seed 11.  Structured loops keep the Wasm stack bounded
independently of string length.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingStringHelper (name : Name)
  | reservedDeclaration (name : Name)
  | incompatibleExternal (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

def externalDeclarations : Array Name := #[`String.hash, `mixHash]

def externalName (declaration : Name) : Name :=
  ResidentNumeric.externalName declaration

def helperNames : Array Name := externalDeclarations.map externalName

private def sourceParam : FVarId := ⟨`source⟩
private def hashParam : FVarId := ⟨`hash⟩
private def keyParam : FVarId := ⟨`key⟩
private def lengthLocal : FVarId := ⟨`length⟩
private def indexLocal : FVarId := ⟨`index⟩
private def remainingLocal : FVarId := ⟨`remaining⟩
private def shiftLocal : FVarId := ⟨`shift⟩
private def hashLocal : FVarId := ⟨`hashValue⟩
private def keyLocal : FVarId := ⟨`keyValue⟩
private def byteLocal : FVarId := ⟨`byteValue⟩
private def blockLoop : FVarId := ⟨`stringHashBlockLoop⟩
private def tailLoop : FVarId := ⟨`stringHashTailLoop⟩

private def murmurMultiplier : UInt64 := 0xc6a4a7935bd1e995

private def mixKey (key : FVarId) : List Instruction := [
  .localGet key,
  .i64Const .uint64 murmurMultiplier,
  .i64Mul,
  .localSet key,
  .localGet key,
  .localGet key,
  .i64Const .uint64 47,
  .i64ShrU,
  .i64Xor,
  .localSet key]

def mixHashFunction : Function := {
  name := externalName `mixHash
  params := #[(hashParam, .uint64), (keyParam, .uint64)]
  results := #[.uint64]
  locals := #[(hashLocal, .uint64), (keyLocal, .uint64)]
  body := [
    .localGet hashParam,
    .localSet hashLocal,
    .localGet keyParam,
    .localSet keyLocal] ++
    mixKey keyLocal ++ [
    .localGet keyLocal,
    .i64Const .uint64 murmurMultiplier,
    .i64Xor,
    .localSet keyLocal,
    .localGet hashLocal,
    .localGet keyLocal,
    .i64Xor,
    .i64Const .uint64 murmurMultiplier,
    .i64Mul,
    .ret] }

private def finishHash : List Instruction := [
  .localGet hashLocal,
  .localGet hashLocal,
  .i64Const .uint64 47,
  .i64ShrU,
  .i64Xor,
  .i64Const .uint64 murmurMultiplier,
  .i64Mul,
  .localSet hashLocal,
  .localGet hashLocal,
  .localGet hashLocal,
  .i64Const .uint64 47,
  .i64ShrU,
  .i64Xor,
  .ret]

private def hashTail : List Instruction := [
  .i64Const .uint64 0,
  .localSet shiftLocal,
  .loop tailLoop [
    .localGet indexLocal,
    .localGet lengthLocal,
    .i32Eq,
    .ifElse
      ([.localGet hashLocal,
        .i64Const .uint64 murmurMultiplier,
        .i64Mul,
        .localSet hashLocal] ++ finishHash)
      [],
    .localGet sourceParam,
    .localGet indexLocal,
    .i32Add,
    .i64Load8U .uint64 (u32 headerBytes),
    .localGet shiftLocal,
    .i64Shl,
    .localSet byteLocal,
    .localGet hashLocal,
    .localGet byteLocal,
    .i64Xor,
    .localSet hashLocal,
    .localGet indexLocal,
    .i32Const .uint32 1,
    .i32Add,
    .localSet indexLocal,
    .localGet shiftLocal,
    .i64Const .uint64 8,
    .i64Add,
    .localSet shiftLocal,
    .br tailLoop]]

def stringHashFunction : Function := {
  name := externalName `String.hash
  params := #[(sourceParam, .object)]
  results := #[.uint64]
  locals := #[(lengthLocal, .uint32), (indexLocal, .uint32),
    (remainingLocal, .uint32), (shiftLocal, .uint64),
    (hashLocal, .uint64), (keyLocal, .uint64), (byteLocal, .uint64)]
  body := [
    .localGet sourceParam,
    .call (.declaration ResidentString.validateName),
    .localGet sourceParam,
    .call (.declaration ResidentString.byteLengthName),
    .localSet lengthLocal,
    .i64Const .uint64 11,
    .localGet lengthLocal,
    .i64ExtendI32U .uint64,
    .i64Const .uint64 murmurMultiplier,
    .i64Mul,
    .i64Xor,
    .localSet hashLocal,
    .i32Const .uint32 0,
    .localSet indexLocal] ++ [
    .loop blockLoop <| [
      .localGet lengthLocal,
      .localGet indexLocal,
      .i32Sub,
      .localSet remainingLocal,
      .localGet remainingLocal,
      .i32Const .uint32 8,
      .i32LtU,
      .ifElse
        ([.localGet remainingLocal,
          .i32Eqz,
          .ifElse finishHash hashTail])
        [],
      .localGet sourceParam,
      .localGet indexLocal,
      .i32Add,
      .i64Load .uint64 (u32 headerBytes),
      .localSet keyLocal] ++
      mixKey keyLocal ++ [
      .localGet keyLocal,
      .i64Const .uint64 murmurMultiplier,
      .i64Mul,
      .localSet keyLocal,
      .localGet hashLocal,
      .localGet keyLocal,
      .i64Xor,
      .i64Const .uint64 murmurMultiplier,
      .i64Mul,
      .localSet hashLocal,
      .localGet indexLocal,
      .i32Const .uint32 8,
      .i32Add,
      .localSet indexLocal,
      .br blockLoop]] }

def functions : Array Function := #[stringHashFunction, mixHashFunction]

private def expectedSignature? (declaration : Name) : Option Signature :=
  if declaration == `String.hash then
    some { params := #[.object], results := #[.uint64] }
  else if declaration == `mixHash then
    some { params := #[.uint64, .uint64], results := #[.uint64] }
  else none

private def functionSignature (function : Function) : Signature := {
  params := function.params.map (·.2)
  results := function.results }

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

def internalizeAvailable (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let declarations := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
  if declarations.isEmpty then return module
  if declarations.contains `String.hash then
    for name in #[ResidentString.validateName, ResidentString.byteLengthName] do
      unless module.functions.any (·.name == name) do
        throw (.missingStringHelper name)
  for declaration in declarations do
    let imports := module.imports.filter (·.declaration? == some declaration)
    let some expected := expectedSignature? declaration |
      throw (.incompatibleExternal declaration)
    let some helper := functions.find? (·.name == externalName declaration) |
      throw (.incompatibleExternal declaration)
    unless imports.size == 1 && imports[0]!.signature == expected &&
        functionSignature helper == expected do
      throw (.incompatibleExternal declaration)
    if module.functions.any (·.name == helper.name) ||
        module.exports.contains helper.name then
      throw (.reservedDeclaration helper.name)
  let selectedNames := declarations.map externalName
  let linkedFunctions :=
    (module.functions.map fun function =>
      { function with body := function.body.map (rewriteInstruction declarations) }) ++
    functions.filter fun function => selectedNames.contains function.name
  let result : Module := {
    module with
    imports := module.imports.filter fun import_ =>
      match import_.declaration? with
      | some declaration => !declarations.contains declaration
      | none => true
    functions := linkedFunctions
    exports := selectedNames.foldl Fir.Wasm.addUnique module.exports
    runtimeOperations := Fir.Wasm.collectRuntimeOps linkedFunctions }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

private def externalTypes? (declaration : Name) : Option ExternalTypes :=
  let object := LCNF.ImpureType.object
  let uint64 := LCNF.ImpureType.uint64
  if declaration == `String.hash then
    some { params := #[object], result := uint64 }
  else
    some { params := #[uint64, uint64], result := uint64 }

private def exampleImport (declaration : Name) : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := (expectedSignature? declaration).get!
  externalTypes? := externalTypes? declaration }

def residentExampleModule : Except String Module := do
  let module ← ResidentString.residentExampleModule
  let module := { module with
    imports := module.imports ++ externalDeclarations.map exampleImport }
  internalizeAvailable module |>.mapError fun error => s!"hash: {repr error}"

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      helperNames.all module.exports.contains &&
      (Fir.Wasm.validateModule module).isOk &&
      (Fir.Wasm.Emit.encode module).isOk
  | .error _ => false

end Fir.Wasm.Emit.ResidentHash
