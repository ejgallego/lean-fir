import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentNatShift

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

/-!
# Wasm-resident bounded `Nat.shiftRight`

The existing W7 numeric runtime represents up to one 64-bit limb. This helper is
exact on that resident numeric domain, including Lean's zero result when the
shift count is at least 64; wider numeric objects retain the existing explicit
trap policy.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingNumericHelper (name : Name)
  | reservedDeclaration
  | missingExternal
  | incompatibleExternal
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

def declaration : Name := `Nat.shiftRight
def helperName : Name := `fir_ext_Nat_shiftRight

private def valueParam : FVarId := ⟨`value⟩
private def countParam : FVarId := ⟨`count⟩
private def valueLowLocal : FVarId := ⟨`valueLow⟩
private def valueHighLocal : FVarId := ⟨`valueHigh⟩
private def countLowLocal : FVarId := ⟨`countLow⟩
private def countHighLocal : FVarId := ⟨`countHigh⟩
private def shiftedLocal : FVarId := ⟨`shifted⟩
private def resultLowLocal : FVarId := ⟨`resultLow⟩
private def resultHighLocal : FVarId := ⟨`resultHigh⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def resultLocal : FVarId := ⟨`result⟩

private def retypeNatural : List Instruction := [
  .localSet rawLocal,
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet rawLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .tobject 0,
  .localSet resultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet resultLocal,
  .ret]

private def shiftBody : List Instruction := [
  .localGet countHighLocal,
  .i32Const .uint32 0,
  .i32Eq,
  .ifElse
    [.localGet countLowLocal,
      .i32Const .uint32 64,
      .i32LtU,
      .ifElse
        [.localGet valueHighLocal,
          .i64ExtendI32U .uint64,
          .i64Const .uint64 32,
          .i64Shl,
          .localGet valueLowLocal,
          .i64ExtendI32U .uint64,
          .i64Or,
          .localGet countLowLocal,
          .i64ExtendI32U .uint64,
          .i64ShrU,
          .localSet shiftedLocal]
        [.i64Const .uint64 0, .localSet shiftedLocal]]
    [.i64Const .uint64 0, .localSet shiftedLocal]]

def function : Function := {
  name := helperName
  params := #[(valueParam, .tobject), (countParam, .tobject)]
  results := #[.tobject]
  locals := #[(valueLowLocal, .uint32), (valueHighLocal, .uint32),
    (countLowLocal, .uint32), (countHighLocal, .uint32),
    (shiftedLocal, .uint64), (resultLowLocal, .uint32),
    (resultHighLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (resultLocal, .tobject)]
  body := [
    .localGet valueParam,
    .call (.declaration ResidentNumeric.validateNaturalName),
    .localGet countParam,
    .call (.declaration ResidentNumeric.validateNaturalName),
    .localGet valueParam,
    .call (.declaration ResidentNumeric.naturalLowName),
    .localSet valueLowLocal,
    .localGet valueParam,
    .call (.declaration ResidentNumeric.naturalHighName),
    .localSet valueHighLocal,
    .localGet countParam,
    .call (.declaration ResidentNumeric.naturalLowName),
    .localSet countLowLocal,
    .localGet countParam,
    .call (.declaration ResidentNumeric.naturalHighName),
    .localSet countHighLocal] ++ shiftBody ++ [
    .localGet shiftedLocal,
    .i32WrapI64 .uint32,
    .localSet resultLowLocal,
    .localGet shiftedLocal,
    .i64Const .uint64 32,
    .i64ShrU,
    .i32WrapI64 .uint32,
    .localSet resultHighLocal,
    .localGet resultLowLocal,
    .localGet resultHighLocal,
    .call (.declaration ResidentNumeric.makeNaturalName)] ++ retypeNatural }

private partial def rewriteInstruction : Instruction → Instruction
  | .call (.declaration candidate) =>
      if candidate == declaration then .call (.declaration helperName)
      else .call (.declaration candidate)
  | .block label body => .block label (body.map rewriteInstruction)
  | .loop label body => .loop label (body.map rewriteInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map rewriteInstruction) (elseBody.map rewriteInstruction)
  | instruction => instruction

/-- Internalize `Nat.shiftRight` when the captured source closure imports it. -/
def internalizeAvailable (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  if !module.imports.any (·.declaration? == some declaration) then
    return module
  for name in #[ResidentNumeric.validateNaturalName,
      ResidentNumeric.naturalLowName, ResidentNumeric.naturalHighName,
      ResidentNumeric.makeNaturalName] do
    unless module.functions.any (·.name == name) do
      throw (.missingNumericHelper name)
  if module.imports.any (·.declaration? == some helperName) ||
      module.functions.any (·.name == helperName) || module.exports.contains helperName then
    throw .reservedDeclaration
  let imports := module.imports.filter (·.declaration? == some declaration)
  unless imports.size == 1 do
    throw .missingExternal
  unless imports[0]!.signature == {
      params := #[.tobject, .tobject], results := #[.tobject] } do
    throw .incompatibleExternal
  let linkedFunctions := module.functions.map fun candidate =>
    { candidate with body := candidate.body.map rewriteInstruction }
  let functions := linkedFunctions.push function
  let result : Module := {
    module with
    imports := module.imports.filter (·.declaration? != some declaration)
    functions
    exports := Fir.Wasm.addUnique module.exports helperName
    runtimeOperations := Fir.Wasm.collectRuntimeOps functions }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

end Fir.Wasm.Emit.ResidentNatShift
