import Fir.Wasm.Emit.ResidentBigNumeric

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
def log2Declaration : Name := `Nat.log2
def log2HelperName : Name := `fir_ext_Nat_log2

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
private def limbCountLocal : FVarId := ⟨`limbCount⟩
private def limbIndexLocal : FVarId := ⟨`limbIndex⟩
private def wordLocal : FVarId := ⟨`word⟩
private def bitCountLocal : FVarId := ⟨`bitCount⟩
private def result64Local : FVarId := ⟨`result64⟩
private def log2Loop : FVarId := ⟨`natLog2Loop⟩

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

/-- Exact floor-log2 over the arbitrary-limb resident Natural layout. -/
def log2Function : Function := {
  name := log2HelperName
  params := #[(valueParam, .tobject)]
  results := #[.tobject]
  locals := #[(limbCountLocal, .uint32), (limbIndexLocal, .uint32),
    (wordLocal, .uint32), (bitCountLocal, .uint32),
    (result64Local, .uint64), (resultLowLocal, .uint32),
    (resultHighLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (resultLocal, .tobject)]
  body := [
    .localGet valueParam,
    .call (.declaration ResidentBigNumeric.validateNaturalName),
    .localGet valueParam,
    .call (.declaration ResidentBigNumeric.naturalCountName),
    .localSet limbCountLocal,
    .localGet limbCountLocal,
    .i32Const .uint32 1,
    .i32Sub,
    .localSet limbIndexLocal,
    .localGet valueParam,
    .localGet limbIndexLocal,
    .call (.declaration ResidentBigNumeric.naturalHighName),
    .localSet wordLocal,
    .localGet wordLocal,
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse [
      .localGet valueParam,
      .localGet limbIndexLocal,
      .call (.declaration ResidentBigNumeric.naturalLowName),
      .localSet wordLocal,
      .i32Const .uint32 0,
      .localSet bitCountLocal] [
      .i32Const .uint32 32,
      .localSet bitCountLocal],
    .loop log2Loop [
      .localGet wordLocal,
      .i32Const .uint32 2,
      .i32LtU,
      .ifElse [] [
        .localGet wordLocal,
        .i32Const .uint32 1,
        .i32ShrU,
        .localSet wordLocal,
        .localGet bitCountLocal,
        .i32Const .uint32 1,
        .i32Add,
        .localSet bitCountLocal,
        .br log2Loop]],
    .localGet limbIndexLocal,
    .i64ExtendI32U .uint64,
    .i64Const .uint64 6,
    .i64Shl,
    .localGet bitCountLocal,
    .i64ExtendI32U .uint64,
    .i64Or,
    .localSet result64Local,
    .localGet result64Local,
    .i32WrapI64 .uint32,
    .localSet resultLowLocal,
    .localGet result64Local,
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
      else if candidate == log2Declaration then .call (.declaration log2HelperName)
      else .call (.declaration candidate)
  | .block label body => .block label (body.map rewriteInstruction)
  | .loop label body => .loop label (body.map rewriteInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map rewriteInstruction) (elseBody.map rewriteInstruction)
  | instruction => instruction

/-- Internalize the available generic Nat bit-position operations. -/
def internalizeAvailable (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let needsShiftRight := module.imports.any (·.declaration? == some declaration)
  let needsLog2 := module.imports.any (·.declaration? == some log2Declaration)
  if !needsShiftRight && !needsLog2 then
    return module
  let numericHelpers :=
    (if needsShiftRight then #[ResidentNumeric.validateNaturalName,
      ResidentNumeric.naturalLowName, ResidentNumeric.naturalHighName] else #[]) ++
    (if needsLog2 then #[ResidentBigNumeric.validateNaturalName,
      ResidentBigNumeric.naturalCountName, ResidentBigNumeric.naturalLowName,
      ResidentBigNumeric.naturalHighName] else #[]) ++
    #[ResidentNumeric.makeNaturalName]
  for name in numericHelpers do
    unless module.functions.any (·.name == name) do
      throw (.missingNumericHelper name)
  for name in (if needsShiftRight then #[helperName] else #[]) ++
      (if needsLog2 then #[log2HelperName] else #[]) do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) || module.exports.contains name then
      throw .reservedDeclaration
  if needsShiftRight then
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw .missingExternal
    unless imports[0]!.signature == {
        params := #[.tobject, .tobject], results := #[.tobject] } do
      throw .incompatibleExternal
  if needsLog2 then
    let imports := module.imports.filter (·.declaration? == some log2Declaration)
    unless imports.size == 1 do
      throw .missingExternal
    unless imports[0]!.signature == {
        params := #[.tobject], results := #[.tobject] } do
      throw .incompatibleExternal
  let linkedFunctions := module.functions.map fun candidate =>
    { candidate with body := candidate.body.map rewriteInstruction }
  let functions := if needsShiftRight then linkedFunctions.push function
    else linkedFunctions
  let functions := if needsLog2 then functions.push log2Function else functions
  let exports := if needsShiftRight then
    Fir.Wasm.addUnique module.exports helperName
  else module.exports
  let exports := if needsLog2 then Fir.Wasm.addUnique exports log2HelperName
    else exports
  let result : Module := {
    module with
    imports := module.imports.filter fun import_ =>
      (!needsShiftRight || import_.declaration? != some declaration) &&
        (!needsLog2 || import_.declaration? != some log2Declaration)
    functions
    exports
    runtimeOperations := Fir.Wasm.collectRuntimeOps functions }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

end Fir.Wasm.Emit.ResidentNatShift
