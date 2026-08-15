import Fir.Wasm.Emit.ResidentBigNumeric

namespace Fir.Wasm.Emit.ResidentNatShift

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

/-!
# Wasm-resident `Nat.shiftRight`

The shift helper operates on the canonical arbitrary-limb resident Natural
layout. Counts beyond the addressable operand extent return zero, matching
Lean's unbounded-Nat semantics without narrowing either operand to `u64`.
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

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

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
private def countLocal : FVarId := ⟨`countValue⟩
private def limbIndexLocal : FVarId := ⟨`limbIndex⟩
private def wordLocal : FVarId := ⟨`word⟩
private def bitCountLocal : FVarId := ⟨`bitCount⟩
private def result64Local : FVarId := ⟨`result64⟩
private def value64Local : FVarId := ⟨`value64⟩
private def next64Local : FVarId := ⟨`next64⟩
private def wholeLowLocal : FVarId := ⟨`wholeLow⟩
private def wholeHighLocal : FVarId := ⟨`wholeHigh⟩
private def resultCountLocal : FVarId := ⟨`resultCount⟩
private def resultIndexLocal : FVarId := ⟨`resultIndex⟩
private def sourceIndexLocal : FVarId := ⟨`sourceIndex⟩
private def scaledLocal : FVarId := ⟨`scaled⟩
private def log2Loop : FVarId := ⟨`natLog2Loop⟩
private def shiftWriteLoop : FVarId := ⟨`natShiftRightWriteLoop⟩

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

private def scale8 (source destination : FVarId) : List Instruction := [
  .localGet source,
  .localGet source,
  .i32Add,
  .localSet destination,
  .localGet destination,
  .localGet destination,
  .i32Add,
  .localSet destination,
  .localGet destination,
  .localGet destination,
  .i32Add,
  .localSet destination]

private def loadLimb64 (index destination : FVarId) : List Instruction := [
  .localGet valueParam,
  .localGet index,
  .call (.declaration ResidentBigNumeric.naturalHighName),
  .i64ExtendI32U .uint64,
  .i64Const .uint64 32,
  .i64Shl,
  .localGet valueParam,
  .localGet index,
  .call (.declaration ResidentBigNumeric.naturalLowName),
  .i64ExtendI32U .uint64,
  .i64Or,
  .localSet destination]

private def computeShiftedLimb : List Instruction := [
  .localGet resultIndexLocal,
  .localGet wholeLowLocal,
  .i32Add,
  .localSet sourceIndexLocal] ++
  loadLimb64 sourceIndexLocal value64Local ++ [
  .localGet countLowLocal,
  .i32Const .uint32 63,
  .i32And,
  .localSet bitCountLocal,
  .localGet bitCountLocal,
  .i32Eqz,
  .ifElse
    [.localGet value64Local, .localSet shiftedLocal]
    ([.i64Const .uint64 0, .localSet next64Local,
      .localGet sourceIndexLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet sourceIndexLocal,
      .localGet sourceIndexLocal,
      .localGet limbCountLocal,
      .i32LtU,
      .ifElse
        (loadLimb64 sourceIndexLocal next64Local)
        [],
      .localGet value64Local,
      .localGet bitCountLocal,
      .i64ExtendI32U .uint64,
      .i64ShrU,
      .localGet next64Local,
      .i32Const .uint32 64,
      .localGet bitCountLocal,
      .i32Sub,
      .i64ExtendI32U .uint64,
      .i64Shl,
      .i64Or,
      .localSet shiftedLocal])]

private def storeShiftedLimb : List Instruction :=
  scale8 resultIndexLocal scaledLocal ++ [
    .localGet rawLocal,
    .i32Const .uint32 (u32 headerBytes),
    .i32Add,
    .localGet scaledLocal,
    .i32Add,
    .localGet shiftedLocal,
    .i32WrapI64 .uint32,
    .i32Store .uint32 0,
    .localGet rawLocal,
    .i32Const .uint32 (u32 headerBytes),
    .i32Add,
    .localGet scaledLocal,
    .i32Add,
    .localGet shiftedLocal,
    .i64Const .uint64 32,
    .i64ShrU,
    .i32WrapI64 .uint32,
    .i32Store .uint32 4]

private def returnZero : List Instruction := [
  .i32Const .tobject 1,
  .ret]

private def finishShift : List Instruction := [
  .localGet limbCountLocal,
  .localGet wholeLowLocal,
  .i32Sub,
  .localSet resultCountLocal,
  .localGet resultCountLocal,
  .i32Const .uint32 1,
  .i32Sub,
  .localSet resultIndexLocal] ++ computeShiftedLimb ++ [
  .localGet shiftedLocal,
  .i64Eqz,
  .ifElse [
    .localGet resultCountLocal,
    .i32Const .uint32 1,
    .i32Sub,
    .localSet resultCountLocal] [],
  .localGet resultCountLocal,
  .i32Eqz,
  .ifElse returnZero [],
  .localGet resultCountLocal,
  .i32Const .uint32 1,
  .i32Eq,
  .ifElse
    ([.i32Const .uint32 0, .localSet resultIndexLocal] ++
      computeShiftedLimb ++ [
      .localGet shiftedLocal,
      .i32WrapI64 .uint32,
      .localGet shiftedLocal,
      .i64Const .uint64 32,
      .i64ShrU,
      .i32WrapI64 .uint32,
      .call (.declaration ResidentNumeric.makeNaturalName)] ++ retypeNatural)
    [],
  .i32Const .uint32 ObjectKind.natural.code,
  .i32Const .uint32 bigNaturalMarker,
  .i32Const .uint32 0,
  .localGet resultCountLocal,
  .call (.declaration ResidentBigNumeric.allocateName),
  .localSet rawLocal,
  .i32Const .uint32 0,
  .localSet resultIndexLocal,
  .loop shiftWriteLoop ([
    .localGet resultIndexLocal,
    .localGet resultCountLocal,
    .i32Eq,
    .ifElse ([.localGet rawLocal] ++ retypeNatural) []] ++
    computeShiftedLimb ++ storeShiftedLimb ++ [
    .localGet resultIndexLocal,
    .i32Const .uint32 1,
    .i32Add,
    .localSet resultIndexLocal,
    .br shiftWriteLoop])]

def function : Function := {
  name := helperName
  params := #[(valueParam, .tobject), (countParam, .tobject)]
  results := #[.tobject]
  locals := #[(countLowLocal, .uint32), (countHighLocal, .uint32),
    (shiftedLocal, .uint64), (resultLowLocal, .uint32),
    (resultHighLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (resultLocal, .tobject),
    (limbCountLocal, .uint32), (countLocal, .uint32),
    (wholeLowLocal, .uint32), (wholeHighLocal, .uint32),
    (bitCountLocal, .uint32), (resultCountLocal, .uint32),
    (resultIndexLocal, .uint32), (sourceIndexLocal, .uint32),
    (scaledLocal, .uint32), (value64Local, .uint64),
    (next64Local, .uint64)]
  body := [
    .localGet valueParam,
    .call (.declaration ResidentBigNumeric.validateNaturalName),
    .localGet countParam,
    .call (.declaration ResidentBigNumeric.validateNaturalName),
    .localGet valueParam,
    .call (.declaration ResidentBigNumeric.naturalCountName),
    .localSet limbCountLocal,
    .localGet countParam,
    .call (.declaration ResidentBigNumeric.naturalCountName),
    .localSet countLocal,
    .localGet countLocal,
    .i32Const .uint32 1,
    .i32GtU,
    .ifElse returnZero [],
    .localGet countParam,
    .i32Const .uint32 0,
    .call (.declaration ResidentBigNumeric.naturalLowName),
    .localSet countLowLocal,
    .localGet countParam,
    .i32Const .uint32 0,
    .call (.declaration ResidentBigNumeric.naturalHighName),
    .localSet countHighLocal,
    .localGet countHighLocal,
    .i32Const .uint32 6,
    .i32ShrU,
    .localSet wholeHighLocal,
    .localGet countLowLocal,
    .i32Const .uint32 6,
    .i32ShrU,
    .localGet countHighLocal,
    .i32Const .uint32 26,
    .i32Shl,
    .i32Or,
    .localSet wholeLowLocal,
    .localGet wholeHighLocal,
    .i32Eqz,
    .ifElse [] returnZero,
    .localGet wholeLowLocal,
    .localGet limbCountLocal,
    .i32GeU,
    .ifElse returnZero []] ++ finishShift }

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
    (if needsShiftRight then #[ResidentBigNumeric.validateNaturalName,
      ResidentBigNumeric.naturalCountName, ResidentBigNumeric.naturalLowName,
      ResidentBigNumeric.naturalHighName, ResidentBigNumeric.allocateName] else #[]) ++
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
