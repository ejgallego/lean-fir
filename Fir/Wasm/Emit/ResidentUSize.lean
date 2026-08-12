import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentUSize

open Fir.Wasm
open Lean

/-!
# Wasm-resident `USize` operations

Final LCNF generated for `Array.forIn'Unsafe` keeps its cursor and bound in
native `USize` lanes. These helpers implement the generic scalar frontier over
wasm64 values. Arithmetic is assembled from accepted wasm32/wasm64 operations
so it retains `USize`'s modulo-2^64 behavior without extending FIR's shared
symbolic instruction surface.
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

def externalDeclarations : Array Name := #[
  `USize.decLt,
  `USize.add,
  `USize.sub,
  `USize.ofNat,
  `USize.toUInt32,
  `USize.toNat,
  `USize.land,
  `USize.shiftLeft,
  `USize.decLe,
  `USize.decEq,
  `USize.complement,
  `USize.shiftRight,
  `USize.mod,
  `USize.ofNatLT]

def externalName (declaration : Name) : Name :=
  Name.mkSimple s!"fir_ext_{declaration.toString.replace "." "_"}"

def helperNames : Array Name := externalDeclarations.map externalName

private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def leftLowLocal : FVarId := ⟨`leftLow⟩
private def leftHighLocal : FVarId := ⟨`leftHigh⟩
private def rightLowLocal : FVarId := ⟨`rightLow⟩
private def rightHighLocal : FVarId := ⟨`rightHigh⟩
private def lowLocal : FVarId := ⟨`low⟩
private def highLocal : FVarId := ⟨`high⟩
private def carryLocal : FVarId := ⟨`carry⟩
private def raw32Local : FVarId := ⟨`raw32⟩
private def raw64Local : FVarId := ⟨`raw64⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def uint8ResultLocal : FVarId := ⟨`uint8Result⟩
private def usizeResultLocal : FVarId := ⟨`usizeResult⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def valueParam : FVarId := ⟨`value⟩
private def erasedParam : FVarId := ⟨`erased⟩
private def borrowLocal : FVarId := ⟨`borrow⟩
private def indexLocal : FVarId := ⟨`index⟩
private def remainderLocal : FVarId := ⟨`remainder⟩
private def remainderLowLocal : FVarId := ⟨`remainderLow⟩
private def remainderHighLocal : FVarId := ⟨`remainderHigh⟩
private def modLoop : FVarId := ⟨`usizeModLoop⟩

private def retypeUInt8 : List Instruction := [
  .i32Const .uint32 0,
  .i64Load .uint64 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet raw32Local,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .uint8 0,
  .localSet uint8ResultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i64Store .uint64 0,
  .localGet uint8ResultLocal,
  .ret]

private def retypeUSize : List Instruction := [
  .localSet raw64Local,
  .i32Const .uint32 0,
  .i64Load .uint64 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet raw64Local,
  .i64Store .uint64 0,
  .i32Const .uint32 0,
  .i64Load .usize 0,
  .localSet usizeResultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i64Store .uint64 0,
  .localGet usizeResultLocal,
  .ret]

private def retypeUInt32 : List Instruction := [
  .localSet raw32Local,
  .i32Const .uint32 0,
  .i64Load .uint64 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet raw32Local,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet raw32Local,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i64Store .uint64 0,
  .localGet raw32Local,
  .ret]

private def retypeObject : List Instruction := [
  .localSet raw32Local,
  .i32Const .uint32 0,
  .i64Load .uint64 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet raw32Local,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .tobject 0,
  .localSet objectResultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i64Store .uint64 0,
  .localGet objectResultLocal,
  .ret]

private def splitUSize (source low high : FVarId) : List Instruction := [
  .localGet source,
  .i32WrapI64 .uint32,
  .localSet low,
  .localGet source,
  .i64Const .uint64 32,
  .i64ShrU,
  .i32WrapI64 .uint32,
  .localSet high]

private def combineUSize (low high : FVarId) : List Instruction := [
  .localGet high,
  .i64ExtendI32U .uint64,
  .i64Const .uint64 32,
  .i64Shl,
  .localGet low,
  .i64ExtendI32U .uint64,
  .i64Or]

def decLtFunction : Function := {
  name := externalName `USize.decLt
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.uint8]
  locals := #[(raw32Local, .uint32), (savedScratchLocal, .uint64),
    (uint8ResultLocal, .uint8)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i64LtU,
    .localSet raw32Local] ++ retypeUInt8 }

def addFunction : Function := {
  name := externalName `USize.add
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.usize]
  locals := #[(leftLowLocal, .uint32), (leftHighLocal, .uint32),
    (rightLowLocal, .uint32), (rightHighLocal, .uint32),
    (lowLocal, .uint32), (highLocal, .uint32), (carryLocal, .uint32),
    (raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := [
    .localGet leftParam,
    .i32WrapI64 .uint32,
    .localSet leftLowLocal,
    .localGet leftParam,
    .i64Const .uint64 32,
    .i64ShrU,
    .i32WrapI64 .uint32,
    .localSet leftHighLocal,
    .localGet rightParam,
    .i32WrapI64 .uint32,
    .localSet rightLowLocal,
    .localGet rightParam,
    .i64Const .uint64 32,
    .i64ShrU,
    .i32WrapI64 .uint32,
    .localSet rightHighLocal,
    .localGet leftLowLocal,
    .localGet rightLowLocal,
    .i32Add,
    .localSet lowLocal,
    .localGet lowLocal,
    .localGet leftLowLocal,
    .i32LtU,
    .localSet carryLocal,
    .localGet leftHighLocal,
    .localGet rightHighLocal,
    .i32Add,
    .localGet carryLocal,
    .i32Add,
    .localSet highLocal,
    .localGet highLocal,
    .i64ExtendI32U .uint64,
    .i64Const .uint64 32,
    .i64Shl,
    .localGet lowLocal,
    .i64ExtendI32U .uint64,
    .i64Or] ++ retypeUSize }

def subFunction : Function := {
  name := externalName `USize.sub
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.usize]
  locals := #[(leftLowLocal, .uint32), (leftHighLocal, .uint32),
    (rightLowLocal, .uint32), (rightHighLocal, .uint32),
    (lowLocal, .uint32), (highLocal, .uint32), (borrowLocal, .uint32),
    (raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := splitUSize leftParam leftLowLocal leftHighLocal ++
    splitUSize rightParam rightLowLocal rightHighLocal ++ [
      .localGet leftLowLocal,
      .localGet rightLowLocal,
      .i32Sub,
      .localSet lowLocal,
      .localGet leftLowLocal,
      .localGet rightLowLocal,
      .i32LtU,
      .localSet borrowLocal,
      .localGet leftHighLocal,
      .localGet rightHighLocal,
      .i32Sub,
      .localGet borrowLocal,
      .i32Sub,
      .localSet highLocal] ++ combineUSize lowLocal highLocal ++ retypeUSize }

private def ofNatBody : List Instruction := [
  .localGet valueParam,
  .call (.declaration ResidentNumeric.validateNaturalName),
  .localGet valueParam,
  .call (.declaration ResidentNumeric.naturalHighName),
  .i64ExtendI32U .uint64,
  .i64Const .uint64 32,
  .i64Shl,
  .localGet valueParam,
  .call (.declaration ResidentNumeric.naturalLowName),
  .i64ExtendI32U .uint64,
  .i64Or] ++ retypeUSize

def ofNatFunction : Function := {
  name := externalName `USize.ofNat
  params := #[(valueParam, .tobject)]
  results := #[.usize]
  locals := #[(raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := ofNatBody }

def ofNatLTFunction : Function := {
  name := externalName `USize.ofNatLT
  params := #[(valueParam, .tobject), (erasedParam, .erased)]
  results := #[.usize]
  locals := #[(raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := ofNatBody }

def toUInt32Function : Function := {
  name := externalName `USize.toUInt32
  params := #[(valueParam, .usize)]
  results := #[.uint32]
  locals := #[(raw32Local, .uint32), (savedScratchLocal, .uint64)]
  body := [
    .localGet valueParam,
    .i32WrapI64 .uint32] ++ retypeUInt32 }

def toNatFunction : Function := {
  name := externalName `USize.toNat
  params := #[(valueParam, .usize)]
  results := #[.tobject]
  locals := #[(lowLocal, .uint32), (highLocal, .uint32),
    (raw32Local, .uint32), (savedScratchLocal, .uint64),
    (objectResultLocal, .tobject)]
  body := splitUSize valueParam lowLocal highLocal ++ [
    .localGet lowLocal,
    .localGet highLocal,
    .call (.declaration ResidentNumeric.makeNaturalName)] ++ retypeObject }

def landFunction : Function := {
  name := externalName `USize.land
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.usize]
  locals := #[(leftLowLocal, .uint32), (leftHighLocal, .uint32),
    (rightLowLocal, .uint32), (rightHighLocal, .uint32),
    (lowLocal, .uint32), (highLocal, .uint32),
    (raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := splitUSize leftParam leftLowLocal leftHighLocal ++
    splitUSize rightParam rightLowLocal rightHighLocal ++ [
      .localGet leftLowLocal,
      .localGet rightLowLocal,
      .i32And,
      .localSet lowLocal,
      .localGet leftHighLocal,
      .localGet rightHighLocal,
      .i32And,
      .localSet highLocal] ++ combineUSize lowLocal highLocal ++ retypeUSize }

def shiftLeftFunction : Function := {
  name := externalName `USize.shiftLeft
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.usize]
  locals := #[(raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i64Shl] ++ retypeUSize }

def shiftRightFunction : Function := {
  name := externalName `USize.shiftRight
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.usize]
  locals := #[(raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i64ShrU] ++ retypeUSize }

def decLeFunction : Function := {
  name := externalName `USize.decLe
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.uint8]
  locals := #[(raw32Local, .uint32), (savedScratchLocal, .uint64),
    (uint8ResultLocal, .uint8)]
  body := [
    .localGet rightParam,
    .localGet leftParam,
    .i64LtU,
    .i32Const .uint32 0,
    .i32Eq,
    .localSet raw32Local] ++ retypeUInt8 }

def decEqFunction : Function := {
  name := externalName `USize.decEq
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.uint8]
  locals := #[(raw32Local, .uint32), (savedScratchLocal, .uint64),
    (uint8ResultLocal, .uint8)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i64LtU,
    .i32Const .uint32 0,
    .i32Eq,
    .localGet rightParam,
    .localGet leftParam,
    .i64LtU,
    .i32Const .uint32 0,
    .i32Eq,
    .i32And,
    .localSet raw32Local] ++ retypeUInt8 }

def complementFunction : Function := {
  name := externalName `USize.complement
  params := #[(valueParam, .usize)]
  results := #[.usize]
  locals := #[(lowLocal, .uint32), (highLocal, .uint32),
    (raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := splitUSize valueParam lowLocal highLocal ++ [
    .i32Const .uint32 0xffffffff,
    .localGet lowLocal,
    .i32Sub,
    .localSet lowLocal,
    .i32Const .uint32 0xffffffff,
    .localGet highLocal,
    .i32Sub,
    .localSet highLocal] ++ combineUSize lowLocal highLocal ++ retypeUSize }

private def modSubtractBody : List Instruction :=
  splitUSize remainderLocal remainderLowLocal remainderHighLocal ++
  splitUSize rightParam rightLowLocal rightHighLocal ++ [
    .localGet remainderLowLocal,
    .localGet rightLowLocal,
    .i32Sub,
    .localSet lowLocal,
    .localGet remainderLowLocal,
    .localGet rightLowLocal,
    .i32LtU,
    .localSet borrowLocal,
    .localGet remainderHighLocal,
    .localGet rightHighLocal,
    .i32Sub,
    .localGet borrowLocal,
    .i32Sub,
    .localSet highLocal] ++ combineUSize lowLocal highLocal ++ [
    .localSet remainderLocal]

def modFunction : Function := {
  name := externalName `USize.mod
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.usize]
  locals := #[(indexLocal, .uint32), (remainderLocal, .uint64),
    (remainderLowLocal, .uint32), (remainderHighLocal, .uint32),
    (rightLowLocal, .uint32), (rightHighLocal, .uint32),
    (lowLocal, .uint32), (highLocal, .uint32), (borrowLocal, .uint32),
    (raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := [
    .i32Const .uint32 0,
    .i64Load .uint64 0,
    .localSet savedScratchLocal,
    .i32Const .uint32 0,
    .localGet leftParam,
    .i64Store .usize 0,
    .i32Const .uint32 0,
    .i64Load .uint64 0,
    .localSet remainderLocal,
    .localGet rightParam,
    .i64Const .uint64 1,
    .i64LtU,
    .ifElse
      []
      [.i64Const .uint64 0,
        .localSet remainderLocal,
        .i32Const .uint32 64,
        .localSet indexLocal,
        .loop modLoop [
          .localGet indexLocal,
          .i32Const .uint32 1,
          .i32Sub,
          .localSet indexLocal,
          .localGet remainderLocal,
          .i64Const .uint64 1,
          .i64Shl,
          .localGet leftParam,
          .localGet indexLocal,
          .i64ExtendI32U .uint64,
          .i64ShrU,
          .i32WrapI64 .uint32,
          .i32Const .uint32 1,
          .i32And,
          .i64ExtendI32U .uint64,
          .i64Or,
          .localSet remainderLocal,
          .localGet remainderLocal,
          .localGet rightParam,
          .i64LtU,
          .i32Const .uint32 0,
          .i32Eq,
          .ifElse modSubtractBody [],
          .localGet indexLocal,
          .i32Const .uint32 0,
          .i32Eq,
          .ifElse [] [.br modLoop]]],
    .i32Const .uint32 0,
    .localGet remainderLocal,
    .i64Store .uint64 0,
    .i32Const .uint32 0,
    .i64Load .usize 0,
    .localSet usizeResultLocal,
    .i32Const .uint32 0,
    .localGet savedScratchLocal,
    .i64Store .uint64 0,
    .localGet usizeResultLocal,
    .ret] }

def functions : Array Function := #[
  decLtFunction,
  addFunction,
  subFunction,
  ofNatFunction,
  toUInt32Function,
  toNatFunction,
  landFunction,
  shiftLeftFunction,
  decLeFunction,
  decEqFunction,
  complementFunction,
  shiftRightFunction,
  modFunction,
  ofNatLTFunction]

private partial def rewriteInstruction (present : Array Name) : Instruction → Instruction
  | .call (.declaration declaration) =>
      if present.contains declaration then
        .call (.declaration (externalName declaration))
      else .call (.declaration declaration)
  | .block label body => .block label (body.map (rewriteInstruction present))
  | .loop label body => .loop label (body.map (rewriteInstruction present))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteInstruction present))
        (elseBody.map (rewriteInstruction present))
  | instruction => instruction

def expectedSignature? (declaration : Name) : Option Signature :=
  if declaration == `USize.decLt then
    some { params := #[.usize, .usize], results := #[.uint8] }
  else if declaration == `USize.add then
    some { params := #[.usize, .usize], results := #[.usize] }
  else if #[`USize.sub, `USize.land, `USize.shiftLeft, `USize.shiftRight,
      `USize.mod].contains declaration then
    some { params := #[.usize, .usize], results := #[.usize] }
  else if declaration == `USize.ofNat then
    some { params := #[.tobject], results := #[.usize] }
  else if declaration == `USize.ofNatLT then
    some { params := #[.tobject, .erased], results := #[.usize] }
  else if declaration == `USize.toUInt32 then
    some { params := #[.usize], results := #[.uint32] }
  else if declaration == `USize.toNat then
    some { params := #[.usize], results := #[.tobject] }
  else if #[`USize.decLe, `USize.decEq].contains declaration then
    some { params := #[.usize, .usize], results := #[.uint8] }
  else if declaration == `USize.complement then
    some { params := #[.usize], results := #[.usize] }
  else
    none

/-- Internalize exactly the `USize` operations imported by the source closure. -/
def internalizeAvailable (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let present := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
  if present.any fun declaration =>
      #[`USize.ofNat, `USize.ofNatLT].contains declaration then
    for name in #[ResidentNumeric.validateNaturalName,
        ResidentNumeric.naturalLowName, ResidentNumeric.naturalHighName] do
      unless module.functions.any (·.name == name) do
        throw (.missingNumericHelper name)
  if present.contains `USize.toNat then
    unless module.functions.any (·.name == ResidentNumeric.makeNaturalName) do
      throw (.missingNumericHelper ResidentNumeric.makeNaturalName)
  for declaration in present do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.missingExternal declaration)
    let some signature := expectedSignature? declaration |
      throw (.incompatibleExternal declaration)
    unless imports[0]!.signature == signature do
      throw (.incompatibleExternal declaration)
    let helperName := externalName declaration
    if module.imports.any (·.declaration? == some helperName) ||
        module.functions.any (·.name == helperName) || module.exports.contains helperName then
      throw (.reservedDeclaration helperName)
  let selectedHelperNames := present.map externalName
  let selectedFunctions := functions.filter fun function =>
    selectedHelperNames.contains function.name
  let linkedFunctions := module.functions.map fun function =>
    { function with body := function.body.map (rewriteInstruction present) }
  let functions := linkedFunctions ++ selectedFunctions
  let result : Module := {
    module with
    imports := module.imports.filter fun import_ =>
      match import_.declaration? with
      | some declaration => !present.contains declaration
      | none => true
    functions
    exports := selectedHelperNames.foldl Fir.Wasm.addUnique module.exports
    runtimeOperations := Fir.Wasm.collectRuntimeOps functions }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

end Fir.Wasm.Emit.ResidentUSize
