import Fir.Wasm.Emit.ResidentBigNumeric

namespace Fir.Wasm.Emit.ResidentUSize

open Fir.Wasm
open Lean

/-!
# Wasm-resident `USize` operations

Final LCNF generated for `Array.forIn'Unsafe` keeps its cursor and bound in
native `USize` lanes. These helpers implement the generic scalar frontier over
wasm64 values using the corresponding core Wasm scalar instructions while
retaining `USize`'s modulo-2^64 behavior.
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
private def lowLocal : FVarId := ⟨`low⟩
private def highLocal : FVarId := ⟨`high⟩
private def raw32Local : FVarId := ⟨`raw32⟩
private def raw64Local : FVarId := ⟨`raw64⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def uint8ResultLocal : FVarId := ⟨`uint8Result⟩
private def usizeResultLocal : FVarId := ⟨`usizeResult⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def valueParam : FVarId := ⟨`value⟩
private def erasedParam : FVarId := ⟨`erased⟩

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

private def binaryFunction (declaration : Name) (operation : Instruction) : Function := {
  name := externalName declaration
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.usize]
  locals := #[(raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := [.localGet leftParam, .localGet rightParam, operation] ++ retypeUSize }

private def decisionFunction (declaration : Name) (comparison : Instruction) : Function := {
  name := externalName declaration
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.uint8]
  locals := #[(raw32Local, .uint32), (savedScratchLocal, .uint64),
    (uint8ResultLocal, .uint8)]
  body := [.localGet leftParam, .localGet rightParam, comparison,
    .localSet raw32Local] ++ retypeUInt8 }

def decLtFunction : Function :=
  decisionFunction `USize.decLt .i64LtU

def addFunction : Function :=
  binaryFunction `USize.add .i64Add

def subFunction : Function :=
  binaryFunction `USize.sub .i64Sub

private def checkedNatToRawUSize : List Instruction := [
  .localGet valueParam,
  .call (.declaration ResidentBigNumeric.validateNaturalName),
  .localGet valueParam,
  .i32Const .uint32 0,
  .call (.declaration ResidentBigNumeric.naturalHighName),
  .i64ExtendI32U .uint64,
  .i64Const .uint64 32,
  .i64Shl,
  .localGet valueParam,
  .i32Const .uint32 0,
  .call (.declaration ResidentBigNumeric.naturalLowName),
  .i64ExtendI32U .uint64,
  .i64Or,
  .localSet raw64Local]

private def immediateNatToUSize : List Instruction := [
  .localGet valueParam,
  .i32Const .uint32 1,
  .i32ShrU,
  .i64ExtendI32U .usize,
  .ret]

private def checkedNatToUSize : List Instruction :=
  checkedNatToRawUSize ++ [.localGet raw64Local] ++ retypeUSize

private def ofNatBody : List Instruction := [
  .localGet valueParam,
  .i32Const .uint32 1,
  .i32And,
  .ifElse immediateNatToUSize checkedNatToUSize]

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

/- Mirror upstream `lean_usize_to_nat`: values that fit the wasm32 tagged-Nat
payload are boxed directly, while larger values retain the generic natural
constructor. This threshold is representation-stable even if a future target
specialization changes the physical `USize` lane from FIR's current Lean64
contract. -/
private def immediateUSizeToNat : List Instruction := [
  .localGet valueParam,
  .i64Const .uint64 1,
  .i64Shl,
  .i64Const .uint64 1,
  .i64Or,
  .i32WrapI64 .tagged,
  .ret]

private def checkedUSizeToNat : List Instruction :=
  splitUSize valueParam lowLocal highLocal ++ [
    .localGet lowLocal,
    .localGet highLocal,
    .call (.declaration ResidentNumeric.makeNaturalName)] ++ retypeObject

def toNatFunction : Function := {
  name := externalName `USize.toNat
  params := #[(valueParam, .usize)]
  results := #[.tobject]
  locals := #[(lowLocal, .uint32), (highLocal, .uint32),
    (raw32Local, .uint32), (savedScratchLocal, .uint64),
    (objectResultLocal, .tobject)]
  body := [
    .localGet valueParam,
    .i64Const .uint64 2147483648,
    .i64LtU,
    .ifElse immediateUSizeToNat checkedUSizeToNat] }

def landFunction : Function :=
  binaryFunction `USize.land .i64And

def shiftLeftFunction : Function :=
  binaryFunction `USize.shiftLeft .i64Shl

def shiftRightFunction : Function :=
  binaryFunction `USize.shiftRight .i64ShrU

def decLeFunction : Function :=
  decisionFunction `USize.decLe .i64LeU

def decEqFunction : Function :=
  decisionFunction `USize.decEq .i64Eq

def complementFunction : Function := {
  name := externalName `USize.complement
  params := #[(valueParam, .usize)]
  results := #[.usize]
  locals := #[(raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := [.localGet valueParam, .i64Const .uint64 0xffffffffffffffff,
    .i64Xor] ++ retypeUSize }

def modFunction : Function := {
  name := externalName `USize.mod
  params := #[(leftParam, .usize), (rightParam, .usize)]
  results := #[.usize]
  locals := #[(raw64Local, .uint64), (savedScratchLocal, .uint64),
    (usizeResultLocal, .usize)]
  body := [
    .localGet rightParam,
    .i64Eqz,
    .ifElse
      [.localGet leftParam, .i64Const .uint64 0, .i64Or,
        .localSet raw64Local]
      [.localGet leftParam, .localGet rightParam, .i64RemU,
        .localSet raw64Local],
    .localGet raw64Local] ++ retypeUSize }

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

private partial def instructionUsesMemory : Instruction → Bool
  | .i32Load .. | .i32Load8S .. | .i32Load8U ..
  | .i32Load16S .. | .i32Load16U .. | .i64Load ..
  | .i64Load8S .. | .i64Load8U .. | .i64Load16S ..
  | .i64Load16U .. | .i64Load32S .. | .i64Load32U ..
  | .f32Load .. | .f64Load .. | .i32Store8 .. | .i32Store16 ..
  | .i32Store .. | .i64Store8 .. | .i64Store16 .. | .i64Store32 ..
  | .i64Store .. | .f32Store .. | .f64Store .. | .memorySize
  | .memoryGrow => true
  | .block _ body | .loop _ body => body.any instructionUsesMemory
  | .ifElse thenBody elseBody =>
      thenBody.any instructionUsesMemory || elseBody.any instructionUsesMemory
  | _ => false

#guard immediateNatToUSize.contains (.i64ExtendI32U .usize)
#guard !immediateNatToUSize.any instructionUsesMemory
#guard immediateUSizeToNat.contains (.i32WrapI64 .tagged)
#guard !immediateUSizeToNat.any instructionUsesMemory

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
    for name in #[ResidentBigNumeric.validateNaturalName,
        ResidentBigNumeric.naturalLowName, ResidentBigNumeric.naturalHighName] do
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
