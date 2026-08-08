import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentUSize

open Fir.Wasm
open Lean

/-!
# Wasm-resident `USize` loop operations

Final LCNF generated for `Array.forIn'Unsafe` keeps its cursor and bound in
native `USize` lanes.  These helpers implement the two operations used by that
loop directly over wasm64 values.  Addition is assembled from two 32-bit
halves so it retains `USize`'s modulo-2^64 behavior without extending FIR's
shared symbolic instruction surface.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | reservedDeclaration (name : Name)
  | missingExternal (name : Name)
  | incompatibleExternal (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

def externalDeclarations : Array Name := #[`USize.decLt, `USize.add]

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

def functions : Array Function := #[decLtFunction, addFunction]

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

private def expectedSignature? (declaration : Name) : Option Signature :=
  if declaration == `USize.decLt then
    some { params := #[.usize, .usize], results := #[.uint8] }
  else if declaration == `USize.add then
    some { params := #[.usize, .usize], results := #[.usize] }
  else
    none

/-- Internalize exactly the `USize` operations imported by the source closure. -/
def internalizeAvailable (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let present := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
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
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

end Fir.Wasm.Emit.ResidentUSize
