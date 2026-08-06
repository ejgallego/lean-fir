import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentNatMod

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

/-!
# Wasm-resident `Nat.mod` for Illuminate frame arithmetic

Illuminate uses `Nat.mod` to wrap a frame offset within a finite animation
interval.  This helper keeps that operation inside the generated module.  It
accepts every canonical natural whose value fits in 32 bits, implements Lean's
zero-divisor result (`n % 0 = n`), and traps explicitly for wider operands.
The width restriction is an input capability of the Illuminate package, not a
host fallback.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingNumericHelper (name : Name)
  | reservedDeclaration (name : Name)
  | missingExternal
  | incompatibleExternal
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

def declaration : Name := `Nat.mod
def helperName : Name := `fir_ext_Nat_mod

private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def leftLowLocal : FVarId := ⟨`leftLow⟩
private def leftHighLocal : FVarId := ⟨`leftHigh⟩
private def rightLowLocal : FVarId := ⟨`rightLow⟩
private def rightHighLocal : FVarId := ⟨`rightHigh⟩
private def remainderLocal : FVarId := ⟨`remainder⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def resultLocal : FVarId := ⟨`result⟩

private def trapUnlessZero (localId : FVarId) : List Instruction := [
  .localGet localId,
  .i32Const .uint32 0,
  .i32Eq,
  .ifElse [] [.unreachable]]

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

def function : Function := {
  name := helperName
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.tobject]
  locals := #[
    (leftLowLocal, .uint32), (leftHighLocal, .uint32),
    (rightLowLocal, .uint32), (rightHighLocal, .uint32),
    (remainderLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (resultLocal, .tobject)]
  body := [
    .localGet leftParam,
    .call (.declaration ResidentNumeric.validateNaturalName),
    .localGet rightParam,
    .call (.declaration ResidentNumeric.validateNaturalName),
    .localGet leftParam,
    .call (.declaration ResidentNumeric.naturalLowName),
    .localSet leftLowLocal,
    .localGet leftParam,
    .call (.declaration ResidentNumeric.naturalHighName),
    .localSet leftHighLocal,
    .localGet rightParam,
    .call (.declaration ResidentNumeric.naturalLowName),
    .localSet rightLowLocal,
    .localGet rightParam,
    .call (.declaration ResidentNumeric.naturalHighName),
    .localSet rightHighLocal] ++
    trapUnlessZero leftHighLocal ++ trapUnlessZero rightHighLocal ++ [
    .localGet rightLowLocal,
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse
      [.localGet leftLowLocal, .localSet remainderLocal]
      [.localGet leftLowLocal, .localGet rightLowLocal, .i32RemU,
        .localSet remainderLocal],
    .localGet remainderLocal,
    .i32Const .uint32 0,
    .call (.declaration ResidentNumeric.makeNaturalName)] ++
    retypeNatural }

private partial def rewriteInstruction : Instruction → Instruction
  | .call (.declaration candidate) =>
      if candidate == declaration then .call (.declaration helperName)
      else .call (.declaration candidate)
  | .block label body => .block label (body.map rewriteInstruction)
  | .loop label body => .loop label (body.map rewriteInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map rewriteInstruction) (elseBody.map rewriteInstruction)
  | instruction => instruction

def internalize (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  for name in #[ResidentNumeric.validateNaturalName,
      ResidentNumeric.naturalLowName, ResidentNumeric.naturalHighName,
      ResidentNumeric.makeNaturalName] do
    unless module.functions.any (·.name == name) do
      throw (.missingNumericHelper name)
  if module.imports.any (·.declaration? == some helperName) ||
      module.functions.any (·.name == helperName) ||
      module.exports.contains helperName then
    throw (.reservedDeclaration helperName)
  let imports := module.imports.filter (·.declaration? == some declaration)
  unless imports.size == 1 do
    throw .missingExternal
  unless imports[0]!.signature == {
      params := #[.tobject, .tobject], results := #[.tobject] } do
    throw .incompatibleExternal
  let functions := module.functions.map fun candidate =>
    { candidate with body := candidate.body.map rewriteInstruction }
  let result : Module := {
    module with
    imports := module.imports.filter (·.declaration? != some declaration)
    functions := functions.push function
    exports := Fir.Wasm.addUnique module.exports helperName
    runtimeOperations := Fir.Wasm.collectRuntimeOps (functions.push function) }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

end Fir.Wasm.Emit.ResidentNatMod
