import Fir.Wasm.Emit.ResidentHash

namespace Fir.Wasm.Emit.ResidentName

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean
open Lean.Compiler

/-!
# Wasm-resident `Lean.Name.beq`

The helper follows Lean's iterative runtime implementation: pointer equality
is the fast path, string and numeric components are compared at the current
node, and the two parent chains are traversed in a structured Wasm loop.  The
native cached-hash rejection is an optimization only and is deliberately
omitted; structural equality is the semantic authority.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingHelper (name : Name)
  | reservedDeclaration (name : Name)
  | incompatibleExternal
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

def declaration : Name := `Lean.Name.beq
def helperName : Name := ResidentNumeric.externalName declaration

private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def leftTagLocal : FVarId := ⟨`leftTag⟩
private def rightTagLocal : FVarId := ⟨`rightTag⟩
private def decisionLocal : FVarId := ⟨`decision⟩
private def nameLoop : FVarId := ⟨`nameEqualityLoop⟩

private def equalsConst (kind : AbiKind) (value : UInt32) : List Instruction :=
  [.i32Const kind value, .i32Eq]

private def trapWhenTrue (condition : List Instruction) : List Instruction :=
  condition ++ [.ifElse [.unreachable] []]

private def trapUnlessTrue (condition : List Instruction) : List Instruction :=
  trapWhenTrue (condition ++ equalsConst .uint32 0)

private def validateNode (object : FVarId) : List Instruction :=
  trapWhenTrue [
    .localGet object,
    .i32Const .uint32 (u32 heapBase),
    .i32LtU] ++
  trapWhenTrue [
    .localGet object,
    .i32Const .uint32 (u32 (target.heapAlignment - 1)),
    .i32And] ++
  trapUnlessTrue [
    .localGet object,
    .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 liveFlag,
    .i32And] ++
  trapUnlessTrue [
    .localGet object,
    .i32Load .uint32 (u32 headerKindOffset),
    .i32Const .uint32 ObjectKind.constructor.code,
    .i32Eq] ++
  trapUnlessTrue [
    .localGet object,
    .i32Load .uint32 (u32 headerAux1Offset),
    .i32Const .uint32 2,
    .i32Eq]

private def returnDecision (value : UInt32) : List Instruction := [
  .i32Const .uint32 value,
  .i64ExtendI32U .uint64,
  .i32WrapI64 .uint8,
  .ret]

private def compareCurrentComponent : List Instruction := [
  .localGet leftTagLocal,
  .i32Const .uint32 1,
  .i32Eq,
  .ifElse
    [.localGet leftParam,
      .i32Load .object (u32 (headerBytes + target.semanticSlotBytes)),
      .localGet rightParam,
      .i32Load .object (u32 (headerBytes + target.semanticSlotBytes)),
      .call (.declaration (ResidentString.externalName `String.decEq)),
      .localSet decisionLocal]
    [.localGet leftParam,
      .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
      .localGet rightParam,
      .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
      .call (.declaration (ResidentBigNumeric.externalName `Nat.decEq)),
      .localSet decisionLocal],
  .localGet decisionLocal,
  .i32Eqz,
  .ifElse (returnDecision 0) []]

def beqFunction : Function := {
  name := helperName
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := #[(leftTagLocal, .uint32), (rightTagLocal, .uint32),
    (decisionLocal, .uint8)]
  body := [
    .loop nameLoop <| [
      .localGet leftParam,
      .localGet rightParam,
      .i32Eq,
      .ifElse (returnDecision 1) [],
      .localGet leftParam,
      .i32Const .uint32 1,
      .i32And,
      .localGet rightParam,
      .i32Const .uint32 1,
      .i32And,
      .i32Or,
      .ifElse (returnDecision 0) []] ++
      validateNode leftParam ++ validateNode rightParam ++ [
      .localGet leftParam,
      .i32Load .uint32 (u32 headerAux0Offset),
      .localSet leftTagLocal,
      .localGet rightParam,
      .i32Load .uint32 (u32 headerAux0Offset),
      .localSet rightTagLocal,
      .localGet leftTagLocal,
      .localGet rightTagLocal,
      .i32Eq,
      .i32Eqz,
      .ifElse (returnDecision 0) [],
      .localGet leftTagLocal,
      .i32Const .uint32 1,
      .i32LtU,
      .i32Eqz,
      .localGet leftTagLocal,
      .i32Const .uint32 3,
      .i32LtU,
      .i32And] ++
      trapUnlessTrue [] ++
      compareCurrentComponent ++ [
      .localGet leftParam,
      .i32Load .tobject (u32 headerBytes),
      .localSet leftParam,
      .localGet rightParam,
      .i32Load .tobject (u32 headerBytes),
      .localSet rightParam,
      .br nameLoop]] }

private partial def rewriteInstruction : Instruction → Instruction
  | .call (.declaration candidate) =>
      if candidate == declaration then .call (.declaration helperName)
      else .call (.declaration candidate)
  | .block label body => .block label (body.map rewriteInstruction)
  | .loop label body => .loop label (body.map rewriteInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map rewriteInstruction) (elseBody.map rewriteInstruction)
  | instruction => instruction

def internalizeAvailable (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let imports := module.imports.filter (·.declaration? == some declaration)
  if imports.isEmpty then return module
  unless imports.size == 1 && imports[0]!.signature == {
      params := #[.tobject, .tobject], results := #[.uint8] } do
    throw .incompatibleExternal
  for name in #[ResidentString.externalName `String.decEq,
      ResidentBigNumeric.externalName `Nat.decEq] do
    unless module.functions.any (·.name == name) do
      throw (.missingHelper name)
  if module.functions.any (·.name == helperName) ||
      module.exports.contains helperName then
    throw (.reservedDeclaration helperName)
  let functions := (module.functions.map fun function =>
    { function with body := function.body.map rewriteInstruction }).push beqFunction
  let result : Module := {
    module with
    imports := module.imports.filter (·.declaration? != some declaration)
    functions
    exports := Fir.Wasm.addUnique module.exports helperName
    runtimeOperations := Fir.Wasm.collectRuntimeOps functions }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

private def exampleImport : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := { params := #[.tobject, .tobject], results := #[.uint8] }
  externalTypes? := some {
    params := #[LCNF.ImpureType.tobject, LCNF.ImpureType.tobject]
    result := LCNF.ImpureType.uint8 } }

def residentExampleModule : Except String Module := do
  let module ← ResidentHash.residentExampleModule
  internalizeAvailable { module with imports := module.imports.push exampleImport }
    |>.mapError fun error => s!"Name: {repr error}"

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      module.exports.contains helperName &&
      (Fir.Wasm.validateModule module).isOk &&
      (Fir.Wasm.Emit.encode module).isOk
  | .error _ => false

end Fir.Wasm.Emit.ResidentName
