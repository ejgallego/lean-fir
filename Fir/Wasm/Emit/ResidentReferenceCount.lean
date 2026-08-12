import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentReferenceCount

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

private def objectParam : FVarId := ⟨`object⟩
private def oldCountLocal : FVarId := ⟨`oldCount⟩
private def newCountLocal : FVarId := ⟨`newCount⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | amountOverflow (amount : Nat)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def checkedAmount (amount : Nat) : Except LinkError UInt32 :=
  if amount < UInt32.size then
    pure (u32 amount)
  else
    throw (.amountOverflow amount)

def isIncrement : RuntimeOp → Bool
  | .inc .. => true
  | _ => false

def incrementName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_inc_{ordinal}"

/-- Stable checked one-reference increment used by resident container helpers. -/
def incrementOnceName : Name := `fir_inc_once

private def equalsConst (kind : AbiKind) (value : UInt32) :
    List Instruction :=
  [.i32Const kind value, .i32Eq]

private def checkedImmediateBody (check : Bool) : List Instruction :=
  if check then [.ret] else [.unreachable]

private def incrementBody (amount : UInt32) : List Instruction :=
  [.localGet objectParam,
    .i32Load .uint32 (u32 headerRefCountOffset),
    .localSet oldCountLocal,
    .localGet oldCountLocal,
    .i32Const .uint32 amount,
    .i32Add,
    .localSet newCountLocal,
    .localGet newCountLocal,
    .localGet oldCountLocal,
    .i32LtU,
    .ifElse
      [.unreachable]
      [.localGet objectParam,
        .i32Const .uint32 0,
        .i32Add,
        .localGet newCountLocal,
        .i32Store .uint32 (u32 headerRefCountOffset),
        .ret]]

private def persistentBody (check : Bool) : List Instruction :=
  [.localGet objectParam,
    .i32Load .uint32 (u32 headerKindOffset)] ++
  equalsConst .uint32 ObjectKind.natural.code ++
  [.ifElse
    ([.localGet objectParam,
      .i32Load .uint32 (u32 headerAux0Offset)] ++
      equalsConst .uint32 promotedTagMarker ++
      [.ifElse (checkedImmediateBody check) [.ret]])
    [.ret]]

private def liveHeapBody (amount : UInt32) (check : Bool) :
    List Instruction :=
  [.localGet objectParam,
    .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 persistentFlag,
    .i32And] ++
  equalsConst .uint32 persistentFlag ++
  [.ifElse (persistentBody check) (incrementBody amount)]

private def alignedHeapBody (amount : UInt32) (check : Bool) :
    List Instruction :=
  [.localGet objectParam,
    .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 liveFlag,
    .i32And] ++
  equalsConst .uint32 liveFlag ++
  [.ifElse (liveHeapBody amount check) [.unreachable]]

private def heapBody (amount : UInt32) (check : Bool) : List Instruction :=
  [.localGet objectParam] ++
  equalsConst .tobject 0 ++
  [.ifElse
    [.unreachable]
    ([.localGet objectParam,
      .i32Const .uint32 (u32 (target.heapAlignment - 1)),
      .i32And] ++
      equalsConst .uint32 0 ++
      [.ifElse (alignedHeapBody amount check) [.unreachable]])]

def incrementFunction (ordinal amount : Nat) (check : Bool) :
    Except LinkError Function := do
  let amount ← checkedAmount amount
  return {
    name := incrementName ordinal
    params := #[(objectParam, .tobject)]
    results := #[]
    locals := #[
      (oldCountLocal, .uint32),
      (newCountLocal, .uint32)]
    body :=
      [.localGet objectParam,
        .i32Const .uint32 1,
        .i32And,
        .ifElse
          (checkedImmediateBody check)
          (heapBody amount check)] }

private def incrementOnceFunction : Function := {
  name := incrementOnceName
  params := #[(objectParam, .tobject)]
  results := #[]
  locals := #[
    (oldCountLocal, .uint32),
    (newCountLocal, .uint32)]
  body :=
    [.localGet objectParam,
      .i32Const .uint32 1,
      .i32And,
      .ifElse
        (checkedImmediateBody true)
        (heapBody 1 true)] }

private structure Binding where
  operation : RuntimeOp
  name : Name
  function : Function

private partial def rewriteInstruction
    (names : Std.HashMap RuntimeOp Name) : Instruction → Instruction
  | .call (.runtime candidate) =>
      match names.get? candidate with
      | some name => .call (.declaration name)
      | none => .call (.runtime candidate)
  | .block label body =>
      .block label (body.map (rewriteInstruction names))
  | .loop label body =>
      .loop label (body.map (rewriteInstruction names))
  | .ifElse thenBody elseBody =>
      .ifElse
        (thenBody.map (rewriteInstruction names))
        (elseBody.map (rewriteInstruction names))
  | instruction => instruction

/--
Internalize nonrecursive reference-count increments. Checked immediate and
promoted-tag representations are no-ops; their unchecked variants trap.
Persistent heap objects are no-ops, while ordinary live heap objects receive
an overflow-checked direct reference-count update.
-/
def internalizeIncrements (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  if module.imports.any (·.declaration? == some incrementOnceName) ||
      module.functions.any (·.name == incrementOnceName) ||
      module.exports.contains incrementOnceName then
    throw (.reservedDeclaration incrementOnceName)
  let module := {
    module with
    functions := module.functions.push incrementOnceFunction }
  let operations := module.runtimeOperations.filter isIncrement
  let bindings ← operations.toList.zipIdx.toArray.mapM fun (operation, ordinal) => do
    let name := incrementName ordinal
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) || module.exports.contains name then
      throw (.reservedDeclaration name)
    let function ← match operation with
      | .inc amount check => incrementFunction ordinal amount check
      | _ => throw .unsupportedOperation
    return { operation, name, function : Binding }
  let names := bindings.foldl
    (init := Std.HashMap.emptyWithCapacity bindings.size)
    fun names binding => names.insert binding.operation binding.name
  let mut functions := module.functions.map fun function =>
    { function with body := function.body.map (rewriteInstruction names) }
  for binding in bindings do
    if functions.any (·.name == binding.name) then
      throw (.reservedDeclaration binding.name)
    functions := functions.push binding.function
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let result : Module := {
    module with
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    functions
    exports := bindings.foldl
      (fun exports binding => Fir.Wasm.addUnique exports binding.name) module.exports
    runtimeOperations }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

def exampleOperations : Array RuntimeOp := #[
  .inc 1 true,
  .inc 3 false]

def exampleCheckedCaller : Function := {
  name := `resident_inc_checked
  params := #[(objectParam, .tobject)]
  results := #[]
  locals := #[]
  body := [
    .localGet objectParam,
    .call (.runtime exampleOperations[0]!),
    .ret] }

def exampleUncheckedCaller : Function := {
  name := `resident_inc_unchecked
  params := #[(objectParam, .tobject)]
  results := #[]
  locals := #[]
  body := [
    .localGet objectParam,
    .call (.runtime exampleOperations[1]!),
    .ret] }

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport
  functions := #[exampleCheckedCaller, exampleUncheckedCaller]
  exports := #[exampleCheckedCaller.name, exampleUncheckedCaller.name]
  initializers := #[]
  runtimeOperations := exampleOperations
  memory := some ResidentRuntime.residentMemory }

def residentExampleModule : Except String Module :=
  internalizeIncrements exampleModule
    |>.mapError fun error => s!"reference counts: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr #[
      Json.mkObj [
        ("entry", exampleCheckedCaller.name.toString),
        ("amount", 1),
        ("check", true)],
      Json.mkObj [
        ("entry", exampleUncheckedCaller.name.toString),
        ("amount", 3),
        ("check", false)]]),
    ("status", "generation-only; W6 reference-count contract proof pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      module.exports.contains exampleCheckedCaller.name &&
      module.exports.contains exampleUncheckedCaller.name &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentReferenceCount
