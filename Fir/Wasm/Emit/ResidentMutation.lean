import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentMutation

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

private def objectParam : FVarId := ⟨`object⟩
private def valueParam : FVarId := ⟨`value⟩
private def addressLocal : FVarId := ⟨`address⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | unsupportedScalarKind (kind : AbiKind)
  | offsetOverflow (value : Nat)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def checkedOffset (value : Nat) : Except LinkError UInt32 :=
  if value < UInt32.size then
    pure (u32 value)
  else
    throw (.offsetOverflow value)

def isSetter : RuntimeOp → Bool
  | .objectSet .. | .scalarSet .. => true
  | _ => false

def setterName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_setter_{ordinal}"

private def equalsConst (kind : AbiKind) (value : UInt32) :
    List Instruction :=
  [.i32Const kind value, .i32Eq]

private def rawAddressPrefix : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet objectParam,
  .i32Store .object 0,
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet addressLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0]

private def requireLiveConstructor (success : List Instruction) :
    List Instruction :=
  [.localGet addressLocal] ++
    equalsConst .uint32 0 ++
    [.ifElse
      [.unreachable]
      ([.localGet addressLocal,
        .i32Const .uint32 (u32 (target.heapAlignment - 1)),
        .i32And] ++
        equalsConst .uint32 0 ++
        [.ifElse
          ([.localGet addressLocal,
            .i32Load .uint32 (u32 headerFlagsOffset),
            .i32Const .uint32 liveFlag,
            .i32And] ++
            equalsConst .uint32 liveFlag ++
            [.ifElse
              ([.localGet addressLocal,
                .i32Load .uint32 (u32 headerKindOffset)] ++
                equalsConst .uint32 ObjectKind.constructor.code ++
                [.ifElse success [.unreachable]])
              [.unreachable]])
          [.unreachable]])]

private def objectSetFunction (ordinal index : Nat) (field : AbiKind) :
    Except LinkError Function := do
  let fieldOffset ← checkedOffset <|
    headerBytes + target.semanticSlotBytes * index
  let indexWord ← checkedOffset index
  return {
    name := setterName ordinal
    params := #[(objectParam, .object), (valueParam, field)]
    results := #[]
    locals := #[
      (addressLocal, .uint32),
      (savedScratchLocal, .uint32)]
    body := rawAddressPrefix ++ requireLiveConstructor
      [.i32Const .uint32 indexWord,
        .localGet addressLocal,
        .i32Load .uint32 (u32 headerAux1Offset),
        .i32LtU,
        .ifElse
          [.localGet addressLocal,
            .localGet valueParam,
            .i32Store field fieldOffset]
          [.unreachable],
        .ret] }

private def scalarBytes : AbiKind → Option Nat
  | .uint8 => some 1
  | .uint16 => some 2
  | .uint32 => some 4
  | .uint64 => some 8
  | _ => none

private def scalarStore (field : AbiKind) (fieldOffset : UInt32) :
    Except LinkError (List Instruction) :=
  match field with
  | .uint8 =>
      pure [.localGet addressLocal, .localGet valueParam,
        .i32Store8 .uint8 fieldOffset]
  | .uint16 =>
      pure [.localGet addressLocal, .localGet valueParam,
        .i32Store16 .uint16 fieldOffset]
  | .uint32 =>
      pure [.localGet addressLocal, .localGet valueParam,
        .i32Store .uint32 fieldOffset]
  | .uint64 =>
      pure [.localGet addressLocal, .localGet valueParam,
        .i64Store .uint64 fieldOffset]
  | kind => throw (.unsupportedScalarKind kind)

private def scalarSetFunction (ordinal width byteOffset : Nat)
    (field : AbiKind) : Except LinkError Function := do
  let some bytes := scalarBytes field |
    throw (.unsupportedScalarKind field)
  let fieldOffset ← checkedOffset <|
    headerBytes + target.semanticSlotBytes * width + byteOffset
  let widthWord ← checkedOffset width
  let requiredWord ← checkedOffset (byteOffset + bytes)
  let store ← scalarStore field fieldOffset
  return {
    name := setterName ordinal
    params := #[(objectParam, .object), (valueParam, field)]
    results := #[]
    locals := #[
      (addressLocal, .uint32),
      (savedScratchLocal, .uint32)]
    body := rawAddressPrefix ++ requireLiveConstructor (
      [.localGet addressLocal,
        .i32Load .uint32 (u32 headerAux1Offset),
        .localGet addressLocal,
        .i32Load .uint32 (u32 headerAux2Offset),
        .i32Add] ++
      equalsConst .uint32 widthWord ++
      [.ifElse
        ([.localGet addressLocal,
          .i32Load .uint32 (u32 headerAux3Offset),
          .i32Const .uint32 requiredWord,
          .i32LtU,
          .ifElse [.unreachable] store])
        [.unreachable],
        .ret]) }

def setterFunction (ordinal : Nat) (operation : RuntimeOp) :
    Except LinkError Function := do
  unless operation.abiWellFormed do
    throw .unsupportedOperation
  match operation with
  | .objectSet index field => objectSetFunction ordinal index field
  | .scalarSet width byteOffset field =>
      scalarSetFunction ordinal width byteOffset field
  | _ => throw .unsupportedOperation

private partial def rewriteInstruction (operation : RuntimeOp)
    (name : Name) : Instruction → Instruction
  | .call (.runtime candidate) =>
      if candidate == operation then
        .call (.declaration name)
      else
        .call (.runtime candidate)
  | .block label body =>
      .block label (body.map (rewriteInstruction operation name))
  | .ifElse thenBody elseBody =>
      .ifElse
        (thenBody.map (rewriteInstruction operation name))
        (elseBody.map (rewriteInstruction operation name))
  | instruction => instruction

private def rewriteFunction (operation : RuntimeOp) (name : Name)
    (function : Function) : Function :=
  { function with body := function.body.map (rewriteInstruction operation name) }

private def internalizeOne (ordinal : Nat) (operation : RuntimeOp)
    (module : Module) : Except LinkError Module := do
  let name := setterName ordinal
  if module.imports.any (·.declaration? == some name) ||
      module.functions.any (·.name == name) ||
      module.exports.contains name then
    throw (.reservedDeclaration name)
  let function ← setterFunction ordinal operation
  let functions :=
    (module.functions.map (rewriteFunction operation name)).push function
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
  return {
    module with
    imports
    functions
    exports := Fir.Wasm.addUnique module.exports name
    runtimeOperations }

/--
Internalize direct constructor object-slot and packed-scalar writes. The
helpers validate the recognized live-constructor boundary and the exact W6
header coordinates before writing module-owned memory. They intentionally do
not perform ownership updates: LCNF emits `inc`/`dec` as separate operations.
-/
def internalizeSetters (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let operations := module.runtimeOperations.filter isSetter
  let result ← operations.toList.zipIdx.foldlM (init := module)
    fun result (operation, ordinal) =>
      internalizeOne ordinal operation result
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

def exampleOperations : Array RuntimeOp := #[
  .objectSet 1 .tobject,
  .scalarSet 2 1 .uint8]

def exampleObjectSetCaller : Function := {
  name := `resident_set_object
  params := #[(objectParam, .object), (valueParam, .tobject)]
  results := #[]
  locals := #[]
  body := [
    .localGet objectParam,
    .localGet valueParam,
    .call (.runtime exampleOperations[0]!),
    .ret] }

def exampleScalarSetCaller : Function := {
  name := `resident_set_scalar
  params := #[(objectParam, .object), (valueParam, .uint8)]
  results := #[]
  locals := #[]
  body := [
    .localGet objectParam,
    .localGet valueParam,
    .call (.runtime exampleOperations[1]!),
    .ret] }

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport
  functions := #[exampleObjectSetCaller, exampleScalarSetCaller]
  exports := #[exampleObjectSetCaller.name, exampleScalarSetCaller.name]
  initializers := #[]
  runtimeOperations := exampleOperations
  memory := some ResidentRuntime.residentMemory }

def residentExampleModule : Except String Module :=
  internalizeSetters exampleModule
    |>.mapError fun error => s!"setters: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr #[
      Json.mkObj [("entry", exampleObjectSetCaller.name.toString)],
      Json.mkObj [("entry", exampleScalarSetCaller.name.toString)]]),
    ("objectHeader",
      Json.mkObj [
        ("tag", 7),
        ("objectFields", 2),
        ("usizeFields", 0),
        ("scalarBytes", 2)]),
    ("status", "generation-only; W6 mutation contract proof pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      module.exports.contains exampleObjectSetCaller.name &&
      module.exports.contains exampleScalarSetCaller.name &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentMutation
