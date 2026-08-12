import Fir.Wasm.Emit.ResidentRuntime
import Fir.Wasm.Emit.ResidentContainerLayout

namespace Fir.Wasm.Emit.ResidentRelease

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

private def objectParam : FVarId := ⟨`object⟩
private def checkParam : FVarId := ⟨`check⟩
private def addressLocal : FVarId := ⟨`address⟩
private def kindLocal : FVarId := ⟨`kind⟩
private def countLocal : FVarId := ⟨`count⟩
private def captureCountLocal : FVarId := ⟨`captureCount⟩
private def descriptorLocal : FVarId := ⟨`descriptor⟩
private def refCountLocal : FVarId := ⟨`refCount⟩
private def markerLocal : FVarId := ⟨`marker⟩
private def arrayCursorLocal : FVarId := ⟨`arrayCursor⟩
private def arrayIndexLocal : FVarId := ⟨`arrayIndex⟩
private def arrayReleaseLoop : FVarId := ⟨`arrayReleaseLoop⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | amountOverflow (amount : Nat)
  | descriptorOverflow (count : Nat)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def checkedWord (value : Nat) : Except LinkError UInt32 :=
  if value < UInt32.size then
    pure (u32 value)
  else
    throw (.amountOverflow value)

def isRelease : RuntimeOp → Bool
  | .dec .. | .delete => true
  | _ => false

def releaseName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_release_{ordinal}"

def releaseHeaderName : Name := `fir_release_header
def decrementOnceName : Name := `fir_dec_once

/--
The compiler-produced `prettyM` graph has at most five constructor object
fields. The resident recursive helper accepts a much wider 32-field frontier
and traps before reading any object beyond it. This is a generation boundary,
not a replacement for a future unbounded release loop instruction.
-/
def constructorFieldLimit : Nat := 32

private def equalsConst (kind : AbiKind) (value : UInt32) :
    List Instruction :=
  [.i32Const kind value, .i32Eq]

private def checkedNoop : List Instruction :=
  [.localGet checkParam, .ifElse [.ret] [.unreachable]]

private def releaseHeaderFunction : Function := {
  name := releaseHeaderName
  params := #[(addressLocal, .uint32)]
  results := #[]
  locals := #[]
  body := [
    .localGet addressLocal,
    .i32Const .uint32 ObjectKind.freed.code,
    .i32Store .uint32 (u32 headerKindOffset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerFlagsOffset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerRefCountOffset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux0Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux1Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux2Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux3Offset),
    .ret] }

private def releaseChild (index : Nat) : List Instruction :=
  [.localGet addressLocal,
    .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes * index)),
    .i32Const .uint32 1,
    .call (.declaration decrementOnceName)]

private def releaseConstructorFields : List Instruction :=
  (List.range constructorFieldLimit).flatMap fun index =>
    [.i32Const .uint32 (u32 index),
      .localGet countLocal,
      .i32LtU,
      .ifElse (releaseChild index) []]

private def constructorReleaseBody : List Instruction :=
  [.i32Const .uint32 (u32 constructorFieldLimit),
    .localGet countLocal,
    .i32LtU,
    .ifElse
      [.unreachable]
      (releaseConstructorFields ++ [.ret])]

private def arrayReleaseBody : List Instruction := [
  .localGet addressLocal,
  .i32Const .uint32 (u32 headerBytes),
  .i32Add,
  .localSet arrayCursorLocal,
  .i32Const .uint32 0,
  .localSet arrayIndexLocal,
  .loop arrayReleaseLoop [
    .localGet arrayIndexLocal,
    .localGet countLocal,
    .i32LtU,
    .ifElse [
      .localGet arrayCursorLocal,
      .i32Load .tobject 0,
      .i32Const .uint32 1,
      .call (.declaration decrementOnceName),
      .localGet arrayCursorLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet arrayCursorLocal,
      .localGet arrayIndexLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet arrayIndexLocal,
      .br arrayReleaseLoop] []],
  .ret]

private def opaqueReleaseBody : List Instruction :=
  [.localGet markerLocal] ++
  equalsConst .uint32 ResidentContainerLayout.arrayMarker ++
  [.ifElse arrayReleaseBody [.ret]]

private def descriptorOwnedFields (descriptor : Array AbiKind) :
    List Instruction :=
  descriptor.toList.zipIdx.flatMap fun (kind, index) =>
    if kind.isObjectField then releaseChild index else []

private partial def descriptorReleaseBody
    (descriptors : Array (Array AbiKind)) (index : Nat) :
    Except LinkError (List Instruction) := do
  if h : index < descriptors.size then
    let descriptor := descriptors[index]
    let descriptorIndex ← checkedWord index
    let captureCount ← checkedWord descriptor.size
    let rest ← descriptorReleaseBody descriptors (index + 1)
    return (
      [.localGet descriptorLocal] ++
      equalsConst .uint32 descriptorIndex ++
      [.ifElse
        ([.localGet captureCountLocal] ++
          equalsConst .uint32 captureCount ++
          [.ifElse
            (descriptorOwnedFields descriptor ++ [.ret])
            [.unreachable]])
        rest])
  else
    return [.unreachable]

private def ownedReleaseBody (descriptors : Array (Array AbiKind)) :
    Except LinkError (List Instruction) := do
  let closureBody ← descriptorReleaseBody descriptors 0
  return (
    [.localGet kindLocal] ++
    equalsConst .uint32 ObjectKind.constructor.code ++
    [.ifElse
      constructorReleaseBody
      ([.localGet kindLocal] ++
        equalsConst .uint32 ObjectKind.closure.code ++
        [.ifElse closureBody
          ([.localGet kindLocal] ++
            equalsConst .uint32 ObjectKind.opaque.code ++
            [.ifElse opaqueReleaseBody [.ret]])])])

private def decrementAboveOneBody : List Instruction :=
  [.localGet addressLocal,
    .localGet refCountLocal,
    .i32Const .uint32 1,
    .i32Sub,
    .i32Store .uint32 (u32 headerRefCountOffset),
    .ret]

private def ordinaryReleaseBody
    (descriptors : Array (Array AbiKind)) :
    Except LinkError (List Instruction) := do
  let owned ← ownedReleaseBody descriptors
  return (
    [.localGet addressLocal,
      .i32Load .uint32 (u32 headerRefCountOffset),
      .localSet refCountLocal,
      .localGet refCountLocal] ++
    equalsConst .uint32 0 ++
    [.ifElse
      [.unreachable]
      ([.i32Const .uint32 1,
        .localGet refCountLocal,
        .i32LtU,
        .ifElse
          decrementAboveOneBody
          ([.localGet addressLocal,
            .call (.declaration releaseHeaderName)] ++ owned)])])

private def persistentReleaseBody : List Instruction :=
  [.localGet kindLocal] ++
  equalsConst .uint32 ObjectKind.natural.code ++
  [.ifElse
    ([.localGet addressLocal,
      .i32Load .uint32 (u32 headerAux0Offset)] ++
      equalsConst .uint32 promotedTagMarker ++
      [.ifElse checkedNoop [.ret]])
    [.ret]]

private def liveReleaseBody
    (descriptors : Array (Array AbiKind)) :
    Except LinkError (List Instruction) := do
  let ordinary ← ordinaryReleaseBody descriptors
  return (
    [.localGet addressLocal,
      .i32Load .uint32 (u32 headerKindOffset),
      .localSet kindLocal,
      .localGet addressLocal,
      .i32Load .uint32 (u32 headerAux0Offset),
      .localSet markerLocal,
      .localGet addressLocal,
      .i32Load .uint32 (u32 headerAux1Offset),
      .localSet countLocal,
      .localGet addressLocal,
      .i32Load .uint32 (u32 headerAux2Offset),
      .localSet captureCountLocal,
      .localGet addressLocal,
      .i32Load .uint32 (u32 headerAux3Offset),
      .localSet descriptorLocal,
      .localGet addressLocal,
      .i32Load .uint32 (u32 headerFlagsOffset),
      .i32Const .uint32 persistentFlag,
      .i32And] ++
    equalsConst .uint32 persistentFlag ++
    [.ifElse persistentReleaseBody ordinary])

private def alignedReleaseBody
    (descriptors : Array (Array AbiKind)) :
    Except LinkError (List Instruction) := do
  let live ← liveReleaseBody descriptors
  return (
    [.localGet objectParam,
      .i32Const .uint32 0,
      .i32Add,
      .localSet addressLocal,
      .localGet addressLocal,
      .i32Load .uint32 (u32 headerFlagsOffset),
      .i32Const .uint32 liveFlag,
      .i32And] ++
    equalsConst .uint32 liveFlag ++
    [.ifElse live [.unreachable]])

private def decrementOnceFunction
    (descriptors : Array (Array AbiKind)) :
    Except LinkError Function := do
  if UInt32.size ≤ descriptors.size then
    throw (.descriptorOverflow descriptors.size)
  let aligned ← alignedReleaseBody descriptors
  return {
    name := decrementOnceName
    params := #[(objectParam, .tobject), (checkParam, .uint32)]
    results := #[]
    locals := #[
      (addressLocal, .uint32),
      (kindLocal, .uint32),
      (countLocal, .uint32),
      (captureCountLocal, .uint32),
      (descriptorLocal, .uint32),
      (refCountLocal, .uint32),
      (markerLocal, .uint32),
      (arrayCursorLocal, .uint32),
      (arrayIndexLocal, .uint32)]
    body :=
      [.localGet objectParam,
        .i32Const .uint32 1,
        .i32And,
        .ifElse
          checkedNoop
          ([.localGet objectParam] ++
            equalsConst .tobject 0 ++
            [.ifElse
              checkedNoop
              ([.localGet objectParam,
                .i32Const .uint32 (u32 (target.heapAlignment - 1)),
                .i32And] ++
                equalsConst .uint32 0 ++
                [.ifElse aligned [.unreachable]])])] }

private def decrementWrapper (ordinal amount : Nat) (check : Bool) :
    Except LinkError Function := do
  let _ ← checkedWord amount
  let call :=
    [.localGet objectParam,
      .i32Const .uint32 (if check then 1 else 0),
      .call (.declaration decrementOnceName)]
  return {
    name := releaseName ordinal
    params := #[(objectParam, .tobject)]
    results := #[]
    locals := #[]
    body := (List.replicate amount call).flatten ++ [.ret] }

private def deleteReleasedBody : List Instruction :=
  [.localGet addressLocal,
    .call (.declaration releaseHeaderName),
    .ret]

private def deleteLiveBody : List Instruction :=
  [.localGet addressLocal,
    .i32Load .uint32 (u32 headerKindOffset)] ++
  equalsConst .uint32 ObjectKind.natural.code ++
  [.ifElse
    ([.localGet addressLocal,
      .i32Load .uint32 (u32 headerFlagsOffset),
      .i32Const .uint32 persistentFlag,
      .i32And] ++
      equalsConst .uint32 persistentFlag ++
      [.ifElse
        ([.localGet addressLocal,
          .i32Load .uint32 (u32 headerAux0Offset)] ++
          equalsConst .uint32 promotedTagMarker ++
          [.ifElse [.unreachable] deleteReleasedBody])
        deleteReleasedBody])
    deleteReleasedBody]

private def deleteAlignedBody : List Instruction :=
  [.localGet objectParam,
    .i32Const .uint32 0,
    .i32Add,
    .localSet addressLocal,
    .localGet addressLocal,
    .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 liveFlag,
    .i32And] ++
  equalsConst .uint32 liveFlag ++
  [.ifElse deleteLiveBody [.unreachable]]

private def deleteWrapper (ordinal : Nat) : Function := {
  name := releaseName ordinal
  params := #[(objectParam, .object)]
  results := #[]
  locals := #[(addressLocal, .uint32)]
  body :=
    [.localGet objectParam] ++
    equalsConst .object 0 ++
    [.ifElse
      [.ret]
      ([.localGet objectParam,
        .i32Const .uint32 1,
        .i32And,
        .ifElse
          [.unreachable]
          ([.localGet objectParam,
            .i32Const .uint32 (u32 (target.heapAlignment - 1)),
            .i32And] ++
            equalsConst .uint32 0 ++
            [.ifElse deleteAlignedBody [.unreachable]])])] }

private def operationFunction (ordinal : Nat) (operation : RuntimeOp) :
    Except LinkError Function :=
  match operation with
  | .dec amount check _ => decrementWrapper ordinal amount check
  | .delete => pure (deleteWrapper ordinal)
  | _ => throw .unsupportedOperation

private partial def rewriteInstruction
    (rewrites : List (RuntimeOp × Name)) : Instruction → Instruction
  | .call (.runtime candidate) =>
      match rewrites.find? (·.1 == candidate) with
      | some (_, name) => .call (.declaration name)
      | none => .call (.runtime candidate)
  | .block label body =>
      .block label (body.map (rewriteInstruction rewrites))
  | .ifElse thenBody elseBody =>
      .ifElse
        (thenBody.map (rewriteInstruction rewrites))
        (elseBody.map (rewriteInstruction rewrites))
  | instruction => instruction

private def rewriteFunction (rewrites : List (RuntimeOp × Name))
    (function : Function) : Function :=
  { function with body := function.body.map (rewriteInstruction rewrites) }

private def reserved (module : Module) (name : Name) : Bool :=
  module.imports.any (·.declaration? == some name) ||
    module.functions.any (·.name == name) ||
    module.exports.contains name

/--
Internalize recursive `dec` and nonrecursive `delete`. Parent headers are
marked freed before descending into constructor fields or statically described
closure captures, so cycles fail on a dead header rather than recurring.
-/
def internalizeReleases (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let operations := module.runtimeOperations.filter isRelease
  let rewrites := operations.toList.zipIdx.map fun (operation, ordinal) =>
    (operation, releaseName ordinal)
  let reservedNames :=
    releaseHeaderName :: decrementOnceName :: rewrites.map (·.2)
  if let some name := reservedNames.find? (reserved module) then
    throw (.reservedDeclaration name)
  let decrementOnce ← decrementOnceFunction module.closureDescriptors
  let wrappers ← operations.toList.zipIdx.mapM fun (operation, ordinal) =>
    operationFunction ordinal operation
  let functions :=
    (module.functions.map (rewriteFunction rewrites)) ++
      #[releaseHeaderFunction, decrementOnce] ++ wrappers.toArray
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
  let exports := rewrites.foldl (init := module.exports)
    fun exports (_, name) => Fir.Wasm.addUnique exports name
  let result := {
    module with
    imports
    functions
    exports
    runtimeOperations }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

def exampleDescriptors : Array (Array AbiKind) :=
  #[#[.tobject, .uint8, .tobject]]

def exampleOperations : Array RuntimeOp := #[
  .dec 1 true none,
  .dec 1 false (some 2),
  .delete]

def exampleCheckedCaller : Function := {
  name := `resident_dec_checked
  params := #[(objectParam, .tobject)]
  results := #[]
  locals := #[]
  body := [
    .localGet objectParam,
    .call (.runtime exampleOperations[0]!),
    .ret] }

def exampleUncheckedCaller : Function := {
  name := `resident_dec_unchecked
  params := #[(objectParam, .tobject)]
  results := #[]
  locals := #[]
  body := [
    .localGet objectParam,
    .call (.runtime exampleOperations[1]!),
    .ret] }

def exampleDeleteCaller : Function := {
  name := `resident_delete
  params := #[(objectParam, .object)]
  results := #[]
  locals := #[]
  body := [
    .localGet objectParam,
    .call (.runtime exampleOperations[2]!),
    .ret] }

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport
  functions := #[
    exampleCheckedCaller,
    exampleUncheckedCaller,
    exampleDeleteCaller]
  exports := #[
    exampleCheckedCaller.name,
    exampleUncheckedCaller.name,
    exampleDeleteCaller.name]
  initializers := #[]
  runtimeOperations := exampleOperations
  closureDescriptors := exampleDescriptors
  memory := some ResidentRuntime.residentMemory }

def residentExampleModule : Except String Module :=
  internalizeReleases exampleModule
    |>.mapError fun error => s!"releases: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr #[
      Json.mkObj [("entry", exampleCheckedCaller.name.toString)],
      Json.mkObj [("entry", exampleUncheckedCaller.name.toString)],
      Json.mkObj [("entry", exampleDeleteCaller.name.toString)]]),
    ("constructorFieldLimit", constructorFieldLimit),
    ("closureDescriptors", Json.arr <|
      exampleDescriptors.map fun descriptor =>
        Json.arr (descriptor.map fun kind => Json.str (toString (repr kind)))),
    ("status", "generation-only; W6 recursive-release contract proof pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      module.exports.contains exampleCheckedCaller.name &&
      module.exports.contains exampleUncheckedCaller.name &&
      module.exports.contains exampleDeleteCaller.name &&
      module.closureDescriptors == exampleDescriptors &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentRelease
