import Fir.Wasm.Emit.Manifest
import Fir.Wasm.Emit.ResidentAllocator

namespace Fir.Wasm.Emit.ResidentClosureAllocation

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

private def addressLocal : FVarId := ⟨`address⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def resultLocal : FVarId := ⟨`result⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | missingClosureTarget (target : Name)
  | missingClosureDescriptor (descriptor : Array AbiKind)
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | unsupportedResult (result : AbiKind)
  | unsupportedCaptureKind (kind : AbiKind)
  | metadataOverflow (label : String) (value : Nat)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

def isPartialApplication : RuntimeOp → Bool
  | .partialApply .. => true
  | _ => false

def partialApplicationName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_alloc_closure_{ordinal}"

private def captureId (index : Nat) : FVarId :=
  ⟨Name.mkSimple s!"capture_{index}"⟩

private def checkedWord (label : String) (value : Nat) :
    Except LinkError UInt32 :=
  if value < UInt32.size then
    pure (u32 value)
  else
    throw (.metadataOverflow label value)

private def store32 (kind : AbiKind) (value : List Instruction)
    (offset : UInt32) : List Instruction :=
  [.localGet addressLocal] ++ value ++ [.i32Store kind offset]

private def zeroAllocation (allocationBytes : Nat) : List Instruction :=
  (List.range (allocationBytes / 4)).flatMap fun index =>
    store32 .uint32 [.i32Const .uint32 0] (u32 (4 * index))

private def headerStores (targetId arity fixed descriptorId allocationBytes : UInt32) :
    List Instruction :=
  store32 .uint32 [.i32Const .uint32 ObjectKind.closure.code]
      (u32 headerKindOffset) ++
    store32 .uint32 [.i32Const .uint32 liveFlag]
      (u32 headerFlagsOffset) ++
    store32 .uint32 [.i32Const .uint32 1]
      (u32 headerRefCountOffset) ++
    store32 .uint32 [.i32Const .uint32 allocationBytes]
      (u32 headerAllocationBytesOffset) ++
    store32 .uint32 [.i32Const .uint32 targetId]
      (u32 headerAux0Offset) ++
    store32 .uint32 [.i32Const .uint32 arity]
      (u32 headerAux1Offset) ++
    store32 .uint32 [.i32Const .uint32 fixed]
      (u32 headerAux2Offset) ++
    store32 .uint32 [.i32Const .uint32 descriptorId]
      (u32 headerAux3Offset)

private def captureStore (kind : AbiKind) (index : Nat) :
    Except LinkError (List Instruction) := do
  let offset := u32 (headerBytes + target.semanticSlotBytes * index)
  match kind.valueType with
  | .i32 =>
      return store32 kind [.localGet (captureId index)] offset
  | .i64 =>
      return [
        .localGet addressLocal,
        .localGet (captureId index),
        .i64Store kind offset]
  | .f32 | .f64 =>
      throw (.unsupportedCaptureKind kind)

private def captureStores (fields : Array AbiKind) :
    Except LinkError (List Instruction) := do
  let stores ← fields.toList.zipIdx.mapM fun (kind, index) =>
    captureStore kind index
  return stores.flatten

/--
Retag one raw wasm32 address as the statically declared object-like result.
The scratch word below `heapBase` is saved and restored exactly.
-/
private def retagAddress (result : AbiKind) : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet addressLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load result 0,
  .localSet resultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet resultLocal,
  .ret]

def partialApplicationFunction (module : Module) (ordinal : Nat)
    (operation : RuntimeOp) : Except LinkError Function := do
  let .partialApply targetName arity fixed fields result := operation |
    throw .unsupportedOperation
  unless operation.abiWellFormed do
    throw .unsupportedOperation
  unless result == .object || result == .tobject do
    throw (.unsupportedResult result)
  let some targetIndex := module.closureDispatch.findIdx? (· == targetName) |
    throw (.missingClosureTarget targetName)
  let some descriptorIndex := module.closureDescriptors.findIdx? (· == fields) |
    throw (.missingClosureDescriptor fields)
  let targetId ← checkedWord "closure target id" targetIndex
  let descriptorId ← checkedWord "closure descriptor id" descriptorIndex
  let arityField ← checkedWord "closure arity" arity
  let fixedField ← checkedWord "closure fixed count" fixed
  let layout := ClosureLayout.ofCaptures fields
  let allocationBytes ← checkedWord "closure allocation bytes" layout.allocationBytes
  let stores ← captureStores fields
  return {
    name := partialApplicationName ordinal
    params := fields.mapIdx fun index kind => (captureId index, kind)
    results := #[result]
    locals := #[
      (addressLocal, .uint32),
      (savedScratchLocal, .uint32),
      (resultLocal, result)]
    body :=
      [.i32Const .uint32 allocationBytes,
        .call (.declaration ResidentAllocator.allocateName),
        .localSet addressLocal] ++
      zeroAllocation layout.allocationBytes ++
      headerStores targetId arityField fixedField descriptorId allocationBytes ++
      stores ++
      retagAddress result }

private structure Binding where
  operation : RuntimeOp
  name : Name
  function : Function

private partial def rewriteInstruction (bindings : Array Binding) :
    Instruction → Instruction
  | .call (.runtime operation) =>
      match bindings.find? (fun binding => binding.operation == operation) with
      | some binding => .call (.declaration binding.name)
      | none => .call (.runtime operation)
  | .block label body =>
      .block label (body.map (rewriteInstruction bindings))
  | .loop label body =>
      .loop label (body.map (rewriteInstruction bindings))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteInstruction bindings))
        (elseBody.map (rewriteInstruction bindings))
  | instruction => instruction

private def installBinding (functions : Array Function) (binding : Binding) :
    Except LinkError (Array Function) := do
  if functions.any (·.name == binding.name) then
    throw (.reservedDeclaration binding.name)
  return functions.push binding.function

/--
Internalize every supported closure allocation after the resident allocator is
installed. Stable target and capture-layout IDs come only from the retained
module tables; removing runtime imports cannot renumber either header field.

Float captures fail closed until the symbolic resident surface gains typed
float stores. The current text and styled `prettyM` closures use only i32
captures, while the standalone fixture also covers an i64 slot.
-/
def internalizePartialApplications (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let operations := module.runtimeOperations.filter isPartialApplication
  let bindings ← operations.toList.zipIdx.toArray.mapM fun (operation, ordinal) => do
    let name := partialApplicationName ordinal
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) || module.exports.contains name then
      throw (.reservedDeclaration name)
    let function ← partialApplicationFunction module ordinal operation
    return { operation, name, function : Binding }
  let functions := module.functions.map fun function =>
    { function with body := function.body.map (rewriteInstruction bindings) }
  let functions ← bindings.foldlM (init := functions) installBinding
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let result : Module := {
    module with
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    functions
    exports := bindings.foldl
      (fun exports binding => Fir.Wasm.addUnique exports binding.name)
      module.exports
    runtimeOperations }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

def exampleUnrelatedTarget : Name := `ResidentClosureAllocation.unrelated
def exampleTarget : Name := `ResidentClosureAllocation.target

def exampleOperations : Array RuntimeOp := #[
  .partialApply exampleTarget 3 0 #[] .object,
  .partialApply exampleTarget 4 3 #[.tobject, .uint8, .usize] .tobject]

def exampleClosureDispatch : Array Name := #[
  exampleUnrelatedTarget,
  exampleTarget]

def exampleClosureDescriptors : Array (Array AbiKind) := #[
  #[.uint32],
  #[],
  #[.tobject, .uint8, .usize]]

def exampleEmptyCaller : Function := {
  name := `resident_closure_empty
  params := #[]
  results := #[.object]
  locals := #[]
  body := [.call (.runtime exampleOperations[0]!), .ret] }

def exampleCapturedCaller : Function := {
  name := `resident_closure_captured
  params := #[
    (captureId 0, .tobject),
    (captureId 1, .uint8),
    (captureId 2, .usize)]
  results := #[.tobject]
  locals := #[]
  body := [
    .localGet (captureId 0),
    .localGet (captureId 1),
    .localGet (captureId 2),
    .call (.runtime exampleOperations[1]!),
    .ret] }

def exampleLoopCaller : Function := {
  name := `resident_closure_inside_loop
  params := #[]
  results := #[.object]
  locals := #[]
  body := [
    .loop ⟨`residentClosureLoop⟩ [
      .call (.runtime exampleOperations[0]!),
      .ret],
    .unreachable] }

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport
  functions := #[exampleEmptyCaller, exampleCapturedCaller, exampleLoopCaller]
  exports := #[exampleEmptyCaller.name, exampleCapturedCaller.name,
    exampleLoopCaller.name]
  initializers := #[]
  runtimeOperations := exampleOperations
  closureDispatch := exampleClosureDispatch
  closureDescriptors := exampleClosureDescriptors }

def residentExampleModule : Except String Module := do
  let allocated ← ResidentAllocator.install exampleModule
    |>.mapError fun error => s!"allocator: {repr error}"
  internalizePartialApplications allocated
    |>.mapError fun error => s!"partial applications: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <| exampleOperations.mapIdx fun ordinal _operation =>
      Json.mkObj [
        ("entry", partialApplicationName ordinal |>.toString)]),
    ("closureDispatch", Json.arr <|
      exampleClosureDispatch.map fun name => (name.toString : Json)),
    ("closureDescriptors", Json.arr <|
      exampleClosureDescriptors.map Fir.Wasm.Emit.Manifest.abiKindsJson),
    ("scratchAddress", 0),
    ("scratchPolicy", "saved-and-restored"),
    ("status", "generation-only; W6 closure-allocation contract proof pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      module.functions.size ==
        3 + ResidentAllocator.helperNames.size + exampleOperations.size &&
      module.exports.contains exampleEmptyCaller.name &&
      module.exports.contains exampleCapturedCaller.name &&
      module.exports.contains exampleLoopCaller.name &&
      module.closureDispatch == exampleClosureDispatch &&
      module.closureDescriptors == exampleClosureDescriptors &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentClosureAllocation
