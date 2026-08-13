import Fir.Wasm.Emit.Manifest
import Fir.Wasm.Emit.ResidentAllocator

namespace Fir.Wasm.Emit.ResidentClosureAllocation

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

private def addressLocal : FVarId := ⟨`address⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def resultLocal : FVarId := ⟨`result⟩
private def targetIdLocal : FVarId := ⟨`targetId⟩
private def arityLocal : FVarId := ⟨`arity⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | missingClosureTarget (target : Name)
  | missingClosureDescriptor (descriptor : Array AbiKind)
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | unsupportedResult (result : AbiKind)
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

private def headerStores (fixed descriptorId allocationBytes : UInt32) :
    List Instruction :=
  store32 .uint32 [.i32Const .uint32 ObjectKind.closure.code]
      (u32 headerKindOffset) ++
    store32 .uint32 [.i32Const .uint32 liveFlag]
      (u32 headerFlagsOffset) ++
    store32 .uint32 [.i32Const .uint32 1]
      (u32 headerRefCountOffset) ++
    store32 .uint32 [.i32Const .uint32 allocationBytes]
      (u32 headerAllocationBytesOffset) ++
    store32 .uint32 [.localGet targetIdLocal]
      (u32 headerAux0Offset) ++
    store32 .uint32 [.localGet arityLocal]
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
  | .f32 =>
      return [
        .localGet addressLocal,
        .localGet (captureId index),
        .i32ReinterpretF32 .uint32,
        .i32Store .uint32 offset]
  | .f64 =>
      return [
        .localGet addressLocal,
        .localGet (captureId index),
        .i64ReinterpretF64 .uint64,
        .i64Store .uint64 offset]

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

private structure HelperKey where
  fields : Array AbiKind
  result : AbiKind
  deriving BEq, Hashable

private def helperKey? : RuntimeOp → Option HelperKey
  | .partialApply _ _ _ fields result => some { fields, result }
  | _ => none

private def collectHelperKeys (operations : Array RuntimeOp) : Array HelperKey :=
  let initial : Array HelperKey × Std.HashSet HelperKey :=
    (#[], Std.HashSet.emptyWithCapacity operations.size)
  (operations.foldl (init := initial) fun (keys, seen) operation =>
      match helperKey? operation with
      | none => (keys, seen)
      | some key =>
          if seen.contains key then (keys, seen)
          else (keys.push key, seen.insert key)).1

/-- Number of typed resident helpers needed for a partial-application inventory. -/
def partialApplicationHelperCount (operations : Array RuntimeOp) : Nat :=
  (collectHelperKeys operations).size

/-- Stable first-shape-order helper names for a partial-application inventory. -/
def partialApplicationHelperNames (operations : Array RuntimeOp) : Array Name :=
  (collectHelperKeys operations).mapIdx fun ordinal _ => partialApplicationName ordinal

private def partialApplicationFunctionForKey
    (descriptorIndices : Std.HashMap (Array AbiKind) Nat) (ordinal : Nat)
    (key : HelperKey) : Except LinkError Function := do
  let { fields, result } := key
  unless result.isObjectLike do
    throw (.unsupportedResult result)
  let some descriptorIndex := descriptorIndices.get? fields |
    throw (.missingClosureDescriptor fields)
  let descriptorId ← checkedWord "closure descriptor id" descriptorIndex
  let fixedField ← checkedWord "closure fixed count" fields.size
  let layout := ClosureLayout.ofCaptures fields
  let allocationBytes ← checkedWord "closure allocation bytes" layout.allocationBytes
  let stores ← captureStores fields
  return {
    name := partialApplicationName ordinal
    params := (fields.mapIdx fun index kind => (captureId index, kind)) ++ #[
      (targetIdLocal, .uint32),
      (arityLocal, .uint32)]
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
      headerStores fixedField descriptorId allocationBytes ++
      stores ++
      retagAddress result }

def partialApplicationFunction (module : Module) (ordinal : Nat)
    (operation : RuntimeOp) : Except LinkError Function := do
  let .partialApply targetName _arity _fixed _fields _result := operation |
    throw .unsupportedOperation
  unless operation.abiWellFormed do
    throw .unsupportedOperation
  unless module.closureDispatch.contains targetName do
    throw (.missingClosureTarget targetName)
  let some key := helperKey? operation |
    throw .unsupportedOperation
  let descriptorIndices := module.closureDescriptors.mapIdx
    (fun index descriptor => (descriptor, index))
    |>.foldl (init := Std.HashMap.emptyWithCapacity module.closureDescriptors.size)
      fun indices entry => indices.insert entry.1 entry.2
  partialApplicationFunctionForKey descriptorIndices ordinal key

private structure Binding where
  key : HelperKey
  name : Name
  function : Function

private structure RewriteBinding where
  name : Name
  targetId : UInt32
  arity : UInt32

mutual
  private partial def rewriteInstructions
      (bindings : Std.HashMap RuntimeOp RewriteBinding) :
      List Instruction → List Instruction
    | instructions => instructions.flatMap (rewriteInstruction bindings)

  private partial def rewriteInstruction
      (bindings : Std.HashMap RuntimeOp RewriteBinding) :
      Instruction → List Instruction
    | .call (.runtime operation) =>
        match bindings.get? operation with
        | some binding => [
            .i32Const .uint32 binding.targetId,
            .i32Const .uint32 binding.arity,
            .call (.declaration binding.name)]
        | none => [.call (.runtime operation)]
    | .block label body =>
        [.block label (rewriteInstructions bindings body)]
    | .loop label body =>
        [.loop label (rewriteInstructions bindings body)]
    | .ifElse thenBody elseBody =>
        [.ifElse (rewriteInstructions bindings thenBody)
          (rewriteInstructions bindings elseBody)]
    | instruction => [instruction]
end

/--
Internalize supported closure allocations after the resident allocator is
installed. Calls with the same typed capture/result shape share one allocator
helper; each call site supplies its stable target ID and arity, while the helper
retains the statically checked capture layout and descriptor. Removing runtime
imports therefore cannot renumber either header field.

Scalar captures are stored bit-exactly in the same fixed eight-byte slots as
object values. Floating lanes use the symbolic reinterpret operations before
the existing integer stores, so this helper does not introduce a second
physical closure layout.
-/
def internalizePartialApplications (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let operations := module.runtimeOperations.filter isPartialApplication
  let targetIndices := module.closureDispatch.mapIdx (fun index name => (name, index))
    |>.foldl (init := Std.HashMap.emptyWithCapacity module.closureDispatch.size)
      fun indices entry => indices.insert entry.1 entry.2
  let descriptorIndices := module.closureDescriptors.mapIdx
    (fun index descriptor => (descriptor, index))
    |>.foldl (init := Std.HashMap.emptyWithCapacity module.closureDescriptors.size)
      fun indices entry => indices.insert entry.1 entry.2
  let importedDeclarations := module.imports.foldl
    (init := Std.HashSet.emptyWithCapacity module.imports.size)
    fun declarations import_ =>
      match import_.declaration? with
      | some name => declarations.insert name
      | none => declarations
  let functionNames := module.functions.foldl
    (init := Std.HashSet.emptyWithCapacity (module.functions.size + operations.size))
    fun names function => names.insert function.name
  let exportedNames := module.exports.foldl
    (init := Std.HashSet.emptyWithCapacity (module.exports.size + operations.size))
    fun names name => names.insert name
  let keys := collectHelperKeys operations
  let bindings ← keys.mapIdxM fun ordinal key => do
    let name := partialApplicationName ordinal
    if importedDeclarations.contains name || functionNames.contains name ||
        exportedNames.contains name then
      throw (.reservedDeclaration name)
    let function ← partialApplicationFunctionForKey descriptorIndices ordinal key
    return { key, name, function : Binding }
  let helperNames := bindings.foldl
    (init := Std.HashMap.emptyWithCapacity bindings.size)
    fun names binding => names.insert binding.key binding.name
  let rewrites ← operations.foldlM
      (init := Std.HashMap.emptyWithCapacity operations.size) fun rewrites operation => do
    let .partialApply targetName arity _fixed _fields _result := operation |
      throw .unsupportedOperation
    unless operation.abiWellFormed do
      throw .unsupportedOperation
    let some targetIndex := targetIndices.get? targetName |
      throw (.missingClosureTarget targetName)
    let some key := helperKey? operation |
      throw .unsupportedOperation
    let some name := helperNames.get? key |
      throw .unsupportedOperation
    let targetId ← checkedWord "closure target id" targetIndex
    let arity ← checkedWord "closure arity" arity
    return rewrites.insert operation { name, targetId, arity }
  let functions := module.functions.map fun function =>
    { function with body := rewriteInstructions rewrites function.body }
  let functions := functions ++ bindings.map (·.function)
  let runtimeOperations := Fir.Wasm.updateRuntimeOps module.runtimeOperations operations
    (bindings.map (·.function))
  let externalImports := module.imports.filter (·.operation?.isNone)
  let result : Module := {
    module with
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    functions
    exports := module.exports ++ bindings.map (·.name)
    runtimeOperations }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

def exampleUnrelatedTarget : Name := `ResidentClosureAllocation.unrelated
def exampleTarget : Name := `ResidentClosureAllocation.target

def exampleOperations : Array RuntimeOp := #[
  .partialApply exampleTarget 3 0 #[] .object,
  .partialApply exampleTarget 4 3 #[.tobject, .uint8, .usize] .tobject,
  .partialApply exampleTarget 3 2 #[.float32, .float] .object,
  .partialApply exampleTarget 3 0 #[] .tagged,
  .partialApply exampleUnrelatedTarget 5 0 #[] .object]

def exampleClosureDispatch : Array Name := #[
  exampleUnrelatedTarget,
  exampleTarget]

def exampleClosureDescriptors : Array (Array AbiKind) := #[
  #[.uint32],
  #[],
  #[.tobject, .uint8, .usize],
  #[.float32, .float]]

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

def exampleFloatCaller : Function := {
  name := `resident_closure_float_captured
  params := #[(captureId 0, .float32), (captureId 1, .float)]
  results := #[.object]
  locals := #[]
  body := [
    .localGet (captureId 0),
    .localGet (captureId 1),
    .call (.runtime exampleOperations[2]!),
    .ret] }

/-- Lean's generic object-family calling convention may retain a `tagged`
annotation for a closure value. It is still the raw address of the allocated
heap closure in the shared i32 object lane. -/
def exampleTaggedCaller : Function := {
  name := `resident_closure_tagged
  params := #[]
  results := #[.tagged]
  locals := #[]
  body := [.call (.runtime exampleOperations[3]!), .ret] }

/-- A different target and arity with the same empty/object helper shape. -/
def exampleSharedShapeCaller : Function := {
  name := `resident_closure_shared_shape
  params := #[]
  results := #[.object]
  locals := #[]
  body := [.call (.runtime exampleOperations[4]!), .ret] }

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport
  functions := #[exampleEmptyCaller, exampleCapturedCaller, exampleLoopCaller,
    exampleFloatCaller, exampleTaggedCaller, exampleSharedShapeCaller]
  exports := #[exampleEmptyCaller.name, exampleCapturedCaller.name,
    exampleLoopCaller.name, exampleFloatCaller.name, exampleTaggedCaller.name,
    exampleSharedShapeCaller.name]
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
    ("entries", Json.arr <| partialApplicationHelperNames exampleOperations |>.map fun name =>
      Json.mkObj [
        ("entry", name.toString)]),
    ("operationCount", exampleOperations.size),
    ("helperCount", partialApplicationHelperCount exampleOperations),
    ("sharingPolicy", "typed-capture-and-result-shape"),
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
        6 + ResidentAllocator.helperNames.size +
          partialApplicationHelperCount exampleOperations &&
      partialApplicationHelperCount exampleOperations == 4 &&
      module.exports.contains exampleEmptyCaller.name &&
      module.exports.contains exampleCapturedCaller.name &&
      module.exports.contains exampleLoopCaller.name &&
      module.exports.contains exampleFloatCaller.name &&
      module.exports.contains exampleTaggedCaller.name &&
      module.exports.contains exampleSharedShapeCaller.name &&
      (partialApplicationHelperNames exampleOperations).all
        module.exports.contains &&
      module.closureDispatch == exampleClosureDispatch &&
      module.closureDescriptors == exampleClosureDescriptors &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

#guard match residentExampleModule with
  | .ok module =>
      match module.functions.find? fun function =>
          function.name == partialApplicationName 0 with
      | some helper =>
          helper.params == #[(targetIdLocal, .uint32), (arityLocal, .uint32)]
      | none => false
  | .error _ => false

end Fir.Wasm.Emit.ResidentClosureAllocation
