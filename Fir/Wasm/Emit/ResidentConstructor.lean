import Fir.Wasm.Emit.ResidentAllocator

namespace Fir.Wasm.Emit.ResidentConstructor

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

private def addressLocal : FVarId := ⟨`address⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def resultLocal : FVarId := ⟨`result⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | unsupportedImmediateTag (tag : Nat)
  | metadataOverflow (label : String) (value : Nat)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

def isConstructor : RuntimeOp → Bool
  | .allocCtor .. => true
  | _ => false

def constructorName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_alloc_ctor_{ordinal}"

private def fieldId (index : Nat) : FVarId :=
  ⟨Name.mkSimple s!"field_{index}"⟩

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

private def headerStores (info : Lean.Compiler.LCNF.CtorInfo)
    (allocationBytes : UInt32) : List Instruction :=
  store32 .uint32 [.i32Const .uint32 ObjectKind.constructor.code]
      (u32 headerKindOffset) ++
    store32 .uint32 [.i32Const .uint32 liveFlag]
      (u32 headerFlagsOffset) ++
    store32 .uint32 [.i32Const .uint32 1]
      (u32 headerRefCountOffset) ++
    store32 .uint32 [.i32Const .uint32 allocationBytes]
      (u32 headerAllocationBytesOffset) ++
    store32 .uint32 [.i32Const .uint32 (u32 info.cidx)]
      (u32 headerAux0Offset) ++
    store32 .uint32 [.i32Const .uint32 (u32 info.size)]
      (u32 headerAux1Offset) ++
    store32 .uint32 [.i32Const .uint32 (u32 info.usize)]
      (u32 headerAux2Offset) ++
    store32 .uint32 [.i32Const .uint32 (u32 info.ssize)]
      (u32 headerAux3Offset)

private def fieldStores (fields : Array AbiKind) : List Instruction :=
  fields.toList.zipIdx.flatMap fun (kind, index) =>
    store32 kind [.localGet (fieldId index)]
      (u32 (headerBytes + target.semanticSlotBytes * index))

/--
Retag one raw wasm32 address as the statically declared constructor result
without adding a shared symbolic cast instruction. Bytes below `heapBase` are
reserved by the resident heap contract. The helper nevertheless saves and
restores the scratch word exactly, so the conversion frames every memory byte.
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

def constructorFunction (ordinal : Nat) (operation : RuntimeOp) :
    Except LinkError Function := do
  let .allocCtor info fields result := operation |
    throw .unsupportedOperation
  unless operation.abiWellFormed do
    throw .unsupportedOperation
  let name := constructorName ordinal
  let params := fields.mapIdx fun index kind => (fieldId index, kind)
  if info.size = 0 && info.usize = 0 && info.ssize = 0 then
    unless info.cidx ≤ maxImmediatePayload do
      throw (.unsupportedImmediateTag info.cidx)
    let encoded ← checkedWord "immediate constructor tag" (info.cidx * 2 + 1)
    return {
      name
      params
      results := #[result]
      locals := #[]
      body := [.i32Const result encoded, .ret] }
  let layout := ConstructorLayout.ofInfo info
  let allocationBytes ← checkedWord "constructor allocation bytes" layout.allocationBytes
  let _ ← checkedWord "constructor tag" info.cidx
  let _ ← checkedWord "constructor object-field count" info.size
  let _ ← checkedWord "constructor usize-field count" info.usize
  let _ ← checkedWord "constructor scalar byte count" info.ssize
  return {
    name
    params
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
      headerStores info allocationBytes ++
      fieldStores fields ++
      retagAddress result }

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
  let name := constructorName ordinal
  if module.imports.any (·.declaration? == some name) ||
      module.functions.any (·.name == name) ||
      module.exports.contains name then
    throw (.reservedDeclaration name)
  let function ← constructorFunction ordinal operation
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
Internalize every constructor-allocation runtime operation after the resident
allocator has been installed. Each metadata-distinct compiler import gets one
helper; calls are rewritten to direct Wasm declarations and the runtime import
prefix is rebuilt from the remaining operations.
-/
def internalizeConstructors (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let operations := module.runtimeOperations.filter isConstructor
  let result ← operations.toList.zipIdx.foldlM (init := module)
    fun result (operation, ordinal) =>
      internalizeOne ordinal operation result
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

def exampleEmptyInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `ResidentConstructor.nil
  cidx := 0
  size := 0
  «usize» := 0
  ssize := 0 }

def examplePairInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `ResidentConstructor.pair
  cidx := 7
  size := 2
  «usize» := 1
  ssize := 3 }

def exampleOperations : Array RuntimeOp := #[
  .allocCtor exampleEmptyInfo #[] .tagged,
  .allocCtor examplePairInfo #[.tobject, .tobject] .object]

def exampleEmptyCaller : Function := {
  name := `resident_ctor_empty
  params := #[]
  results := #[.tagged]
  locals := #[]
  body := [.call (.runtime exampleOperations[0]!), .ret] }

def examplePairCaller : Function := {
  name := `resident_ctor_pair
  params := #[(fieldId 0, .tobject), (fieldId 1, .tobject)]
  results := #[.object]
  locals := #[]
  body := [
    .localGet (fieldId 0),
    .localGet (fieldId 1),
    .call (.runtime exampleOperations[1]!),
    .ret] }

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport
  functions := #[exampleEmptyCaller, examplePairCaller]
  exports := #[exampleEmptyCaller.name, examplePairCaller.name]
  initializers := #[]
  runtimeOperations := exampleOperations }

def residentExampleModule : Except String Module := do
  let allocated ← ResidentAllocator.install exampleModule
    |>.mapError fun error => s!"allocator: {repr error}"
  internalizeConstructors allocated
    |>.mapError fun error => s!"constructors: {repr error}"

def manifest (operations : Array RuntimeOp) : Json :=
  Json.mkObj [
    ("entries", Json.arr <| operations.mapIdx fun ordinal _operation =>
      Json.mkObj [
        ("entry", constructorName ordinal |>.toString)]),
    ("scratchAddress", 0),
    ("scratchPolicy", "saved-and-restored"),
    ("status", "generation-only; W6 constructor contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      module.functions.size ==
        2 + ResidentAllocator.helperNames.size + exampleOperations.size &&
      module.exports.contains exampleEmptyCaller.name &&
      module.exports.contains examplePairCaller.name &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentConstructor
