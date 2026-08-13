import Fir.Wasm.Emit.ResidentAllocator

namespace Fir.Wasm.Emit.ResidentScalarBox

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean
open Lean.Compiler

/-!
# Wasm-resident small scalar boxing

Lean 4.33 represents boxed small integers through the generic tagged path.
FIR's `wasm32-lean64` contract preserves that source representation: payloads
that fit wasm32 are immediate words and larger semantic tags are persistent
promoted-tag objects. This helper family implements the exact operations
needed by compiler-generated boxed wrappers without adding host imports.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | reservedDeclaration (name : Name)
  | missingExternal (name : Name)
  | incompatibleExternal (name : Name)
  | unsupportedOperation
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def valueParam : FVarId := ⟨`value⟩
private def objectParam : FVarId := ⟨`object⟩
private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def raw64Local : FVarId := ⟨`raw64⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def taggedResultLocal : FVarId := ⟨`taggedResult⟩
private def uint8ResultLocal : FVarId := ⟨`uint8Result⟩
private def uint16ResultLocal : FVarId := ⟨`uint16Result⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def addressLocal : FVarId := ⟨`address⟩

def boxUInt8Name : Name := `fir_box_uint8
def boxUInt16Name : Name := `fir_box_uint16
def boxUInt32Name : Name := `fir_box_uint32
def boxUInt64Name : Name := `fir_box_uint64
def unboxUInt8Name : Name := `fir_unbox_uint8
def unboxUInt16Name : Name := `fir_unbox_uint16
def unboxUInt32Name : Name := `fir_unbox_uint32
def unboxUInt64Name : Name := `fir_unbox_uint64
def uint32DecEqName : Name := `fir_ext_UInt32_decEq

def externalDeclarations : Array Name := #[`UInt32.decEq]

def helperNames : Array Name :=
  #[boxUInt8Name, boxUInt16Name, boxUInt32Name, boxUInt64Name,
    unboxUInt8Name, unboxUInt16Name, unboxUInt32Name, unboxUInt64Name,
    uint32DecEqName]

private def equalsConst (kind : AbiKind) (value : UInt32) : List Instruction :=
  [.i32Const kind value, .i32Eq]

private def trapUnless (condition : List Instruction) : List Instruction :=
  condition ++ [.ifElse [] [.unreachable]]

private def retypeRaw (result : AbiKind) (resultLocal : FVarId) : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet rawLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load result 0,
  .localSet resultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet resultLocal,
  .ret]

/-- Upstream `lean_box` specialized to the complete `UInt8` range. -/
def boxUInt8Function : Function := {
  name := boxUInt8Name
  params := #[(valueParam, .uint8)]
  results := #[.tagged]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (taggedResultLocal, .tagged)]
  body := [
    .localGet valueParam,
    .localGet valueParam,
    .i32Add,
    .i32Const .uint32 1,
    .i32Add,
    .localSet rawLocal] ++
    retypeRaw .tagged taggedResultLocal }

/-- Upstream `lean_box` specialized to the complete `UInt16` range. -/
def boxUInt16Function : Function := {
  name := boxUInt16Name
  params := #[(valueParam, .uint16)]
  results := #[.tobject]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (objectResultLocal, .tobject)]
  body := [
    .localGet valueParam,
    .localGet valueParam,
    .i32Add,
    .i32Const .uint32 1,
    .i32Add,
    .localSet rawLocal] ++
    retypeRaw .tobject objectResultLocal }

/-- Upstream `lean_unbox` specialized to a tagged `UInt8`. -/
def unboxUInt8Function : Function := {
  name := unboxUInt8Name
  params := #[(objectParam, .tobject)]
  results := #[.uint8]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (uint8ResultLocal, .uint8)]
  body :=
    trapUnless ([.localGet objectParam, .i32Const .uint32 1, .i32And] ++
      equalsConst .uint32 1) ++ [
      .localGet objectParam,
      .i32Const .uint32 1,
      .i32ShrU,
      .localSet rawLocal] ++
    trapUnless ([.localGet rawLocal, .i32Const .uint32 0xffffff00, .i32And] ++
      equalsConst .uint32 0) ++
    retypeRaw .uint8 uint8ResultLocal }

/-- Upstream `lean_unbox` specialized to a tagged `UInt16`. -/
def unboxUInt16Function : Function := {
  name := unboxUInt16Name
  params := #[(objectParam, .tobject)]
  results := #[.uint16]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (uint16ResultLocal, .uint16)]
  body :=
    trapUnless ([.localGet objectParam, .i32Const .uint32 1, .i32And] ++
      equalsConst .uint32 1) ++ [
      .localGet objectParam,
      .i32Const .uint32 1,
      .i32ShrU,
      .localSet rawLocal] ++
    trapUnless ([.localGet rawLocal, .i32Const .uint32 0xffff0000, .i32And] ++
      equalsConst .uint32 0) ++
    retypeRaw .uint16 uint16ResultLocal }

private def requireHeapAddress : List Instruction :=
  trapUnless ([.localGet objectParam, .i32Const .uint32 (u32 heapBase),
    .i32LtU] ++ equalsConst .uint32 0) ++
  trapUnless ([.localGet objectParam,
    .i32Const .uint32 (u32 (target.heapAlignment - 1)), .i32And] ++
    equalsConst .uint32 0)

private def requireHeaderWord (offset : Nat) (value : UInt32) : List Instruction :=
  trapUnless ([.localGet objectParam, .i32Load .uint32 (u32 offset)] ++
    equalsConst .uint32 value)

private def promotedUInt32Body : List Instruction :=
  requireHeapAddress ++
    trapUnless ([.localGet objectParam, .i32Load .uint32 (u32 headerFlagsOffset),
      .i32Const .uint32 (liveFlag + persistentFlag), .i32And] ++
      equalsConst .uint32 (liveFlag + persistentFlag)) ++
    requireHeaderWord headerKindOffset ObjectKind.natural.code ++
    requireHeaderWord headerAllocationBytesOffset (u32 40) ++
    requireHeaderWord headerAux0Offset promotedTagMarker ++
    requireHeaderWord headerAux1Offset 1 ++
    requireHeaderWord headerAux2Offset 0 ++
    requireHeaderWord headerAux3Offset 0 ++ [
      .localGet objectParam,
      .i64Load .uint64 (u32 headerBytes),
      .localSet raw64Local] ++
    trapUnless ([.localGet raw64Local, .i64Const .uint64 32, .i64ShrU,
      .i32WrapI64 .uint32] ++ equalsConst .uint32 0) ++ [
      .localGet raw64Local,
      .i32WrapI64 .uint32,
      .ret]

private def immediateUInt32Body : List Instruction := [
  .localGet objectParam,
  .i32Const .uint32 1,
  .i32ShrU,
  .ret]

/-- Decode the immediate or promoted-tag representation of a boxed `UInt32`. -/
def unboxUInt32Function : Function := {
  name := unboxUInt32Name
  params := #[(objectParam, .tobject)]
  results := #[.uint32]
  locals := #[(raw64Local, .uint64)]
  body := [
    .localGet objectParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse immediateUInt32Body promotedUInt32Body] }

private def storeAddress32 (value : List Instruction) (byteOffset : Nat) :
    List Instruction :=
  [.localGet addressLocal] ++ value ++ [.i32Store .uint32 (u32 byteOffset)]

private def storeAddress64 (value : List Instruction) (byteOffset : Nat) :
    List Instruction :=
  [.localGet addressLocal] ++ value ++ [.i64Store .uint64 (u32 byteOffset)]

private def promotedUInt32BoxBody : List Instruction :=
  [.i32Const .uint32 40,
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++
  storeAddress32 [.i32Const .uint32 ObjectKind.natural.code]
    headerKindOffset ++
  storeAddress32 [.i32Const .uint32 (liveFlag + persistentFlag)]
    headerFlagsOffset ++
  storeAddress32 [.i32Const .uint32 0] headerRefCountOffset ++
  storeAddress32 [.i32Const .uint32 40] headerAllocationBytesOffset ++
  storeAddress32 [.i32Const .uint32 promotedTagMarker] headerAux0Offset ++
  storeAddress32 [.i32Const .uint32 1] headerAux1Offset ++
  storeAddress32 [.i32Const .uint32 0] headerAux2Offset ++
  storeAddress32 [.i32Const .uint32 0] headerAux3Offset ++
  storeAddress32 [.localGet valueParam] headerBytes ++
  storeAddress32 [.i32Const .uint32 0] (headerBytes + 4) ++ [
    .localGet addressLocal,
    .localSet rawLocal] ++
  retypeRaw .tobject objectResultLocal

private def immediateUInt32BoxBody : List Instruction := [
  .localGet valueParam,
  .localGet valueParam,
  .i32Add,
  .i32Const .uint32 1,
  .i32Add,
  .localSet rawLocal] ++ retypeRaw .tobject objectResultLocal

/--
Upstream's integer box split adapted to FIR's wasm32 object lane. Values that
fit the physical immediate payload are encoded directly; the remaining
semantic tagged `UInt32` values use the canonical persistent promoted-natural
layout.
-/
def boxUInt32Function : Function := {
  name := boxUInt32Name
  params := #[(valueParam, .uint32)]
  results := #[.tobject]
  locals := #[(rawLocal, .uint32), (addressLocal, .uint32),
    (savedScratchLocal, .uint32), (objectResultLocal, .tobject)]
  body := [
    .localGet valueParam,
    .i32Const .uint32 2147483648,
    .i32LtU,
    .ifElse immediateUInt32BoxBody promotedUInt32BoxBody] }

private def immediateUInt64BoxBody : List Instruction := [
  .localGet valueParam,
  .i32WrapI64 .uint32,
  .localSet rawLocal,
  .localGet rawLocal,
  .localGet rawLocal,
  .i32Add,
  .i32Const .uint32 1,
  .i32Add,
  .localSet rawLocal] ++ retypeRaw .tobject objectResultLocal

private def promotedUInt64BoxBody : List Instruction :=
  [.i32Const .uint32 40,
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++
  storeAddress32 [.i32Const .uint32 ObjectKind.natural.code]
    headerKindOffset ++
  storeAddress32 [.i32Const .uint32 (liveFlag + persistentFlag)]
    headerFlagsOffset ++
  storeAddress32 [.i32Const .uint32 0] headerRefCountOffset ++
  storeAddress32 [.i32Const .uint32 40] headerAllocationBytesOffset ++
  storeAddress32 [.i32Const .uint32 promotedTagMarker] headerAux0Offset ++
  storeAddress32 [.i32Const .uint32 1] headerAux1Offset ++
  storeAddress32 [.i32Const .uint32 0] headerAux2Offset ++
  storeAddress32 [.i32Const .uint32 0] headerAux3Offset ++
  storeAddress64 [.localGet valueParam] headerBytes ++ [
    .localGet addressLocal,
    .localSet rawLocal] ++
  retypeRaw .tobject objectResultLocal

private def heapUInt64BoxBody : List Instruction :=
  [.i32Const .uint32 40,
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++
    storeAddress32 [.i32Const .uint32 ObjectKind.boxed.code]
      headerKindOffset ++
    storeAddress32 [.i32Const .uint32 liveFlag] headerFlagsOffset ++
    storeAddress32 [.i32Const .uint32 1] headerRefCountOffset ++
    storeAddress32 [.i32Const .uint32 40] headerAllocationBytesOffset ++
    storeAddress32 [.i32Const .uint32 BoxedScalarKind.uint64.code]
      headerAux0Offset ++
    storeAddress32 [.i32Const .uint32 8] headerAux1Offset ++
    storeAddress32 [.i32Const .uint32 0] headerAux2Offset ++
    storeAddress32 [.i32Const .uint32 0] headerAux3Offset ++
    storeAddress64 [.localGet valueParam] headerBytes ++ [
      .localGet addressLocal,
      .localSet rawLocal] ++
    retypeRaw .tobject objectResultLocal

/-- Lean's generic scalar box split: wasm32 immediate, persistent promoted
semantic tag, or ordinary refcounted box above the 63-bit tagged limit. -/
def boxUInt64Function : Function := {
  name := boxUInt64Name
  params := #[(valueParam, .uint64)]
  results := #[.tobject]
  locals := #[(rawLocal, .uint32), (addressLocal, .uint32),
    (savedScratchLocal, .uint32), (objectResultLocal, .tobject)]
  body := [
    .localGet valueParam,
    .i64Const .uint64 0x80000000,
    .i64LtU,
    .ifElse immediateUInt64BoxBody [
      .localGet valueParam,
      .i64Const .uint64 0x8000000000000000,
      .i64LtU,
      .ifElse promotedUInt64BoxBody heapUInt64BoxBody]] }

private def immediateUInt64Body : List Instruction := [
  .localGet objectParam,
  .i32Const .uint32 1,
  .i32ShrU,
  .i64ExtendI32U .uint64,
  .ret]

private def promotedUInt64Body : List Instruction :=
  trapUnless ([.localGet objectParam, .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 (liveFlag + persistentFlag), .i32And] ++
    equalsConst .uint32 (liveFlag + persistentFlag)) ++
  requireHeaderWord headerAllocationBytesOffset 40 ++
  requireHeaderWord headerAux0Offset promotedTagMarker ++
  requireHeaderWord headerAux1Offset 1 ++
  requireHeaderWord headerAux2Offset 0 ++
  requireHeaderWord headerAux3Offset 0 ++ [
    .localGet objectParam,
    .i64Load .uint64 (u32 headerBytes),
    .ret]

private def heapUInt64Body : List Instruction :=
  trapUnless ([.localGet objectParam, .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 liveFlag, .i32And] ++ equalsConst .uint32 liveFlag) ++
  requireHeaderWord headerAllocationBytesOffset 40 ++
  requireHeaderWord headerAux0Offset BoxedScalarKind.uint64.code ++
  requireHeaderWord headerAux1Offset 8 ++
  requireHeaderWord headerAux2Offset 0 ++
  requireHeaderWord headerAux3Offset 0 ++ [
    .localGet objectParam,
    .i64Load .uint64 (u32 headerBytes),
    .ret]

/-- Decode every canonical UInt64 box representation. -/
def unboxUInt64Function : Function := {
  name := unboxUInt64Name
  params := #[(objectParam, .tobject)]
  results := #[.uint64]
  locals := #[]
  body := [
    .localGet objectParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse immediateUInt64Body <| requireHeapAddress ++ [
      .localGet objectParam,
      .i32Load .uint32 (u32 headerKindOffset),
      .i32Const .uint32 ObjectKind.natural.code,
      .i32Eq,
      .ifElse promotedUInt64Body <|
        requireHeaderWord headerKindOffset ObjectKind.boxed.code ++
          heapUInt64Body]] }

/-- Upstream fixed-width equality is physical wasm32 equality. -/
def uint32DecEqFunction : Function := {
  name := uint32DecEqName
  params := #[(leftParam, .uint32), (rightParam, .uint32)]
  results := #[.uint8]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (uint8ResultLocal, .uint8)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i32Eq,
    .localSet rawLocal] ++ retypeRaw .uint8 uint8ResultLocal }

private def runtimeName? : RuntimeOp → Option Name
  | .box .uint8 .tagged => some boxUInt8Name
  | .box .uint16 .tobject => some boxUInt16Name
  | .box .uint32 .tobject => some boxUInt32Name
  | .box .uint64 .tobject => some boxUInt64Name
  | .unbox .uint8 => some unboxUInt8Name
  | .unbox .uint16 => some unboxUInt16Name
  | .unbox .uint32 => some unboxUInt32Name
  | .unbox .uint64 => some unboxUInt64Name
  | _ => none

private def runtimeFunction : RuntimeOp → Except LinkError Function
  | .box .uint8 .tagged => pure boxUInt8Function
  | .box .uint16 .tobject => pure boxUInt16Function
  | .box .uint32 .tobject => pure boxUInt32Function
  | .box .uint64 .tobject => pure boxUInt64Function
  | .unbox .uint8 => pure unboxUInt8Function
  | .unbox .uint16 => pure unboxUInt16Function
  | .unbox .uint32 => pure unboxUInt32Function
  | .unbox .uint64 => pure unboxUInt64Function
  | _ => throw .unsupportedOperation

private structure Binding where
  operation : RuntimeOp
  name : Name
  function : Function

private partial def rewriteInstruction (bindings : Array Binding) :
    Instruction → Instruction
  | .call (.declaration declaration) =>
      if externalDeclarations.contains declaration then
        .call (.declaration uint32DecEqName)
      else
        .call (.declaration declaration)
  | .call (.runtime operation) =>
      match bindings.find? (fun binding => binding.operation == operation) with
      | some binding => .call (.declaration binding.name)
      | none => .call (.runtime operation)
  | .block label body => .block label (body.map (rewriteInstruction bindings))
  | .loop label body => .loop label (body.map (rewriteInstruction bindings))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteInstruction bindings))
        (elseBody.map (rewriteInstruction bindings))
  | instruction => instruction

private def installBinding (functions : Array Function) (binding : Binding) :
    Except LinkError (Array Function) := do
  match functions.find? (·.name == binding.name) with
  | none => return functions.push binding.function
  | some existing =>
      unless existing == binding.function do
        throw (.reservedDeclaration binding.name)
      return functions

/-- Internalize an explicit dependency-closed set of small-scalar operations. -/
def internalizeOperations (module : Module) (operations : Array RuntimeOp)
    (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let presentExternal := module.imports.any
    (·.declaration? == some `UInt32.decEq)
  if presentExternal then
    if module.imports.any (·.declaration? == some uint32DecEqName) ||
        module.functions.any (·.name == uint32DecEqName) ||
        module.exports.contains uint32DecEqName then
      throw (.reservedDeclaration uint32DecEqName)
    let imports := module.imports.filter
      (·.declaration? == some `UInt32.decEq)
    unless imports.size == 1 do
      throw (.missingExternal `UInt32.decEq)
    unless imports[0]!.signature == {
        params := #[.uint32, .uint32], results := #[.uint8] } do
      throw (.incompatibleExternal `UInt32.decEq)
  let bindings ← operations.mapM fun operation => do
    let some name := runtimeName? operation |
      throw .unsupportedOperation
    if module.imports.any (·.declaration? == some name) then
      throw (.reservedDeclaration name)
    return { operation, name, function := ← runtimeFunction operation }
  let functions := module.functions.map fun function =>
    { function with body := function.body.map (rewriteInstruction bindings) }
  let functions ← bindings.foldlM (init := functions) installBinding
  let functions := if presentExternal then functions.push uint32DecEqFunction
    else functions
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter fun import_ =>
    import_.operation?.isNone &&
      !(presentExternal && import_.declaration? == some `UInt32.decEq)
  let exports := bindings.foldl
    (fun exports binding => Fir.Wasm.addUnique exports binding.name)
    module.exports
  let exports := if presentExternal then
    Fir.Wasm.addUnique exports uint32DecEqName
  else exports
  let result : Module := {
    module with
    functions
    runtimeOperations
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    exports }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

/-- Internalize exactly the supported small-scalar operations present. -/
def internalizeAvailable (module : Module) (validate : Bool := true) : Except LinkError Module :=
  internalizeOperations module
    (module.runtimeOperations.filter (runtimeName? · |>.isSome)) validate

private def roundtripName : Name := `resident_scalar_box_uint8_roundtrip
private def roundtripUInt16Name : Name := `resident_scalar_box_uint16_roundtrip
private def roundtripUInt32Name : Name := `resident_scalar_box_uint32_roundtrip
private def roundtripUInt64Name : Name := `resident_scalar_box_uint64_roundtrip
private def unboxUInt32ExampleName : Name := `resident_scalar_unbox_uint32

private def exampleOperations : Array RuntimeOp := #[
  .box .uint8 .tagged,
  .unbox .uint8,
  .unbox .uint32,
  .box .uint16 .tobject,
  .unbox .uint16,
  .box .uint32 .tobject,
  .box .uint64 .tobject,
  .unbox .uint64]

private def roundtripFunction : Function := {
  name := roundtripName
  params := #[(valueParam, .uint8)]
  results := #[.uint8]
  locals := #[]
  body := [.localGet valueParam, .call (.runtime exampleOperations[0]!),
    .call (.runtime exampleOperations[1]!), .ret] }

private def unboxUInt32ExampleFunction : Function := {
  name := unboxUInt32ExampleName
  params := #[(objectParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [.localGet objectParam, .call (.runtime exampleOperations[2]!), .ret] }

private def roundtripUInt16Function : Function := {
  name := roundtripUInt16Name
  params := #[(valueParam, .uint16)]
  results := #[.uint16]
  locals := #[]
  body := [.localGet valueParam, .call (.runtime exampleOperations[3]!),
    .call (.runtime exampleOperations[4]!), .ret] }

private def roundtripUInt32Function : Function := {
  name := roundtripUInt32Name
  params := #[(valueParam, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [.localGet valueParam, .call (.runtime exampleOperations[5]!),
    .call (.runtime exampleOperations[2]!), .ret] }

private def roundtripUInt64Function : Function := {
  name := roundtripUInt64Name
  params := #[(valueParam, .uint64)]
  results := #[.uint64]
  locals := #[]
  body := [.localGet valueParam, .call (.runtime exampleOperations[6]!),
    .call (.runtime exampleOperations[7]!), .ret] }

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport ++ #[{
    key := .external `UInt32.decEq
    moduleName := "lean.extern"
    itemName := "UInt32.decEq"
    signature := { params := #[.uint32, .uint32], results := #[.uint8] }
    externalTypes? := some {
      params := #[LCNF.ImpureType.uint32, LCNF.ImpureType.uint32]
      result := LCNF.ImpureType.uint8 } }]
  functions := #[roundtripFunction, unboxUInt32ExampleFunction,
    roundtripUInt16Function, roundtripUInt32Function, roundtripUInt64Function]
  exports := #[roundtripName, roundtripUInt16Name, roundtripUInt32Name,
    roundtripUInt64Name, unboxUInt32ExampleName]
  initializers := #[]
  runtimeOperations := exampleOperations
  memory := some ResidentRuntime.residentMemory }

def residentExampleModule : Except String Module := do
  let module ← ResidentAllocator.install exampleModule
    |>.mapError fun error => s!"allocator: {repr error}"
  internalizeAvailable module
    |>.mapError fun error => s!"scalar box: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr #[
      Json.mkObj [
        ("entry", roundtripName.toString),
        ("params", Json.arr #["uint8"]),
        ("result", "uint8")],
      Json.mkObj [
        ("entry", unboxUInt32ExampleName.toString),
        ("params", Json.arr #["tobject"]),
        ("result", "uint32")],
      Json.mkObj [
        ("entry", roundtripUInt16Name.toString),
        ("params", Json.arr #["uint16"]),
        ("result", "uint16")],
      Json.mkObj [
        ("entry", roundtripUInt32Name.toString),
        ("params", Json.arr #["uint32"]),
        ("result", "uint32")],
      Json.mkObj [
        ("entry", roundtripUInt64Name.toString),
        ("params", Json.arr #["uint64"]),
        ("result", "uint64")]]),
    ("helpers", Json.arr <| helperNames.map fun name => (name.toString : Json)),
    ("memory", "memory"),
    ("imports", Json.arr #[]),
    ("scratchAddress", 0),
    ("scratchPolicy", "saved-and-restored"),
    ("status", "generation-ready; W6 contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      module.functions.size ==
        5 + helperNames.size + ResidentAllocator.helperNames.size &&
      helperNames.all module.exports.contains &&
      (Fir.Wasm.validateModule module).isOk && (Fir.Wasm.Emit.encode module).isOk
  | .error _ => false

end Fir.Wasm.Emit.ResidentScalarBox
