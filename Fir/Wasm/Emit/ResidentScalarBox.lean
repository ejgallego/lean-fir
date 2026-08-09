import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentScalarBox

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

/-!
# Wasm-resident small scalar boxing

Lean 4.32 represents boxed small integers through the generic tagged path.
FIR's `wasm32-lean64` contract preserves that source representation: payloads
that fit wasm32 are immediate words and larger semantic tags are persistent
promoted-tag objects. This helper family implements the exact operations
needed by compiler-generated boxed wrappers without adding host imports.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def valueParam : FVarId := ⟨`value⟩
private def objectParam : FVarId := ⟨`object⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def raw64Local : FVarId := ⟨`raw64⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def taggedResultLocal : FVarId := ⟨`taggedResult⟩
private def uint8ResultLocal : FVarId := ⟨`uint8Result⟩

def boxUInt8Name : Name := `fir_box_uint8
def unboxUInt8Name : Name := `fir_unbox_uint8
def unboxUInt32Name : Name := `fir_unbox_uint32

def helperNames : Array Name := #[boxUInt8Name, unboxUInt8Name, unboxUInt32Name]

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

private def runtimeName? : RuntimeOp → Option Name
  | .box .uint8 .tagged => some boxUInt8Name
  | .unbox .uint8 => some unboxUInt8Name
  | .unbox .uint32 => some unboxUInt32Name
  | _ => none

private def runtimeFunction : RuntimeOp → Except LinkError Function
  | .box .uint8 .tagged => pure boxUInt8Function
  | .unbox .uint8 => pure unboxUInt8Function
  | .unbox .uint32 => pure unboxUInt32Function
  | _ => throw .unsupportedOperation

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

/-- Internalize exactly the supported small-scalar operations present. -/
def internalizeAvailable (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let operations := module.runtimeOperations.filter (runtimeName? · |>.isSome)
  let bindings ← operations.mapM fun operation => do
    let some name := runtimeName? operation |
      throw .unsupportedOperation
    if module.imports.any (·.declaration? == some name) then
      throw (.reservedDeclaration name)
    return { operation, name, function := ← runtimeFunction operation }
  let functions := module.functions.map fun function =>
    { function with body := function.body.map (rewriteInstruction bindings) }
  let functions ← bindings.foldlM (init := functions) installBinding
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let result : Module := {
    module with
    functions
    runtimeOperations
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    exports := bindings.foldl
      (fun exports binding => Fir.Wasm.addUnique exports binding.name)
      module.exports }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

private def roundtripName : Name := `resident_scalar_box_uint8_roundtrip
private def unboxUInt32ExampleName : Name := `resident_scalar_unbox_uint32

private def exampleOperations : Array RuntimeOp := #[
  .box .uint8 .tagged,
  .unbox .uint8,
  .unbox .uint32]

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

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport
  functions := #[roundtripFunction, unboxUInt32ExampleFunction]
  exports := #[roundtripName, unboxUInt32ExampleName]
  initializers := #[]
  runtimeOperations := exampleOperations
  memory := some ResidentRuntime.residentMemory }

def residentExampleModule : Except LinkError Module :=
  internalizeAvailable exampleModule

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
        ("result", "uint32")]]),
    ("helpers", Json.arr <| helperNames.map fun name => (name.toString : Json)),
    ("memory", "memory"),
    ("imports", Json.arr #[]),
    ("scratchAddress", 0),
    ("scratchPolicy", "saved-and-restored"),
    ("status", "generation-ready; W6 contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      module.functions.size == 5 &&
      helperNames.all module.exports.contains &&
      (Fir.Wasm.validateModule module).isOk && (Fir.Wasm.Emit.encode module).isOk
  | .error _ => false

end Fir.Wasm.Emit.ResidentScalarBox
