import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentAllocator

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

def frontierName : Name := `fir_heap_frontier
def setFrontierName : Name := `fir_heap_set_frontier
def rewindName : Name := `fir_heap_rewind
def allocateName : Name := `fir_heap_alloc
def store8Name : Name := `fir_heap_store8
def store16Name : Name := `fir_heap_store16
def store32Name : Name := `fir_heap_store32
def store64Name : Name := `fir_heap_store64

def helperNames : Array Name := #[
  frontierName,
  setFrontierName,
  rewindName,
  allocateName,
  store8Name,
  store16Name,
  store32Name,
  store64Name]

private def requestedBytes : FVarId := ⟨`requestedBytes⟩
private def address : FVarId := ⟨`address⟩
private def value32 : FVarId := ⟨`value32⟩
private def value64 : FVarId := ⟨`value64⟩
private def current : FVarId := ⟨`current⟩
private def allocationEnd : FVarId := ⟨`allocationEnd⟩
private def requiredPages : FVarId := ⟨`requiredPages⟩
private def currentPages : FVarId := ⟨`currentPages⟩
private def growResult : FVarId := ⟨`growResult⟩

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def trapWhenTrue (condition : List Instruction) : List Instruction :=
  condition ++ [.ifElse [.unreachable] []]

private def requireAligned (fvarId : FVarId) : List Instruction :=
  trapWhenTrue [
    .localGet fvarId,
    .i32Const .uint32 (u32 (target.heapAlignment - 1)),
    .i32And]

private def pagesForEnd (fvarId : FVarId) : List Instruction := [
  .localGet fvarId,
  .i32Const .uint32 1,
  .i32Sub,
  .i32Const .uint32 16,
  .i32ShrU,
  .i32Const .uint32 1,
  .i32Add]

def frontierFunction (frontierIndex : Nat) : Function := {
  name := frontierName
  params := #[]
  results := #[.uint32]
  locals := #[]
  body := [.globalGet frontierIndex .uint32, .ret] }

def setFrontierFunction (frontierIndex : Nat) : Function := {
  name := setFrontierName
  params := #[(address, .uint32)]
  results := #[]
  locals := #[
    (current, .uint32),
    (requiredPages, .uint32),
    (currentPages, .uint32)]
  body :=
    [.globalGet frontierIndex .uint32,
      .localSet current] ++
    trapWhenTrue [
      .localGet address,
      .localGet current,
      .i32LtU] ++
    trapWhenTrue [
      .localGet address,
      .i32Const .uint32 (u32 heapBase),
      .i32LtU] ++
    requireAligned address ++
    pagesForEnd address ++
    [.localSet requiredPages,
      .memorySize,
      .localSet currentPages] ++
    trapWhenTrue [
      .localGet currentPages,
      .localGet requiredPages,
      .i32LtU] ++
    [.localGet address,
      .globalSet frontierIndex .uint32,
      .ret] }

/--
Restores a previously observed aligned frontier without shrinking linear
memory. This is deliberately separate from `fir_heap_set_frontier`, whose
monotonic synchronization contract remains unchanged.
-/
def rewindFunction (frontierIndex : Nat) : Function := {
  name := rewindName
  params := #[(address, .uint32)]
  results := #[]
  locals := #[(current, .uint32)]
  body :=
    [.globalGet frontierIndex .uint32,
      .localSet current] ++
    trapWhenTrue [
      .localGet current,
      .localGet address,
      .i32LtU] ++
    trapWhenTrue [
      .localGet address,
      .i32Const .uint32 (u32 heapBase),
      .i32LtU] ++
    requireAligned address ++
    [.localGet address,
      .globalSet frontierIndex .uint32,
      .ret] }

def allocateFunction (frontierIndex : Nat) : Function := {
  name := allocateName
  params := #[(requestedBytes, .uint32)]
  results := #[.uint32]
  locals := #[
    (current, .uint32),
    (allocationEnd, .uint32),
    (requiredPages, .uint32),
    (currentPages, .uint32),
    (growResult, .uint32)]
  body :=
    trapWhenTrue [
      .localGet requestedBytes,
      .i32Const .uint32 (u32 headerBytes),
      .i32LtU] ++
    requireAligned requestedBytes ++
    [.globalGet frontierIndex .uint32,
      .localSet current] ++
    trapWhenTrue [
      .localGet current,
      .i32Const .uint32 (u32 heapBase),
      .i32LtU] ++
    requireAligned current ++
    [.localGet current,
      .localGet requestedBytes,
      .i32Add,
      .localSet allocationEnd] ++
    trapWhenTrue [
      .localGet allocationEnd,
      .localGet current,
      .i32LtU] ++
    pagesForEnd allocationEnd ++
    [.localSet requiredPages,
      .memorySize,
      .localSet currentPages,
      .localGet currentPages,
      .localGet requiredPages,
      .i32LtU,
      Instruction.ifElse
        ([.localGet requiredPages,
          .localGet currentPages,
          .i32Sub,
          .memoryGrow,
          .localSet growResult] ++ trapWhenTrue [
          .localGet growResult,
          .i32Const .uint32 4294967295,
          .i32Eq])
        [],
      .localGet allocationEnd,
      .globalSet frontierIndex .uint32,
      .localGet current,
      .ret] }

def store8Function : Function := {
  name := store8Name
  params := #[(address, .uint32), (value32, .uint8)]
  results := #[]
  locals := #[]
  body := [
    .localGet address,
    .localGet value32,
    .i32Store8 .uint8 0,
    .ret] }

def store16Function : Function := {
  name := store16Name
  params := #[(address, .uint32), (value32, .uint16)]
  results := #[]
  locals := #[]
  body := [
    .localGet address,
    .localGet value32,
    .i32Store16 .uint16 0,
    .ret] }

def store32Function : Function := {
  name := store32Name
  params := #[(address, .uint32), (value32, .uint32)]
  results := #[]
  locals := #[]
  body := [
    .localGet address,
    .localGet value32,
    .i32Store .uint32 0,
    .ret] }

def store64Function : Function := {
  name := store64Name
  params := #[(address, .uint32), (value64, .uint64)]
  results := #[]
  locals := #[]
  body := [
    .localGet address,
    .localGet value64,
    .i64Store .uint64 0,
    .ret] }

def functions (frontierIndex : Nat) : Array Function := #[
  frontierFunction frontierIndex,
  setFrontierFunction frontierIndex,
  rewindFunction frontierIndex,
  allocateFunction frontierIndex,
  store8Function,
  store16Function,
  store32Function,
  store64Function]

def allocatorModule : Module := {
  imports := #[]
  functions := functions 0
  exports := helperNames
  initializers := #[]
  runtimeOperations := #[]
  memory := some ResidentRuntime.residentMemory
  globals := #[{ kind := .uint32, init := .i32 (u32 heapBase) }] }

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | reservedDeclaration (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

/--
Install the low-level resident heap frontier, allocation primitive, and typed
raw stores without rewriting semantic runtime operations. The resident global
is appended after every lazy-cache global and prior resident global, so all
existing physical indices remain stable.
-/
def install (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  let memory ←
    match module.memory with
    | none => pure ResidentRuntime.residentMemory
    | some memory =>
        unless memory == ResidentRuntime.residentMemory do
          throw .incompatibleMemory
        pure memory
  for name in helperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) ||
        module.exports.contains name then
      throw (.reservedDeclaration name)
  let frontierIndex := module.cacheGlobalKinds.size + module.globals.size
  let result : Module := {
    module with
    functions := module.functions ++ functions frontierIndex
    exports := module.exports ++ helperNames
    memory := some memory
    globals := module.globals.push
      { kind := .uint32, init := .i32 (u32 heapBase) } }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <| helperNames.map fun name => (name.toString : Json)),
    ("memory", "memory"),
    ("heapBase", heapBase),
    ("alignment", target.heapAlignment),
    ("minimumAllocationBytes", headerBytes),
    ("imports", Json.arr #[]),
    ("status", "generation-only; W6 allocator contract proof pending")]

#guard allocatorModule.imports.isEmpty
#guard allocatorModule.globals ==
  #[{ kind := .uint32, init := .i32 (u32 heapBase) }]
#guard allocatorModule.memory == some ResidentRuntime.residentMemory
#guard Fir.Wasm.validateModule allocatorModule |>.isOk
#guard Fir.Wasm.Emit.encode allocatorModule |>.isOk

end Fir.Wasm.Emit.ResidentAllocator
