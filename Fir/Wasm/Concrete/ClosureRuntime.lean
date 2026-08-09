import Fir.Wasm.Concrete.Runtime

namespace Fir.Wasm.Concrete

/-- Deterministic generated-function order used by closure headers. The
linear-memory object stores only the `UInt32` index; proofs recover the stable
source name through this table. -/
abbrev ClosureDispatchTable := Array Lean.Name

def ClosureDispatchTable.resolve? (table : ClosureDispatchTable)
    (function : Lean.Name) : Option Nat :=
  table.findIdx? (· == function)

def ClosureDispatchTable.lookup? (table : ClosureDispatchTable)
    (id : UInt32) : Option Lean.Name :=
  table[id.toNat]?

def closureTargetId (table : ClosureDispatchTable) (function : Lean.Name) :
    Except ConcreteError UInt32 := do
  let some index := table.resolve? function |
    throw (.target (.unknownClosureTarget function))
  uint32Field "closure target id" index

def closureDescriptorId (table : ClosureDescriptorTable)
    (descriptor : Array AbiKind) : Except ConcreteError UInt32 := do
  let some index := table.resolve? descriptor |
    throw (.target (.unknownClosureDescriptor descriptor))
  uint32Field "closure capture descriptor id" index

/-- Write one typed physical capture into its fixed eight-byte slot. Narrow
lanes occupy the low word and require canonical zero padding. -/
def LinearMemory.writeClosureCapture (memory : LinearMemory) (address : Nat)
    (kind : AbiKind) (value : LaneValue) : Except MemoryError LinearMemory :=
  match kind.valueType, value with
  | .i32, .word32 word => do
      let memory ← memory.writeWord32 address word
      memory.writeUInt32 (address + 4) 0
  | .i64, .word64 word => memory.writeUInt64 address word
  | .f32, .float32Bits bits => do
      let memory ← memory.writeUInt32 address bits
      memory.writeUInt32 (address + 4) 0
  | .f64, .float64Bits bits => memory.writeUInt64 address bits
  | expected, actual =>
      .error (.closureCaptureKindMismatch expected actual.valueType)

def LinearMemory.writeClosureCaptures (memory : LinearMemory) (base index : Nat) :
    List (AbiKind × LaneValue) → Except MemoryError LinearMemory
  | [] => .ok memory
  | (kind, value) :: rest => do
      let memory ← memory.writeClosureCapture
        (closureCaptureAddress base index) kind value
      memory.writeClosureCaptures base (index + 1) rest

/-- Allocate a concrete closure. Header auxiliaries are target id, total
arity, fixed-capture count, and reserved zero; captures follow in typed
eight-byte slots. -/
def allocateClosure (state : MemoryState) (dispatch : ClosureDispatchTable)
    (descriptors : ClosureDescriptorTable)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (captures : Array LaneValue) : Except ConcreteError (MemoryState × Word32) := do
  unless captureKinds.size = captures.size do
    throw (.target (.closureCaptureCountMismatch captureKinds.size captures.size))
  unless captures.size < arity do
    throw (.target .closureMetadataMismatch)
  let targetId ← closureTargetId dispatch function
  let descriptorId ← closureDescriptorId descriptors captureKinds
  let arityField ← uint32Field "closure arity" arity
  let fixedField ← uint32Field "closure fixed count" captures.size
  let layout := ClosureLayout.ofCaptures captureKinds
  let (state, address) ← liftMemory <|
    state.allocateObject .closure (layout.allocationBytes - headerBytes) false
      targetId arityField fixedField descriptorId
  let memory ← liftMemory <| state.memory.writeClosureCaptures address.value 0
    (captureKinds.toList.zip captures.toList)
  return ({ state with memory }, address)

/-- Decoded and validated closure control metadata. Capture kinds remain
operation-specific static data supplied by the generated trampoline. -/
structure ClosureMetadata where
  header : Header
  targetId : UInt32
  descriptorId : UInt32
  function : Lean.Name
  arity : Nat
  fixed : Nat
  captureKinds : Array AbiKind
  deriving Inhabited, BEq, Repr

def readClosureHeader (state : MemoryState) (object : Word32) :
    Except ConcreteError Header := do
  unless object.classify = .heap do
    throw (.source .expectedClosure)
  let header ← liftMemory <| state.readLiveHeader object
  unless header.kind == .closure do
    throw (.source .expectedClosure)
  let arity := header.aux1.toNat
  let fixed := header.aux2.toNat
  let requiredBytes :=
    align8 (headerBytes + target.semanticSlotBytes * fixed)
  unless fixed < arity &&
      requiredBytes ≤ header.allocationBytes.toNat do
    throw (.target .closureMetadataMismatch)
  return header

def readClosureMetadata (state : MemoryState) (dispatch : ClosureDispatchTable)
    (descriptors : ClosureDescriptorTable) (object : Word32) :
    Except ConcreteError ClosureMetadata := do
  let header ← readClosureHeader state object
  let some function := dispatch.lookup? header.aux0 |
    throw (.target (.unknownClosureTargetId header.aux0))
  let some captureKinds := descriptors.lookup? header.aux3 |
    throw (.target (.unknownClosureDescriptorId header.aux3))
  unless captureKinds.size == header.aux2.toNat do
    throw (.target .closureMetadataMismatch)
  return {
    header
    targetId := header.aux0
    descriptorId := header.aux3
    function
    arity := header.aux1.toNat
    fixed := header.aux2.toNat
    captureKinds }

def closureMatches (state : MemoryState) (dispatch : ClosureDispatchTable)
    (descriptors : ClosureDescriptorTable) (object : Word32)
    (function : Lean.Name) (arity fixed : Nat) :
    Except ConcreteError UInt32 := do
  let metadata ← readClosureMetadata state dispatch descriptors object
  return if metadata.function == function && metadata.arity == arity &&
      metadata.fixed == fixed then 1 else 0

def projectClosureCapture (state : MemoryState) (dispatch : ClosureDispatchTable)
    (descriptors : ClosureDescriptorTable) (object : Word32)
    (function : Lean.Name) (arity fixed index : Nat) (kind : AbiKind) :
    Except ConcreteError LaneValue := do
  let metadata ← readClosureMetadata state dispatch descriptors object
  unless metadata.function == function && metadata.arity == arity &&
      metadata.fixed == fixed do
    throw (.target .closureMetadataMismatch)
  unless index < fixed do
    throw (.target (.closureCaptureIndexOutOfBounds index fixed))
  let some actualKind := metadata.captureKinds[index]? |
    throw (.target .closureMetadataMismatch)
  unless actualKind.refines kind do
    throw (.target .closureMetadataMismatch)
  liftMemory <| state.memory.readClosureCapture
    (closureCaptureAddress object.value index) actualKind

/-- Snapshot every statically typed closure capture before application may
release the closure header. Unlike the ownership decoder, this retains scalar
lanes because the generated projection prefix must still transfer them to the
callee. -/
def readClosureCaptures (state : MemoryState) (object : Word32)
    (index : Nat) : List AbiKind → Except ConcreteError (List LaneValue)
  | [] => .ok []
  | kind :: rest => do
      let lane ← liftMemory <| state.memory.readClosureCapture
        (closureCaptureAddress object.value index) kind
      let lanes ← readClosureCaptures state object (index + 1) rest
      return lane :: lanes

/-- Captures transferred by one successful concrete closure application.
The snapshot outlives an exclusive closure's released header and is the sole
source used by the immediately following generated projection prefix. -/
structure ClosureApplication where
  object : Word32
  function : Lean.Name
  arity : Nat
  captureKinds : Array AbiKind
  captures : Array LaneValue

/-- Retain one already-typed owned capture during closure application.
Physical zero is the erased value and therefore transfers no heap ownership;
ordinary `incrementReference` remains strict for standalone increment calls. -/
def retainClosureCapture (state : MemoryState) (object : Word32) :
    Except ConcreteError MemoryState :=
  if object == Word32.zero then .ok state
  else incrementReference state object 1 true

@[simp] theorem retainClosureCapture_zero (state : MemoryState) :
    retainClosureCapture state Word32.zero = .ok state := by
  unfold retainClosureCapture
  rw [if_pos (by decide)]

/-- Consume one concrete closure reference and snapshot its transferred fixed
arguments. An exclusive closure installs the canonical released header without
recursively releasing captures. A shared closure decrements the parent and
retains every statically owning capture. Persistent closures are unchanged. -/
def takeClosureApplication (state : MemoryState)
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (object : Word32) :
    Except ConcreteError (MemoryState × ClosureApplication) := do
  let metadata ← readClosureMetadata state dispatch descriptors object
  let captures ← readClosureCaptures state object 0 metadata.captureKinds.toList
  let application : ClosureApplication := {
    object
    function := metadata.function
    arity := metadata.arity
    captureKinds := metadata.captureKinds
    captures := captures.toArray }
  if metadata.header.persistent then
    return (state, application)
  if metadata.header.refCount == 0 then
    throw (.sourceAddress (.referenceCountUnderflow object))
  if metadata.header.refCount == 1 then
    let state ← deleteObject state object
    return (state, application)
  let owned ← readClosureOwnedReferences state object 0
    metadata.captureKinds.toList
  let state ← decrementReferenceOnce state object true descriptors
  let state ← owned.foldlM (init := state) fun state child =>
    retainClosureCapture state child
  return (state, application)

/-- Project one typed capture from a previously taken application snapshot.
This is independent of the closure's current live-header state. -/
def ClosureApplication.project (application : ClosureApplication)
    (object : Word32) (function : Lean.Name) (arity fixed index : Nat)
    (kind : AbiKind) : Except ConcreteError LaneValue := do
  unless application.object == object && application.function == function &&
      application.arity == arity && application.captures.size == fixed do
    throw (.target .closureMetadataMismatch)
  unless index < fixed do
    throw (.target (.closureCaptureIndexOutOfBounds index fixed))
  let some actualKind := application.captureKinds[index]? |
    throw (.target .closureMetadataMismatch)
  unless actualKind.refines kind do
    throw (.target .closureMetadataMismatch)
  let some lane := application.captures[index]? |
    throw (.target .closureMetadataMismatch)
  return lane

end Fir.Wasm.Concrete
