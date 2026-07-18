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

def closureCaptureAddress (base index : Nat) : Nat :=
  base + headerBytes + target.semanticSlotBytes * index

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

def LinearMemory.readClosureCapture (memory : LinearMemory) (address : Nat)
    (kind : AbiKind) : Except MemoryError LaneValue := do
  match kind.valueType with
  | .i32 =>
      let word ← memory.readWord32 address
      let padding ← memory.readUInt32 (address + 4)
      unless padding == 0 do
        throw (.nonzeroPadding (address + 4) padding.toNat)
      return .word32 word
  | .i64 => return .word64 (← memory.readUInt64 address)
  | .f32 =>
      let bits ← memory.readUInt32 address
      let padding ← memory.readUInt32 (address + 4)
      unless padding == 0 do
        throw (.nonzeroPadding (address + 4) padding.toNat)
      return .float32Bits bits
  | .f64 => return .float64Bits (← memory.readUInt64 address)

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
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (captures : Array LaneValue) : Except ConcreteError (MemoryState × Word32) := do
  unless captureKinds.size = captures.size do
    throw (.target (.closureCaptureCountMismatch captureKinds.size captures.size))
  unless captures.size < arity do
    throw (.target .closureMetadataMismatch)
  let targetId ← closureTargetId dispatch function
  let arityField ← uint32Field "closure arity" arity
  let fixedField ← uint32Field "closure fixed count" captures.size
  let layout := ClosureLayout.ofCaptures captureKinds
  let (state, address) ← liftMemory <|
    state.allocateObject .closure (layout.allocationBytes - headerBytes) false
      targetId arityField fixedField 0
  let memory ← liftMemory <| state.memory.writeClosureCaptures address.value 0
    (captureKinds.toList.zip captures.toList)
  return ({ state with memory }, address)

/-- Decoded and validated closure control metadata. Capture kinds remain
operation-specific static data supplied by the generated trampoline. -/
structure ClosureMetadata where
  header : Header
  targetId : UInt32
  function : Lean.Name
  arity : Nat
  fixed : Nat
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
  unless header.aux3 == 0 && fixed < arity &&
      requiredBytes ≤ header.allocationBytes.toNat do
    throw (.target .closureMetadataMismatch)
  return header

def readClosureMetadata (state : MemoryState) (dispatch : ClosureDispatchTable)
    (object : Word32) : Except ConcreteError ClosureMetadata := do
  let header ← readClosureHeader state object
  let some function := dispatch.lookup? header.aux0 |
    throw (.target (.unknownClosureTargetId header.aux0))
  return {
    header
    targetId := header.aux0
    function
    arity := header.aux1.toNat
    fixed := header.aux2.toNat }

def closureMatches (state : MemoryState) (dispatch : ClosureDispatchTable)
    (object : Word32) (function : Lean.Name) (arity fixed : Nat) :
    Except ConcreteError UInt32 := do
  let metadata ← readClosureMetadata state dispatch object
  return if metadata.function == function && metadata.arity == arity &&
      metadata.fixed == fixed then 1 else 0

def projectClosureCapture (state : MemoryState) (dispatch : ClosureDispatchTable)
    (object : Word32) (function : Lean.Name) (arity fixed index : Nat)
    (kind : AbiKind) : Except ConcreteError LaneValue := do
  let metadata ← readClosureMetadata state dispatch object
  unless metadata.function == function && metadata.arity == arity &&
      metadata.fixed == fixed do
    throw (.target .closureMetadataMismatch)
  unless index < fixed do
    throw (.target (.closureCaptureIndexOutOfBounds index fixed))
  liftMemory <| state.memory.readClosureCapture
    (closureCaptureAddress object.value index) kind

end Fir.Wasm.Concrete
