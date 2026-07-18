import Fir.Wasm.Concrete.Memory

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Concrete execution keeps source-semantic failures distinct from checked
memory/target failures, matching the W2 structured-trap boundary. -/
inductive ConcreteAddressFault where
  | referenceCountUnderflow (address : Word32)
  deriving BEq, Repr

/-- Failures introduced by the generated mutable-global boundary rather than
by FIR evaluation or linear-memory decoding. -/
inductive ConcreteGlobalError where
  | unknownGlobal (name : Lean.Name)
  | kindMismatch (name : Lean.Name) (expected actual : AbiKind)
  | uninitializedGlobal (name : Lean.Name)
  deriving BEq, Repr

inductive ConcreteError where
  | source (fault : RuntimeFault)
  | sourceAddress (fault : ConcreteAddressFault)
  | target (failure : MemoryError)
  | targetGlobal (failure : ConcreteGlobalError)
  deriving BEq, Repr

/-- Source-origin failures before address representations are translated back
through the refinement witness. -/
inductive ConcreteSourceFailure where
  | runtime (fault : RuntimeFault)
  | address (fault : ConcreteAddressFault)
  deriving BEq, Repr

/-- Backend-only failures have no corresponding successful source step. -/
inductive ConcreteTargetFailure where
  | memory (failure : MemoryError)
  | global (failure : ConcreteGlobalError)
  deriving BEq, Repr

/-- Lossless structured trap boundary for the concrete runtime. The outer
constructor records whether the source program or target machinery failed;
the payload retains the complete checked failure. -/
inductive ConcreteTrap where
  | source (failure : ConcreteSourceFailure)
  | target (failure : ConcreteTargetFailure)
  deriving BEq, Repr

def ConcreteError.toTrap : ConcreteError → ConcreteTrap
  | .source fault => .source (.runtime fault)
  | .sourceAddress fault => .source (.address fault)
  | .target failure => .target (.memory failure)
  | .targetGlobal failure => .target (.global failure)

def liftMemory {α : Type} : Except MemoryError α → Except ConcreteError α
  | .ok value => .ok value
  | .error failure => .error (.target failure)

/-- Checked conversion for object-header metadata.  It is public so operation
refinement proofs can expose the exact failure/success boundary. -/
def uint32Field (field : String) (value : Nat) : Except ConcreteError UInt32 :=
  if value < UInt32.size then
    .ok (UInt32.ofNat value)
  else
    .error (.target (.headerValueOverflow field value))

def promotedTagMarker : UInt32 := 1

def bigNaturalMarker : UInt32 := 2

/-- Allocate the persistent heap representation of a semantic tagged payload
that cannot fit in the wasm32 immediate word. -/
def allocatePromotedTag (state : MemoryState) (payload : UInt64) :
    Except ConcreteError (MemoryState × Word32) := do
  let (state, address) ← liftMemory <|
    state.allocateObject .natural 8 true promotedTagMarker 1
  let memory ← liftMemory <| state.memory.writeUInt64
    (address.value + headerBytes) payload
  return ({ state with memory }, address)

/-- Encode one semantic tagged payload. Payloads above the wasm32 immediate
range remain semantically tagged but receive a persistent natural allocation. -/
def encodeTagged (state : MemoryState) (payload : UInt64) :
    Except ConcreteError (MemoryState × Word32) :=
  if fits : payload.toNat ≤ maxImmediatePayload then
    .ok (state, Word32.encodeImmediate payload.toNat fits)
  else
    allocatePromotedTag state payload

/-- Decode the constructor/tag value represented by an immediate, a concrete
constructor, or a persistent promoted tag. Other heap naturals are not
constructors and preserve the source `expectedConstructor` failure. -/
def readTag (state : MemoryState) (word : Word32) : Except ConcreteError UInt64 := do
  match word.classify with
  | .immediate =>
      let some payload := word.decodeImmediate? |
        throw (.target (.invalidObjectAddress word))
      return UInt64.ofNat payload
  | .heap =>
      let header ← liftMemory <| state.readLiveHeader word
      if header.kind == .constructor then
        return UInt64.ofNat header.aux0.toNat
      else if header.kind == .natural && header.persistent &&
          header.aux0 == promotedTagMarker then
        liftMemory <| state.memory.readUInt64 (word.value + headerBytes)
      else
        throw (.source .expectedConstructor)
  | .sentinel | .invalid => throw (.source .expectedConstructor)

/-- Concrete, typed payload accepted by FIR integer boxing. This deliberately
excludes floats until the shared semantic runtime has float scalar values. -/
inductive BoxedScalar where
  | uint8 (value : UInt8)
  | uint16 (value : UInt16)
  | uint32 (value : UInt32)
  | uint64 (value : UInt64)
  | usize (value : UInt64)
  deriving Inhabited, BEq, Repr

def BoxedScalar.kind : BoxedScalar → BoxedScalarKind
  | .uint8 _ => .uint8
  | .uint16 _ => .uint16
  | .uint32 _ => .uint32
  | .uint64 _ => .uint64
  | .usize _ => .usize

def BoxedScalar.payload : BoxedScalar → UInt64
  | .uint8 value => value.toUInt64
  | .uint16 value => value.toUInt64
  | .uint32 value => value.toUInt64
  | .uint64 value | .usize value => value

def BoxedScalar.semanticValue : BoxedScalar → Value
  | .uint8 value => .scalar (.uint8 value)
  | .uint16 value => .scalar (.uint16 value)
  | .uint32 value => .scalar (.uint32 value)
  | .uint64 value => .scalar (.uint64 value)
  | .usize value => .usize value

def BoxedScalar.lane : BoxedScalar → LaneValue
  | .uint8 value => .word32 (Word32.ofUInt8 value)
  | .uint16 value => .word32 (Word32.ofUInt16 value)
  | .uint32 value => .word32 (Word32.ofUInt32 value)
  | .uint64 value | .usize value => .word64 value

def BoxedScalar.ofPayload : BoxedScalarKind → UInt64 → BoxedScalar
  | .uint8, payload => .uint8 payload.toUInt8
  | .uint16, payload => .uint16 payload.toUInt16
  | .uint32, payload => .uint32 payload.toUInt32
  | .uint64, payload => .uint64 payload
  | .usize, payload => .usize payload

@[simp] theorem BoxedScalar.kind_ofPayload (kind : BoxedScalarKind)
    (payload : UInt64) :
    (BoxedScalar.ofPayload kind payload).kind = kind := by
  cases kind <;> rfl

@[simp] theorem BoxedScalar.ofPayload_kind_payload (scalar : BoxedScalar) :
    BoxedScalar.ofPayload scalar.kind scalar.payload = scalar := by
  cases scalar <;> simp [BoxedScalar.kind, BoxedScalar.payload, BoxedScalar.ofPayload]

def BoxedScalarKind.semanticType : BoxedScalarKind → Lean.Expr
  | .uint8 => LCNF.ImpureType.uint8
  | .uint16 => LCNF.ImpureType.uint16
  | .uint32 => LCNF.ImpureType.uint32
  | .uint64 => LCNF.ImpureType.uint64
  | .usize => LCNF.ImpureType.usize

/-- Every concrete scalar lane carries exactly its semantic integer value at
the W6 ABI boundary. -/
theorem BoxedScalar.valueRel (witness : RefinementWitness) (scalar : BoxedScalar) :
    ValueRel witness scalar.kind.abiKind scalar.lane scalar.semanticValue := by
  cases scalar with
  | uint8 value => exact .uint8 rfl
  | uint16 value => exact .uint16 rfl
  | uint32 value => exact .uint32 rfl
  | uint64 value => exact .uint64
  | usize value => exact .usize

/-- Allocate one canonical heap-backed box. `boxScalar` calls this only above
FIR's semantic tagged limit; keeping it public exposes the exact allocation
and payload-write boundary to the refinement proof. -/
def allocateBoxedScalar (state : MemoryState) (scalar : BoxedScalar) :
    Except ConcreteError (MemoryState × Word32) := do
  let kind := scalar.kind
  let (state, address) ← liftMemory <|
    state.allocateObject .boxed target.semanticSlotBytes false kind.code
      (UInt32.ofNat kind.payloadBytes)
  let memory ← liftMemory <| state.memory.writeUInt64
    (address.value + headerBytes) scalar.payload
  return ({ state with memory }, address)

/-- Decode one checked heap-backed box. The stored kind, meaningful width,
reserved auxiliaries, allocation extent, and zero-extended payload must all be
canonical before the semantic scalar is reconstructed. -/
def readHeapBoxedScalar (state : MemoryState) (address : Word32) (header : Header) :
    Except ConcreteError BoxedScalar := do
  let some kind := BoxedScalarKind.ofCode? header.aux0 |
    throw (.target (.unknownBoxedScalarKind header.aux0))
  unless !header.persistent do
    throw (.target (.malformedBoxedHeader address.value))
  unless header.aux1 == UInt32.ofNat kind.payloadBytes do
    throw (.target (.malformedBoxedHeader address.value))
  unless header.aux2 == 0 && header.aux3 == 0 do
    throw (.target (.malformedBoxedHeader address.value))
  unless header.allocationBytes.toNat =
      align8 (headerBytes + target.semanticSlotBytes) do
    throw (.target (.malformedBoxedHeader address.value))
  let payload ← liftMemory <| state.memory.readUInt64 (address.value + headerBytes)
  let scalar := BoxedScalar.ofPayload kind payload
  unless scalar.payload == payload do
    throw (.target (.malformedBoxedHeader address.value))
  return scalar

theorem readHeapBoxedScalar_forAllocation
    (state : MemoryState) (address : Word32) (scalar : BoxedScalar)
    (payloadRead : state.memory.readUInt64 (address.value + headerBytes) =
      .ok scalar.payload) :
    readHeapBoxedScalar state address
      (Header.forAllocation .boxed
        (align8 (headerBytes + target.semanticSlotBytes)) false scalar.kind.code
          (UInt32.ofNat scalar.kind.payloadBytes)) = .ok scalar := by
  have payloadRead' :
      state.memory.readUInt64 (address.value + 32) = .ok scalar.payload := by
    simpa [headerBytes] using payloadRead
  unfold readHeapBoxedScalar
  simp [Header.forAllocation, target, headerBytes, align8, payloadRead']
  simp only [liftMemory, Bind.bind, Except.bind]
  rw [BoxedScalar.ofPayload_kind_payload]
  simp
  rfl

/-- Decode a semantic box result. Tagged values use the requested result kind,
matching `scalarFromType`; a heap-backed box returns its stored kind and value,
matching FIR's intentionally type-erased heap `unbox` branch. -/
def readBoxedScalar (state : MemoryState) (expected : BoxedScalarKind)
    (object : Word32) : Except ConcreteError BoxedScalar := do
  match object.classify with
  | .immediate =>
      let some payload := object.decodeImmediate? |
        throw (.target (.invalidObjectAddress object))
      return BoxedScalar.ofPayload expected (UInt64.ofNat payload)
  | .heap =>
      let header ← liftMemory <| state.readLiveHeader object
      if header.kind == .boxed then
        readHeapBoxedScalar state object header
      else if header.kind == .natural && header.persistent &&
          header.aux0 == promotedTagMarker then
        return BoxedScalar.ofPayload expected (← readTag state object)
      else
        throw (.source .expectedScalar)
  | .sentinel | .invalid => throw (.source .expectedObject)

/-- Checked concrete implementation of FIR's `isShared`. Tagged immediates
and persistent promoted tags are shared; ordinary heap objects are shared
exactly when persistent or not uniquely referenced. -/
def readIsShared (state : MemoryState) (object : Word32) :
    Except ConcreteError UInt8 := do
  match object.classify with
  | .immediate => return 1
  | .heap =>
      let header ← liftMemory <| state.readLiveHeader object
      return if header.persistent || header.refCount != 1 then 1 else 0
  | .sentinel | .invalid => throw (.source .expectedObject)

def Header.isPromotedTag (header : Header) : Bool :=
  header.kind == .natural && header.persistent &&
    header.aux0 == promotedTagMarker

/-- Replace one already-validated common header without changing the heap
frontier. Callers choose the updated mutable metadata. -/
def writeLiveHeader (state : MemoryState) (address : Word32) (header : Header) :
    Except ConcreteError MemoryState := do
  let memory ← liftMemory <| header.write state.memory address
  return { state with memory }

/-- Concrete nonrecursive increment. Promoted tags retain semantic tagged
behavior even though their physical word classifies as a heap address. -/
def incrementReference (state : MemoryState) (object : Word32)
    (amount : Nat) (check : Bool) : Except ConcreteError MemoryState := do
  match object.classify with
  | .immediate =>
      if check then return state else throw (.source .expectedHeapReference)
  | .heap =>
      let header ← liftMemory <| state.readLiveHeader object
      if header.isPromotedTag then
        if check then return state else throw (.source .expectedHeapReference)
      else if header.persistent then
        return state
      else
        let refCount ← uint32Field "reference count" (header.refCount.toNat + amount)
        writeLiveHeader state object { header with refCount }
  | .sentinel | .invalid => throw (.source .expectedObject)

/-- Concrete FIR boxing. The allocation choice follows the source semantic
tagged limit, not the narrower wasm32 immediate limit. The existing
`encodeTagged` refinement owns the intermediate persistent representation. -/
def boxScalar (state : MemoryState) (scalar : BoxedScalar) :
    Except ConcreteError (MemoryState × Word32) :=
  if scalar.payload.toNat ≤ maxTaggedPayload then
    encodeTagged state scalar.payload
  else
    allocateBoxedScalar state scalar

theorem boxScalar_of_tagged (state : MemoryState) (scalar : BoxedScalar)
    (tagged : scalar.payload.toNat ≤ maxTaggedPayload) :
    boxScalar state scalar = encodeTagged state scalar.payload := by
  simp [boxScalar, tagged]

theorem boxScalar_of_heap (state : MemoryState) (scalar : BoxedScalar)
    (heap : maxTaggedPayload < scalar.payload.toNat) :
    boxScalar state scalar = allocateBoxedScalar state scalar := by
  simp [boxScalar, Nat.not_le.mpr heap]

/-- Address of one eight-byte constructor object slot. -/
def objectFieldAddress (base index : Nat) : Nat :=
  base + headerBytes + target.semanticSlotBytes * index

/-- Install constructor object words and their required zero high padding.
This remains public so the concrete-correctness layer can state exact payload
postconditions at the runtime operation boundary. -/
def writeObjectFields (memory : LinearMemory) (base index : Nat) :
    List Word32 → Except MemoryError LinearMemory
  | [] => .ok memory
  | field :: rest => do
      let offset := objectFieldAddress base index
      let memory ← memory.writeWord32 offset field
      let memory ← memory.writeUInt32 (offset + 4) 0
      writeObjectFields memory base (index + 1) rest

/-- Allocate or immediately encode one constructor. All pre-scalar slots are
initialized: object slots contain their supplied words with zero high padding,
while `USize` and packed-scalar storage remains zero. -/
def allocateConstructor (state : MemoryState) (info : LCNF.CtorInfo)
    (fields : Array Word32) : Except ConcreteError (MemoryState × Word32) := do
  unless fields.size = info.size do
    throw (.source (.arityMismatch info.size fields.size))
  let tag ← uint32Field "constructor tag" info.cidx
  if info.size = 0 && info.usize = 0 && info.ssize = 0 then
    encodeTagged state (UInt64.ofNat tag.toNat)
  else
    let objectFields ← uint32Field "object-field count" info.size
    let usizeFields ← uint32Field "usize-field count" info.usize
    let scalarBytes ← uint32Field "scalar byte count" info.ssize
    let layout := ConstructorLayout.ofInfo info
    let (state, address) ← liftMemory <|
      state.allocateObject .constructor (layout.allocationBytes - headerBytes)
        false tag objectFields usizeFields scalarBytes
    let memory ← liftMemory <|
      writeObjectFields state.memory address.value 0 fields.toList
    return ({ state with memory }, address)

/-- Checked constructor-header decoder shared by projections and their
refinement proofs. -/
def readConstructorHeader (state : MemoryState) (object : Word32) :
    Except ConcreteError Header := do
  unless object.classify = .heap do
    throw (.source .expectedConstructor)
  let header ← liftMemory <| state.readLiveHeader object
  unless header.kind == .constructor do
    throw (.source .expectedConstructor)
  return header

def readObjectField (state : MemoryState) (object : Word32) (index : Nat) :
    Except ConcreteError Word32 := do
  let header ← readConstructorHeader state object
  let size := header.aux1.toNat
  unless index < size do
    throw (.source (.objectFieldOutOfBounds index size))
  let offset := object.value + headerBytes + target.semanticSlotBytes * index
  let word ← liftMemory <| state.memory.readWord32 offset
  let padding ← liftMemory <| state.memory.readUInt32 (offset + 4)
  unless padding == 0 do
    throw (.target (.nonzeroPadding (offset + 4) padding.toNat))
  return word

def readUSizeField (state : MemoryState) (object : Word32) (index : Nat) :
    Except ConcreteError UInt64 := do
  let header ← readConstructorHeader state object
  let objectFields := header.aux1.toNat
  let size := header.aux2.toNat
  unless index < size do
    throw (.source (.usizeFieldOutOfBounds index size))
  let offset := object.value + headerBytes +
    target.semanticSlotBytes * (objectFields + index)
  liftMemory <| state.memory.readUInt64 offset

/-- Replace the mutable constructor tag while preserving the checked common
header. Rewriting the complete header keeps one canonical encoding path for
all metadata updates and leaves the payload bytes untouched. -/
def writeTag (state : MemoryState) (object : Word32) (tag : Nat) :
    Except ConcreteError MemoryState := do
  let header ← readConstructorHeader state object
  let encoded ← uint32Field "constructor tag" tag
  let memory ← liftMemory <| { header with aux0 := encoded }.write state.memory object
  return { state with memory }

/-- Replace one checked `USize` constructor slot. The slot address is derived
from the decoded object-field count, matching the Lean64 semantic layout
captured by the concrete target policy. -/
def writeUSizeField (state : MemoryState) (object : Word32) (index : Nat)
    (value : UInt64) : Except ConcreteError MemoryState := do
  let header ← readConstructorHeader state object
  let objectFields := header.aux1.toNat
  let size := header.aux2.toNat
  unless index < size do
    throw (.source (.usizeFieldOutOfBounds index size))
  let offset := object.value + headerBytes +
    target.semanticSlotBytes * (objectFields + index)
  let memory ← liftMemory <| state.memory.writeUInt64 offset value
  return { state with memory }

/-- Validate a compiler-shaped packed scalar address. The first operand is
the number of fixed semantic slots, not the scalar type width. -/
def scalarFieldAddress (object : Word32) (header : Header)
    (slotIndex byteOffset bytes : Nat) : Except ConcreteError Nat := do
  unless slotIndex = header.aux1.toNat + header.aux2.toNat do
    throw (.source (.scalarFieldMissing slotIndex byteOffset))
  unless byteOffset + bytes ≤ header.aux3.toNat do
    throw (.source (.scalarFieldMissing slotIndex byteOffset))
  return object.value + headerBytes + target.semanticSlotBytes * slotIndex + byteOffset

def readScalarUInt8Field (state : MemoryState) (object : Word32)
    (slotIndex byteOffset : Nat) : Except ConcreteError UInt8 := do
  let header ← readConstructorHeader state object
  let address ← scalarFieldAddress object header slotIndex byteOffset 1
  liftMemory <| state.memory.readByte address

def writeScalarUInt8Field (state : MemoryState) (object : Word32)
    (slotIndex byteOffset : Nat) (value : UInt8) : Except ConcreteError MemoryState := do
  let header ← readConstructorHeader state object
  let address ← scalarFieldAddress object header slotIndex byteOffset 1
  let memory ← liftMemory <| state.memory.writeByte address value
  return { state with memory }

def readScalarUInt16Field (state : MemoryState) (object : Word32)
    (slotIndex byteOffset : Nat) : Except ConcreteError UInt16 := do
  let header ← readConstructorHeader state object
  let address ← scalarFieldAddress object header slotIndex byteOffset 2
  liftMemory <| state.memory.readUInt16 address

def writeScalarUInt16Field (state : MemoryState) (object : Word32)
    (slotIndex byteOffset : Nat) (value : UInt16) : Except ConcreteError MemoryState := do
  let header ← readConstructorHeader state object
  let address ← scalarFieldAddress object header slotIndex byteOffset 2
  let memory ← liftMemory <| state.memory.writeUInt16 address value
  return { state with memory }

def readScalarUInt32Field (state : MemoryState) (object : Word32)
    (slotIndex byteOffset : Nat) : Except ConcreteError UInt32 := do
  let header ← readConstructorHeader state object
  let address ← scalarFieldAddress object header slotIndex byteOffset 4
  liftMemory <| state.memory.readUInt32 address

def writeScalarUInt32Field (state : MemoryState) (object : Word32)
    (slotIndex byteOffset : Nat) (value : UInt32) : Except ConcreteError MemoryState := do
  let header ← readConstructorHeader state object
  let address ← scalarFieldAddress object header slotIndex byteOffset 4
  let memory ← liftMemory <| state.memory.writeUInt32 address value
  return { state with memory }

def readScalarUInt64Field (state : MemoryState) (object : Word32)
    (slotIndex byteOffset : Nat) : Except ConcreteError UInt64 := do
  let header ← readConstructorHeader state object
  let address ← scalarFieldAddress object header slotIndex byteOffset 8
  liftMemory <| state.memory.readUInt64 address

def writeScalarUInt64Field (state : MemoryState) (object : Word32)
    (slotIndex byteOffset : Nat) (value : UInt64) : Except ConcreteError MemoryState := do
  let header ← readConstructorHeader state object
  let address ← scalarFieldAddress object header slotIndex byteOffset 8
  let memory ← liftMemory <| state.memory.writeUInt64 address value
  return { state with memory }

partial def naturalLimbs (value : Nat) : List UInt64 :=
  if value < UInt64.size then
    [UInt64.ofNat value]
  else
    UInt64.ofNat (value % UInt64.size) :: naturalLimbs (value / UInt64.size)

/-- Install little-endian natural limbs.  It is public so allocation
refinement can state and prove exact payload postconditions. -/
def writeNaturalLimbs (memory : LinearMemory) (base index : Nat) :
    List UInt64 → Except MemoryError LinearMemory
  | [] => .ok memory
  | limb :: rest => do
      let memory ← memory.writeUInt64
        (base + headerBytes + target.semanticSlotBytes * index) limb
      writeNaturalLimbs memory base (index + 1) rest

/-- Decode little-endian natural limbs.  It is public so fresh-allocation
framing can transport existing natural objects. -/
def readNaturalLimbs (memory : LinearMemory) (base index : Nat) :
    Nat → Except MemoryError Nat
  | 0 => .ok 0
  | count + 1 => do
      let limb ← memory.readUInt64
        (base + headerBytes + target.semanticSlotBytes * index)
      let rest ← readNaturalLimbs memory base (index + 1) count
      return limb.toNat + UInt64.size * rest

/-- Concrete natural literal allocation. Values within the source semantic
tagged range use `encodeTagged`; larger values use a little-endian array of
64-bit limbs in a normal reference-counted natural allocation. -/
def allocateNatural (state : MemoryState) (value : Nat) :
    Except ConcreteError (MemoryState × Word32) := do
  if value ≤ Fir.LeanIR.Impure.maxTaggedPayload then
    encodeTagged state (UInt64.ofNat value)
  else
    let limbs := naturalLimbs value
    let limbCount ← uint32Field "natural limb count" limbs.length
    let (state, address) ← liftMemory <|
      state.allocateObject .natural (target.semanticSlotBytes * limbs.length)
        false bigNaturalMarker limbCount
    let memory ← liftMemory <|
      writeNaturalLimbs state.memory address.value 0 limbs
    return ({ state with memory }, address)

def readNatural (state : MemoryState) (object : Word32) : Except ConcreteError Nat := do
  unless object.classify = .heap do
    throw (.source .expectedObject)
  let header ← liftMemory <| state.readLiveHeader object
  unless header.kind == .natural && !header.persistent &&
      header.aux0 == bigNaturalMarker do
    throw (.source .expectedObject)
  liftMemory <| readNaturalLimbs state.memory object.value 0 header.aux1.toNat

/-- Decode the object-representation lanes in one static closure capture
descriptor. Scalar lanes are skipped; object, tagged, `tobject`, and erased
lanes retain source order so recursive release matches `HeapObject.children`. -/
def readClosureOwnedReferences (state : MemoryState) (object : Word32)
    (index : Nat) : List AbiKind → Except ConcreteError (List Word32)
  | [] => .ok []
  | kind :: rest => do
      if kind.isObjectField then
        let lane ← liftMemory <| state.memory.readClosureCapture
          (closureCaptureAddress object.value index) kind
        let .word32 word := lane |
          throw (.target (.closureCaptureKindMismatch .i32 lane.valueType))
        let words ← readClosureOwnedReferences state object (index + 1) rest
        return word :: words
      else
        readClosureOwnedReferences state object (index + 1) rest

/-- Load references owned by the current concrete object before marking it
dead. Constructors use their physical object-field count; closures recover
their immutable ordered capture kinds through the checked `aux3` descriptor
index. -/
def readOwnedReferences (state : MemoryState) (object : Word32) (header : Header)
    (descriptors : ClosureDescriptorTable := #[]) :
    Except ConcreteError (List Word32) :=
  match header.kind with
  | .constructor =>
      List.ofFnM fun index : Fin header.aux1.toNat =>
        readObjectField state object index
  | .closure => do
      let some captureKinds := descriptors.lookup? header.aux3 |
        throw (.target (.unknownClosureDescriptorId header.aux3))
      unless captureKinds.size == header.aux2.toNat do
        throw (.target .closureMetadataMismatch)
      readClosureOwnedReferences state object 0 captureKinds.toList
  | .freed => throw (.target (.unsupportedOwnershipKind .freed))
  | .boxed | .string | .natural | .integer | .byteArray | .opaque => .ok []

/-- Fuel-indexed recursive release. Each nested heap object consumes one unit;
siblings reuse the remaining depth while threading the updated memory. Tagged
and erased checked no-ops do not consume heap-recursion fuel. -/
def decrementReferenceOnceFuel : Nat → MemoryState → Word32 → Bool →
    (descriptors : ClosureDescriptorTable := #[]) → Except ConcreteError MemoryState
  | 0, state, object, check, _ => do
      match object.classify with
      | .immediate =>
          if check then return state else throw (.source .expectedHeapReference)
      | .heap =>
          let header ← liftMemory <| state.readLiveHeader object
          if header.isPromotedTag then
            if check then return state else throw (.source .expectedHeapReference)
          else
            throw (.target .releaseFuelExhausted)
      | .sentinel =>
          if check then return state else throw (.source .expectedObject)
      | .invalid => throw (.source .expectedObject)
  | fuel + 1, state, object, check, descriptors => do
      match object.classify with
      | .immediate =>
          if check then return state else throw (.source .expectedHeapReference)
      | .heap =>
          let header ← liftMemory <| state.readLiveHeader object
          if header.isPromotedTag then
            if check then return state else throw (.source .expectedHeapReference)
          else if header.persistent then
            return state
          else if header.refCount == 0 then
            throw (.sourceAddress (.referenceCountUnderflow object))
          else if 1 < header.refCount.toNat then
            writeLiveHeader state object
              { header with refCount := UInt32.ofNat (header.refCount.toNat - 1) }
          else
            let owned ← readOwnedReferences state object header descriptors
            let state ← writeLiveHeader state object header.forRelease
            owned.foldlM (init := state) fun state child =>
              decrementReferenceOnceFuel fuel state child true descriptors
      | .sentinel =>
          if check then return state else throw (.source .expectedObject)
      | .invalid => throw (.source .expectedObject)

/-- One concrete decrement, including the zero transition and recursive
release of constructor fields or statically typed closure captures. The
parent is marked dead before children are visited, matching FIR's cycle-safe
ordering. The allocated byte prefix provides a conservative bound on possible
nesting depth. -/
def decrementReferenceOnce (state : MemoryState) (object : Word32)
    (check : Bool) (descriptors : ClosureDescriptorTable := #[]) :
    Except ConcreteError MemoryState :=
  decrementReferenceOnceFuel (state.heapCursor / headerBytes + 1) state object check
    descriptors

/-- FIR's multi-decrement repeats the one-step transition exactly; amount zero
therefore leaves even a non-object operand untouched. -/
def decrementReference (state : MemoryState) (object : Word32)
    (amount : Nat) (check : Bool) (descriptors : ClosureDescriptorTable := #[]) :
    Except ConcreteError MemoryState :=
  (List.replicate amount object).foldlM (init := state) fun state object =>
    decrementReferenceOnce state object check descriptors

/-- Mark one ordinary heap allocation dead without recursively releasing its
owned fields. This is FIR's explicit `delete` operation, distinct from a
reference-count decrement. Promoted tags retain tagged-value behavior and are
therefore rejected as heap references. -/
def deleteObject (state : MemoryState) (object : Word32) :
    Except ConcreteError MemoryState := do
  unless object.classify = .heap do
    throw (.source .expectedHeapReference)
  let header ← liftMemory <| state.readLiveHeader object
  if header.isPromotedTag then
    throw (.source .expectedHeapReference)
  writeLiveHeader state object header.forRelease

/-- Canonical concrete word for semantic tagged zero. Reset writes this into
cleared object slots; word zero remains reserved for erased values and empty
reuse tokens. -/
def taggedZero : Word32 :=
  Word32.encodeImmediate 0 (by decide)

/-- Reset one object for possible constructor reuse. Tagged values and shared
heap cells return the empty token. A unique constructor preserves its
allocation, snapshots and clears the requested object-field prefix, releases
the old references in order, and returns its address as the reuse token. -/
def resetObject (state : MemoryState) (count : Nat) (object : Word32)
    (descriptors : ClosureDescriptorTable := #[]) :
    Except ConcreteError (MemoryState × Word32) := do
  match object.classify with
  | .immediate => return (state, Word32.zero)
  | .heap =>
      let header ← liftMemory <| state.readLiveHeader object
      if header.isPromotedTag || header.persistent || header.refCount != 1 then
        let state ← decrementReferenceOnce state object true descriptors
        return (state, Word32.zero)
      unless header.kind == .constructor do
        throw (.source .expectedConstructor)
      let size := header.aux1.toNat
      if count > size then
        throw (.source (.objectFieldOutOfBounds count size))
      let owned ← (List.range count).mapM fun index =>
        readObjectField state object index
      let memory ← liftMemory <|
        writeObjectFields state.memory object.value 0
          (List.replicate count taggedZero)
      let state := { state with memory }
      let state ← owned.foldlM (init := state) fun state child =>
        decrementReferenceOnce state child true descriptors
      return (state, object)
  | .sentinel | .invalid => throw (.source .expectedObject)

/-- Replace a byte interval with zeros. Reuse applies this to the complete old
payload before writing the new constructor fields, so stale `USize`, packed,
and trailing object data cannot leak through a smaller replacement layout. -/
def LinearMemory.zeroBytes (memory : LinearMemory) (address : Nat) : Nat →
    Except MemoryError LinearMemory
  | 0 => .ok memory
  | count + 1 => do
      let memory ← memory.writeByte address 0
      memory.zeroBytes (address + 1) count

/-- The byte-level transaction used by successful in-place constructor reuse:
erase the complete retained payload, install the replacement object fields,
then publish the replacement header. Keeping this boundary explicit lets the
correctness layer reason about the unpublished intermediate memories without
weakening the public heap relation. -/
def LinearMemory.reuseConstructorMemory (memory : LinearMemory)
    (address : Word32) (allocationBytes : Nat) (replacement : Header)
    (fields : List Word32) : Except MemoryError LinearMemory := do
  let memory ← memory.zeroBytes
    (address.value + headerBytes) (allocationBytes - headerBytes)
  let memory ← writeObjectFields memory address.value 0 fields
  replacement.write memory address

/-- Consume a concrete reuse token. Word zero selects fresh allocation. A
nonzero token must name a live constructor allocation large enough for the
replacement layout; its physical extent is retained while payload and header
metadata are rebuilt in place. -/
def reuseObject (state : MemoryState) (token : Word32) (info : LCNF.CtorInfo)
    (updateHeader : Bool) (fields : Array Word32) :
    Except ConcreteError (MemoryState × Word32) := do
  if token == Word32.zero then
    allocateConstructor state info fields
  else
    unless token.classify = .heap do
      throw (.source .expectedReuseToken)
    unless fields.size = info.size do
      throw (.source (.malformed
        s!"reuse for {info.name} expected {info.size} object fields, got {fields.size}"))
    let header ← liftMemory <| state.readLiveHeader token
    unless header.kind == .constructor do
      throw (.source .expectedConstructor)
    let layout := ConstructorLayout.ofInfo info
    unless layout.allocationBytes ≤ header.allocationBytes.toNat do
      throw (.target (.reuseAllocationTooSmall header.allocationBytes.toNat
        layout.allocationBytes))
    let tag ← if updateHeader then
      uint32Field "constructor tag" info.cidx
    else
      pure header.aux0
    let objectFields ← uint32Field "object-field count" info.size
    let usizeFields ← uint32Field "usize-field count" info.usize
    let scalarBytes ← uint32Field "scalar byte count" info.ssize
    let replacement : Header := {
      header with
      kind := .constructor
      persistent := false
      live := true
      aux0 := tag
      aux1 := objectFields
      aux2 := usizeFields
      aux3 := scalarBytes }
    let memory ← liftMemory <| state.memory.reuseConstructorMemory token
      header.allocationBytes.toNat replacement fields.toList
    return ({ state with memory }, token)

@[simp] theorem encodeTagged_immediate (state : MemoryState) (payload : UInt64)
    (fits : payload.toNat ≤ maxImmediatePayload) :
    encodeTagged state payload =
      .ok (state, Word32.encodeImmediate payload.toNat fits) := by
  simp [encodeTagged, fits]

theorem encodeTagged_immediate_refines (witness : RefinementWitness)
    (payload : UInt64) (fits : payload.toNat ≤ maxImmediatePayload) :
    ValueRel witness .tobject
      (.word32 (Word32.encodeImmediate payload.toNat fits))
      (.object (.tagged payload)) :=
  .tobject (.tagged (.immediate payload fits))

end Fir.Wasm.Concrete
