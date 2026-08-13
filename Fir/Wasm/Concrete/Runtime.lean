import Fir.Wasm.Concrete.Memory

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Concrete execution keeps source-semantic failures distinct from checked
memory/target failures, matching the W2 structured-trap boundary. -/
inductive ConcreteAddressFault where
  | deadObject (address : Word32)
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

/-- Translate a concrete-memory failure without inspecting successful payloads.
The catch-all keeps new target-side memory failures on the target lane while
retaining the one shared dead-address classification. -/
def ConcreteError.ofMemory : MemoryError → ConcreteError
  | .deadObject address => .sourceAddress (.deadObject address)
  | failure => .target failure

def liftMemory {α : Type} : Except MemoryError α → Except ConcreteError α
  | .ok value => .ok value
  | .error failure => .error (.ofMemory failure)

/-- Checked conversion for object-header metadata.  It is public so operation
refinement proofs can expose the exact failure/success boundary. -/
def uint32Field (field : String) (value : Nat) : Except ConcreteError UInt32 :=
  if value < UInt32.size then
    .ok (UInt32.ofNat value)
  else
    .error (.target (.headerValueOverflow field value))

def promotedTagMarker : UInt32 := 1

def bigNaturalMarker : UInt32 := 2

/-- Experimental version marker for the current arbitrary-precision heap-Int
layout. Clients may rely on the checked API, not on long-term layout stability. -/
def integerSignMagnitudeMarker : UInt32 := 1

/-- Version marker for the W6 string payload. Strings store their canonical
UTF-8 bytes contiguously after the common header; `aux1` records the exact byte
count and `aux2`/`aux3` remain reserved. -/
def stringUtf8Marker : UInt32 := 1

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
canonical before the semantic scalar is reconstructed. Persistence is
ownership metadata and does not change the boxed representation. -/
def readHeapBoxedScalar (state : MemoryState) (address : Word32) (header : Header) :
    Except ConcreteError BoxedScalar := do
  let some kind := BoxedScalarKind.ofCode? header.aux0 |
    throw (.target (.unknownBoxedScalarKind header.aux0))
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

/-- Replace one checked constructor object slot. Decoding the old field first
validates the constructor, index, and canonical zero padding; the store then
changes only the low wasm32 word of the eight-byte semantic slot. -/
def writeObjectField (state : MemoryState) (object : Word32) (index : Nat)
    (field : Word32) : Except ConcreteError MemoryState := do
  let _ ← readObjectField state object index
  let offset := objectFieldAddress object.value index
  let memory ← liftMemory <| state.memory.writeWord32 offset field
  return { state with memory }

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

/-- Read a constructor `USize` using Lean final-LCNF's absolute fixed-slot
coordinate. The type-local reader remains available to refinement internals. -/
def readUSizeSlot (state : MemoryState) (object : Word32) (slot : Nat) :
    Except ConcreteError UInt64 := do
  let header ← readConstructorHeader state object
  let objectFields := header.aux1.toNat
  let usizeFields := header.aux2.toNat
  unless objectFields ≤ slot && slot < objectFields + usizeFields do
    throw (.source (.usizeFieldOutOfBounds slot (objectFields + usizeFields)))
  readUSizeField state object (slot - objectFields)

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

/-- Write a constructor `USize` using Lean final-LCNF's absolute fixed-slot
coordinate, translating through the decoded object-field prefix. -/
def writeUSizeSlot (state : MemoryState) (object : Word32) (slot : Nat)
    (value : UInt64) : Except ConcreteError MemoryState := do
  let header ← readConstructorHeader state object
  let objectFields := header.aux1.toNat
  let usizeFields := header.aux2.toNat
  unless objectFields ≤ slot && slot < objectFields + usizeFields do
    throw (.source (.usizeFieldOutOfBounds slot (objectFields + usizeFields)))
  writeUSizeField state object (slot - objectFields) value

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

/-- Canonical little-endian base-`2^64` limbs. This is well-founded rather
than `partial` so allocation correctness can use its equation theorem. -/
def naturalLimbs (value : Nat) : List UInt64 :=
  if _h : value < UInt64.size then
    [UInt64.ofNat value]
  else
    UInt64.ofNat (value % UInt64.size) :: naturalLimbs (value / UInt64.size)
termination_by value
decreasing_by
  apply Nat.div_lt_self
  · have sizePositive : 0 < UInt64.size := by decide
    omega
  · decide

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
  unless header.kind == .natural && header.aux0 == bigNaturalMarker do
    throw (.source .expectedObject)
  liftMemory <| readNaturalLimbs state.memory object.value 0 header.aux1.toNat

/-- Unsigned magnitude represented by a semantic arbitrary-precision integer. -/
def integerMagnitude : Int → Nat
  | .ofNat value => value
  | .negSucc value => value + 1

/-- Header sign lane for the current experimental Int layout: zero is
nonnegative and one is negative. -/
def integerSign : Int → UInt32
  | .ofNat _ => 0
  | .negSucc _ => 1

def integerOfSignMagnitude (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude

/-- Allocate one ordinary arbitrary-precision integer as canonical
little-endian base-`2^64` magnitude limbs. Header auxiliaries currently carry
`(version, limbCount, sign, reserved)`. This is an experimental concrete
surface and may evolve with the backend. -/
def allocateInteger (state : MemoryState) (value : Int) :
    Except ConcreteError (MemoryState × Word32) := do
  let limbs := naturalLimbs (integerMagnitude value)
  let limbCount ← uint32Field "integer limb count" limbs.length
  let (state, address) ← liftMemory <|
    state.allocateObject .integer (target.semanticSlotBytes * limbs.length)
      false integerSignMagnitudeMarker limbCount (integerSign value) 0
  let memory ← liftMemory <|
    writeNaturalLimbs state.memory address.value 0 limbs
  return ({ state with memory }, address)

/-- Decode the current checked arbitrary-precision heap-Int layout. The
decoder rejects unknown versions, invalid signs, empty magnitudes, negative
zero, reserved metadata, and noncanonical allocation extents. -/
def readInteger (state : MemoryState) (object : Word32) : Except ConcreteError Int := do
  unless object.classify = .heap do
    throw (.source .expectedObject)
  let header ← liftMemory <| state.readLiveHeader object
  unless header.kind == .integer &&
      header.aux0 == integerSignMagnitudeMarker do
    throw (.source .expectedObject)
  let limbCount := header.aux1.toNat
  unless (header.aux2 == 0 || header.aux2 == 1) && header.aux3 == 0 &&
      0 < limbCount && header.allocationBytes.toNat =
        align8 (headerBytes + target.semanticSlotBytes * limbCount) do
    throw (.target (.malformedIntegerHeader object.value))
  let magnitude ← liftMemory <|
    readNaturalLimbs state.memory object.value 0 limbCount
  if header.aux2 == 1 then
    if magnitude == 0 then
      throw (.target (.malformedIntegerHeader object.value))
    else
      return integerOfSignMagnitude true magnitude
  else
    return integerOfSignMagnitude false magnitude

/-- Canonical byte sequence stored by one concrete string allocation. Keeping
this conversion public lets the refinement layer compare the payload directly
without trusting a second UTF-8 decoder. -/
def stringUtf8Bytes (value : String) : List UInt8 :=
  value.toUTF8.data.toList

/-- Install one contiguous UTF-8 payload immediately after the common object
header. -/
def writeStringBytes (memory : LinearMemory) (base index : Nat) :
    List UInt8 → Except MemoryError LinearMemory
  | [] => .ok memory
  | byte :: rest => do
      let memory ← memory.writeByte (base + headerBytes + index) byte
      writeStringBytes memory base (index + 1) rest

/-- Read one bounded concrete string payload as raw canonical UTF-8 bytes. -/
def readStringBytes (memory : LinearMemory) (base index : Nat) :
    Nat → Except MemoryError (List UInt8)
  | 0 => .ok []
  | count + 1 => do
      let byte ← memory.readByte (base + headerBytes + index)
      let rest ← readStringBytes memory base (index + 1) count
      return byte :: rest

/-- Allocate one source string as a versioned, reference-counted UTF-8 object.
The aligned allocation may contain zero padding, but only the `aux1` bytes are
part of the semantic payload. -/
def allocateString (state : MemoryState) (value : String) :
    Except ConcreteError (MemoryState × Word32) := do
  let bytes := stringUtf8Bytes value
  let byteCount ← uint32Field "string UTF-8 byte count" bytes.length
  let (state, address) ← liftMemory <|
    state.allocateObject .string bytes.length false stringUtf8Marker byteCount
  let memory ← liftMemory <|
    writeStringBytes state.memory address.value 0 bytes
  return ({ state with memory }, address)

/-- Checked raw decoder for the frozen W6 string layout. Malformed metadata
cannot make the decoder read beyond the object's retained physical extent. -/
def readStringPayload (state : MemoryState) (object : Word32) :
    Except ConcreteError (List UInt8) := do
  unless object.classify = .heap do
    throw (.source .expectedObject)
  let header ← liftMemory <| state.readLiveHeader object
  unless header.kind == .string do
    throw (.source .expectedObject)
  unless header.aux0 == stringUtf8Marker && header.aux2 == 0 && header.aux3 == 0 &&
      headerBytes + header.aux1.toNat ≤ header.allocationBytes.toNat do
    throw (.target (.malformedHeader object.value header.allocationBytes.toNat))
  liftMemory <| readStringBytes state.memory object.value 0 header.aux1.toNat

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

/-- Decode exactly the live owned prefix of the canonical resident generic
Array layout. `aux1` is the logical size and `aux2` is physical capacity;
spare slots are deliberately not read and therefore never participate in
recursive ownership. -/
def readResidentArrayOwnedReferences (state : MemoryState) (object : Word32)
    (header : Header) : Except ConcreteError (List Word32) := do
  unless header.kind == .opaque && header.aux0 == residentArrayMarker &&
      header.aux3 == 0 && header.aux1.toNat ≤ header.aux2.toNat &&
      header.allocationBytes.toNat ==
        residentArrayAllocationBytes header.aux2.toNat do
    throw (.target (.malformedHeader object.value header.allocationBytes.toNat))
  List.ofFnM fun index : Fin header.aux1.toNat =>
    liftMemory <| state.memory.readWord32
      (object.value + headerBytes + target.semanticSlotBytes * index)

/-- Checked common decoder for the resident generic Array layout. This is the
W6 semantic boundary consumed by read and mutation proofs; clients do not need
to repeat the physical `opaque/ARRY/size/capacity` checks. -/
def readResidentArrayHeader (state : MemoryState) (object : Word32) :
    Except ConcreteError Header := do
  unless object.classify = .heap do
    throw (.source .expectedObject)
  let header ← liftMemory <| state.readLiveHeader object
  unless header.kind == .opaque && header.aux0 == residentArrayMarker &&
      header.aux3 == 0 && header.aux1.toNat ≤ header.aux2.toNat &&
      header.allocationBytes.toNat ==
        residentArrayAllocationBytes header.aux2.toNat do
    throw (.target (.malformedHeader object.value header.allocationBytes.toNat))
  return header

/-- Read the logical size without exposing retained spare capacity. -/
def readResidentArraySize (state : MemoryState) (object : Word32) :
    Except ConcreteError Nat := do
  let header ← readResidentArrayHeader state object
  return header.aux1.toNat

/-- Borrow one live resident-Array slot. The operation reads the low `tobject`
word only; it performs no retain and changes no concrete runtime state. -/
def readResidentArrayElementBorrowed (state : MemoryState) (object : Word32)
    (index : Nat) : Except ConcreteError Word32 := do
  let header ← readResidentArrayHeader state object
  unless index < header.aux1.toNat do
    throw (.source (.objectFieldOutOfBounds index header.aux1.toNat))
  liftMemory <| state.memory.readWord32
    (object.value + headerBytes + target.semanticSlotBytes * index)

/-- Allocate the canonical resident generic Array and initialize exactly its
live `tobject` prefix. `capacity` determines the retained extent; spare slots
remain allocator-zeroed and are not semantic ownership. -/
def allocateResidentArray (state : MemoryState) (elements : Array Word32)
    (capacity : Nat) : Except ConcreteError (MemoryState × Word32) := do
  unless elements.size ≤ capacity do
    throw (.source (.malformed "Array logical size exceeds capacity"))
  let logicalSize ← uint32Field "Array logical size" elements.size
  let physicalCapacity ← uint32Field "Array capacity" capacity
  let (state, address) ← liftMemory <|
    state.allocateObject .opaque (target.semanticSlotBytes * capacity) false
      residentArrayMarker logicalSize physicalCapacity 0
  let memory ← liftMemory <|
    writeObjectFields state.memory address.value 0 elements.toList
  return ({ state with memory }, address)

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
  | .opaque =>
      if header.aux0 == residentArrayMarker then
        readResidentArrayOwnedReferences state object header
      else
        .ok []
  | .freed => throw (.target (.unsupportedOwnershipKind .freed))
  | .boxed | .string | .natural | .integer | .byteArray => .ok []

/-- A released allocation is a persistence no-op only when its complete
retained header has the canonical shape installed by ownership release. This
check is intentionally local to persistence: ordinary object decoders keep
rejecting every dead header through `readLiveHeader`. -/
def Header.isCanonicalFreedAt (header : Header) (state : MemoryState)
    (address : Word32) : Bool :=
  header.kind == .freed && !header.persistent && !header.live &&
    header.refCount == 0 && header.aux0 == 0 && header.aux1 == 0 &&
    header.aux2 == 0 && header.aux3 == 0 &&
    headerBytes ≤ header.allocationBytes.toNat &&
    header.allocationBytes.toNat % target.heapAlignment == 0 &&
    address.value + header.allocationBytes.toNat ≤ state.memory.size

/-- Recover the canonical released-header case after `readLiveHeader` has
classified it as dead. Noncanonical dead headers retain the exact structured
`deadObject` target failure. -/
def persistenceDeadNoOp (state : MemoryState) (object : Word32) :
    Except ConcreteError MemoryState := do
  let header ← liftMemory <| Header.read state.memory object
  if header.isCanonicalFreedAt state object then
    return state
  else
    throw (.target (.deadObject object))

/-- Fuel-indexed mirror of Lean's `lean_mark_persistent`. The current object
is rewritten before its owned references are visited, so cycles terminate at
the newly persistent header. Immediate and sentinel lanes, plus canonical
released allocations reached through stale semantic ownership, contain no
live heap graph and are exact no-ops. -/
def markPersistentFuel : Nat → MemoryState → Word32 →
    (descriptors : ClosureDescriptorTable := #[]) → Except ConcreteError MemoryState
  | 0, state, object, _ => do
      match object.classify with
      | .heap =>
          match state.readLiveHeader object with
          | .error (.deadObject _) => persistenceDeadNoOp state object
          | .error failure => throw (.target failure)
          | .ok header =>
              if header.persistent then return state
              else throw (.target .releaseFuelExhausted)
      | .immediate | .sentinel => return state
      | .invalid => throw (.source .expectedObject)
  | fuel + 1, state, object, descriptors => do
      match object.classify with
      | .heap =>
          match state.readLiveHeader object with
          | .error (.deadObject _) => persistenceDeadNoOp state object
          | .error failure => throw (.target failure)
          | .ok header =>
              if header.persistent then
                return state
              let owned ← readOwnedReferences state object header descriptors
              let state ← writeLiveHeader state object
                { header with persistent := true, refCount := 0 }
              owned.foldlM (init := state) fun state child =>
                markPersistentFuel fuel state child descriptors
      | .immediate | .sentinel => return state
      | .invalid => throw (.source .expectedObject)

/-- Mark a concrete value's complete reachable heap graph persistent. The
allocated prefix bounds every simple heap path; mark-before-descend handles
cycles without a separate visited structure. -/
def markPersistent (state : MemoryState) (object : Word32)
    (descriptors : ClosureDescriptorTable := #[]) :
    Except ConcreteError MemoryState :=
  markPersistentFuel (state.heapCursor / headerBytes + 1) state object descriptors

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
owned fields. Physical zero is the erased failed-reset sentinel and is a
delete-specific no-op, matching FIR and Lean's native runtime. Other sentinels,
immediates, and promoted tags remain invalid heap references. -/
def deleteObject (state : MemoryState) (object : Word32) :
    Except ConcreteError MemoryState := do
  if object == Word32.zero then
    return state
  unless object.classify = .heap do
    throw (.source .expectedHeapReference)
  let header ← liftMemory <| state.readLiveHeader object
  if header.isPromotedTag then
    throw (.source .expectedHeapReference)
  writeLiveHeader state object header.forRelease

@[simp] theorem deleteObject_zero (state : MemoryState) :
    deleteObject state Word32.zero = .ok state := by
  unfold deleteObject
  rw [if_pos (by decide)]
  simp only [pure, Except.pure]

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
