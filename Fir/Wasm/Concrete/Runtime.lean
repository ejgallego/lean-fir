import Fir.Wasm.Concrete.Memory

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Concrete execution keeps source-semantic failures distinct from checked
memory/target failures, matching the W2 structured-trap boundary. -/
inductive ConcreteError where
  | source (fault : RuntimeFault)
  | target (failure : MemoryError)
  deriving BEq, Repr

def liftMemory {α : Type} : Except MemoryError α → Except ConcreteError α
  | .ok value => .ok value
  | .error failure => .error (.target failure)

private def uint32Field (field : String) (value : Nat) : Except ConcreteError UInt32 :=
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

private def writeObjectFields (memory : LinearMemory) (base index : Nat) :
    List Word32 → Except MemoryError LinearMemory
  | [] => .ok memory
  | field :: rest => do
      let offset := base + headerBytes + target.semanticSlotBytes * index
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

private def readConstructorHeader (state : MemoryState) (object : Word32) :
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

partial def naturalLimbs (value : Nat) : List UInt64 :=
  if value < UInt64.size then
    [UInt64.ofNat value]
  else
    UInt64.ofNat (value % UInt64.size) :: naturalLimbs (value / UInt64.size)

private def writeNaturalLimbs (memory : LinearMemory) (base index : Nat) :
    List UInt64 → Except MemoryError LinearMemory
  | [] => .ok memory
  | limb :: rest => do
      let memory ← memory.writeUInt64
        (base + headerBytes + target.semanticSlotBytes * index) limb
      writeNaturalLimbs memory base (index + 1) rest

private def readNaturalLimbs (memory : LinearMemory) (base index : Nat) :
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
