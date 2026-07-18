import Fir.Wasm.Concrete.Layout

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Values at the concrete function/memory boundary. Floating-point lanes are
stored as their raw IEEE bit patterns so the refinement relation does not
depend on host floating-point equality. -/
inductive LaneValue where
  | word32 (value : Word32)
  | word64 (value : UInt64)
  | float32Bits (value : UInt32)
  | float64Bits (value : UInt64)
  deriving Repr

def LaneValue.valueType : LaneValue → ValueType
  | .word32 _ => .i32
  | .word64 _ => .i64
  | .float32Bits _ => .f32
  | .float64Bits _ => .f64

abbrev LocationMap := List (Location × Word32)

abbrev PromotedTags := List (UInt64 × Word32)

def LocationMap.lookup? : LocationMap → Location → Option Word32
  | [], _ => none
  | (candidate, address) :: rest, location =>
      if candidate = location then some address else lookup? rest location

def PromotedTags.lookup? : PromotedTags → UInt64 → Option Word32
  | [], _ => none
  | (candidate, address) :: rest, payload =>
      if candidate = payload then some address else lookup? rest payload

/-- Ghost data used only by the refinement proof. `locations` relates semantic
heap locations to concrete linear-memory addresses. `promotedTags` records
large semantic immediates represented as persistent natural objects because
they do not fit in a 31-bit wasm32 immediate word. -/
structure RefinementWitness where
  locations : LocationMap := []
  promotedTags : PromotedTags := []
  deriving Inhabited, Repr

def RefinementWitness.bindLocation (witness : RefinementWitness)
    (location : Location) (address : Word32) : RefinementWitness :=
  { witness with locations := (location, address) :: witness.locations }

def RefinementWitness.promoteTag (witness : RefinementWitness)
    (payload : UInt64) (address : Word32) : RefinementWitness :=
  { witness with promotedTags := (payload, address) :: witness.promotedTags }

@[simp] theorem RefinementWitness.lookup_bindLocation_self
    (witness : RefinementWitness) (location : Location) (address : Word32) :
    (witness.bindLocation location address).locations.lookup? location = some address := by
  simp [RefinementWitness.bindLocation, LocationMap.lookup?]

@[simp] theorem RefinementWitness.lookup_promoteTag_self
    (witness : RefinementWitness) (payload : UInt64) (address : Word32) :
    (witness.promoteTag payload address).promotedTags.lookup? payload = some address := by
  simp [RefinementWitness.promoteTag, PromotedTags.lookup?]

/-- The lookup-visible part of a witness is injective and every related word
is a concrete heap address. This avoids baking proof-only location identities
into linear memory. -/
structure RefinementWitness.WellFormed (witness : RefinementWitness) : Prop where
  locationHeap : ∀ location address,
    witness.locations.lookup? location = some address → address.classify = .heap
  locationInjective : ∀ left right address,
    witness.locations.lookup? left = some address →
    witness.locations.lookup? right = some address → left = right
  promotedHeap : ∀ payload address,
    witness.promotedTags.lookup? payload = some address → address.classify = .heap
  promotedInjective : ∀ left right address,
    witness.promotedTags.lookup? left = some address →
    witness.promotedTags.lookup? right = some address → left = right
  locationPromotionDisjoint : ∀ location payload left right,
    witness.locations.lookup? location = some left →
    witness.promotedTags.lookup? payload = some right → left ≠ right

inductive HeapReferenceRel (witness : RefinementWitness) :
    Word32 → Location → Prop where
  | mapped {location address}
      (found : witness.locations.lookup? location = some address) :
      HeapReferenceRel witness address location

inductive TaggedReferenceRel (witness : RefinementWitness) :
    Word32 → UInt64 → Prop where
  | immediate (payload : UInt64)
      (fits : payload.toNat ≤ maxImmediatePayload) :
      TaggedReferenceRel witness
        (Word32.encodeImmediate payload.toNat fits) payload
  | promoted {payload address}
      (found : witness.promotedTags.lookup? payload = some address) :
      TaggedReferenceRel witness address payload

inductive ObjectReferenceRel (witness : RefinementWitness) :
    Word32 → ObjectRef → Prop where
  | heap (related : HeapReferenceRel witness address location) :
      ObjectReferenceRel witness address (.heap location)
  | tagged (related : TaggedReferenceRel witness word payload) :
      ObjectReferenceRel witness word (.tagged payload)

/-- ABI-indexed value refinement. This is the concrete replacement for W2's
opaque-handle `Encodes` relation. It fixes the physical lane and semantic value
simultaneously, so later operation refinements cannot silently reinterpret an
`i32` scalar as an address or an erased sentinel as an object. -/
inductive ValueRel (witness : RefinementWitness) :
    AbiKind → LaneValue → Value → Prop where
  | object (related : HeapReferenceRel witness word location) :
      ValueRel witness .object (.word32 word) (.object (.heap location))
  | tagged (related : TaggedReferenceRel witness word payload) :
      ValueRel witness .tagged (.word32 word) (.object (.tagged payload))
  | tobject (related : ObjectReferenceRel witness word reference) :
      ValueRel witness .tobject (.word32 word) (.object reference)
  | erased :
      ValueRel witness .erased (.word32 Word32.zero) .erased
  | reuseNone :
      ValueRel witness .reuseToken (.word32 Word32.zero) (.reuseToken none)
  | reuseSome (related : HeapReferenceRel witness word location) :
      ValueRel witness .reuseToken (.word32 word) (.reuseToken (some location))
  | uint8 (encoded : word.value = value.toNat) :
      ValueRel witness .uint8 (.word32 word) (.scalar (.uint8 value))
  | uint16 (encoded : word.value = value.toNat) :
      ValueRel witness .uint16 (.word32 word) (.scalar (.uint16 value))
  | uint32 (encoded : word.value = value.toNat) :
      ValueRel witness .uint32 (.word32 word) (.scalar (.uint32 value))
  | uint64 :
      ValueRel witness .uint64 (.word64 value) (.scalar (.uint64 value))
  | usize :
      ValueRel witness .usize (.word64 value) (.usize value)

theorem ValueRel.physical_type {witness : RefinementWitness} {kind : AbiKind}
    {concrete : LaneValue} {semantic : Value}
    (related : ValueRel witness kind concrete semantic) :
    concrete.valueType = kind.valueType := by
  cases related <;> rfl

theorem TaggedReferenceRel.immediate_not_sentinel
    {witness : RefinementWitness} {word : Word32} {payload : UInt64}
    (related : TaggedReferenceRel witness word payload)
    (notPromoted : witness.promotedTags.lookup? payload = none) :
    word ≠ Word32.zero := by
  cases related with
  | immediate payload fits => exact Word32.immediate_ne_zero payload.toNat fits
  | promoted found => simp [notPromoted] at found

theorem HeapReferenceRel.is_heap {witness : RefinementWitness}
    (valid : witness.WellFormed) {word : Word32} {location : Location}
    (related : HeapReferenceRel witness word location) :
    word.classify = .heap := by
  cases related with
  | mapped found => exact valid.locationHeap _ _ found

theorem TaggedReferenceRel.promoted_is_heap {witness : RefinementWitness}
    (valid : witness.WellFormed) {word : Word32} {payload : UInt64}
    (related : TaggedReferenceRel witness word payload)
    (tooLarge : maxImmediatePayload < payload.toNat) :
    word.classify = .heap := by
  cases related with
  | immediate _ fits => omega
  | promoted found => exact valid.promotedHeap _ _ found

theorem ValueRel.new_heap_location (witness : RefinementWitness)
    (location : Location) (address : Word32) :
    ValueRel (witness.bindLocation location address) .object (.word32 address)
      (.object (.heap location)) :=
  .object (.mapped (RefinementWitness.lookup_bindLocation_self witness location address))

theorem ValueRel.new_promoted_tag (witness : RefinementWitness)
    (payload : UInt64) (address : Word32) :
    ValueRel (witness.promoteTag payload address) .tagged (.word32 address)
      (.object (.tagged payload)) :=
  .tagged (.promoted (RefinementWitness.lookup_promoteTag_self witness payload address))

end Fir.Wasm.Concrete
