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

/-- Proof-only metadata used to decode typed payloads. It is derived from the
operation that allocated the object and is not stored as a semantic value in
linear memory. -/
inductive AllocationDescriptor where
  | constructor (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind)
  | boxed (kind : BoxedScalarKind)
  | promotedTag (payload : UInt64)
  | natural (value : Nat)
  deriving Inhabited, BEq, Repr

abbrev DescriptorMap := List (Word32 × AllocationDescriptor)

def LocationMap.lookup? : LocationMap → Location → Option Word32
  | [], _ => none
  | (candidate, address) :: rest, location =>
      if candidate = location then some address else lookup? rest location

def PromotedTags.lookup? : PromotedTags → UInt64 → Option Word32
  | [], _ => none
  | (candidate, address) :: rest, payload =>
      if candidate = payload then some address else lookup? rest payload

def DescriptorMap.lookup? : DescriptorMap → Word32 → Option AllocationDescriptor
  | [], _ => none
  | (candidate, descriptor) :: rest, address =>
      if candidate.value = address.value then some descriptor else lookup? rest address

/-- Ghost data used only by the refinement proof. `locations` relates semantic
heap locations to concrete linear-memory addresses. `promotedTags` records
large semantic immediates represented as persistent natural objects because
they do not fit in a 31-bit wasm32 immediate word. -/
structure RefinementWitness where
  locations : LocationMap := []
  promotedTags : PromotedTags := []
  descriptors : DescriptorMap := []
  deriving Inhabited, Repr

def RefinementWitness.bindLocation (witness : RefinementWitness)
    (location : Location) (address : Word32) : RefinementWitness :=
  { witness with locations := (location, address) :: witness.locations }

def RefinementWitness.promoteTag (witness : RefinementWitness)
    (payload : UInt64) (address : Word32) : RefinementWitness :=
  { witness with
      promotedTags := (payload, address) :: witness.promotedTags
      descriptors := (address, .promotedTag payload) :: witness.descriptors }

def RefinementWitness.bindConstructor (witness : RefinementWitness)
    (location : Location) (address : Word32) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) : RefinementWitness :=
  { witness with
      locations := (location, address) :: witness.locations
      descriptors := (address, .constructor info fieldKinds) :: witness.descriptors }

def RefinementWitness.bindNatural (witness : RefinementWitness)
    (location : Location) (address : Word32) (value : Nat) : RefinementWitness :=
  { witness with
      locations := (location, address) :: witness.locations
      descriptors := (address, .natural value) :: witness.descriptors }

def RefinementWitness.bindBoxed (witness : RefinementWitness)
    (location : Location) (address : Word32)
    (kind : BoxedScalarKind) : RefinementWitness :=
  { witness with
      locations := (location, address) :: witness.locations
      descriptors := (address, .boxed kind) :: witness.descriptors }

@[simp] theorem RefinementWitness.lookup_bindLocation_self
    (witness : RefinementWitness) (location : Location) (address : Word32) :
    (witness.bindLocation location address).locations.lookup? location = some address := by
  simp [RefinementWitness.bindLocation, LocationMap.lookup?]

@[simp] theorem RefinementWitness.lookup_promoteTag_self
    (witness : RefinementWitness) (payload : UInt64) (address : Word32) :
    (witness.promoteTag payload address).promotedTags.lookup? payload = some address := by
  simp [RefinementWitness.promoteTag, PromotedTags.lookup?]

@[simp] theorem RefinementWitness.lookup_promoteTag_descriptor
    (witness : RefinementWitness) (payload : UInt64) (address : Word32) :
    (witness.promoteTag payload address).descriptors.lookup? address =
      some (.promotedTag payload) := by
  simp [RefinementWitness.promoteTag, DescriptorMap.lookup?]

@[simp] theorem RefinementWitness.lookup_bindConstructor_location
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    (witness.bindConstructor location address info fieldKinds).locations.lookup? location =
      some address := by
  simp [RefinementWitness.bindConstructor, LocationMap.lookup?]

@[simp] theorem RefinementWitness.lookup_bindConstructor_descriptor
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    (witness.bindConstructor location address info fieldKinds).descriptors.lookup? address =
      some (.constructor info fieldKinds) := by
  simp [RefinementWitness.bindConstructor, DescriptorMap.lookup?]

theorem RefinementWitness.lookup_bindConstructor_location_other
    (witness : RefinementWitness) (location other : Location) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (different : other ≠ location) :
    (witness.bindConstructor location address info fieldKinds).locations.lookup? other =
      witness.locations.lookup? other := by
  simp [RefinementWitness.bindConstructor, LocationMap.lookup?, Ne.symm different]

theorem RefinementWitness.lookup_bindConstructor_descriptor_other
    (witness : RefinementWitness) (location : Location) (address other : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (different : address.value ≠ other.value) :
    (witness.bindConstructor location address info fieldKinds).descriptors.lookup? other =
      witness.descriptors.lookup? other := by
  simp [RefinementWitness.bindConstructor, DescriptorMap.lookup?, different]

@[simp] theorem RefinementWitness.lookup_bindNatural_location
    (witness : RefinementWitness) (location : Location) (address : Word32) (value : Nat) :
    (witness.bindNatural location address value).locations.lookup? location = some address := by
  simp [RefinementWitness.bindNatural, LocationMap.lookup?]

@[simp] theorem RefinementWitness.lookup_bindNatural_descriptor
    (witness : RefinementWitness) (location : Location) (address : Word32) (value : Nat) :
    (witness.bindNatural location address value).descriptors.lookup? address =
      some (.natural value) := by
  simp [RefinementWitness.bindNatural, DescriptorMap.lookup?]

@[simp] theorem RefinementWitness.lookup_bindBoxed_location
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (kind : BoxedScalarKind) :
    (witness.bindBoxed location address kind).locations.lookup? location =
      some address := by
  simp [RefinementWitness.bindBoxed, LocationMap.lookup?]

@[simp] theorem RefinementWitness.lookup_bindBoxed_descriptor
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (kind : BoxedScalarKind) :
    (witness.bindBoxed location address kind).descriptors.lookup? address =
      some (.boxed kind) := by
  simp [RefinementWitness.bindBoxed, DescriptorMap.lookup?]

theorem RefinementWitness.lookup_bindBoxed_location_other
    (witness : RefinementWitness) (location other : Location) (address : Word32)
    (kind : BoxedScalarKind) (different : other ≠ location) :
    (witness.bindBoxed location address kind).locations.lookup? other =
      witness.locations.lookup? other := by
  simp [RefinementWitness.bindBoxed, LocationMap.lookup?, Ne.symm different]

theorem RefinementWitness.lookup_bindBoxed_descriptor_other
    (witness : RefinementWitness) (location : Location) (address other : Word32)
    (kind : BoxedScalarKind) (different : address.value ≠ other.value) :
    (witness.bindBoxed location address kind).descriptors.lookup? other =
      witness.descriptors.lookup? other := by
  simp [RefinementWitness.bindBoxed, DescriptorMap.lookup?, different]

/-- Lookup-level monotonicity of proof-only refinement metadata. Allocation
operations establish this relation before transporting value and heap-cell
relations to an extended witness. -/
structure RefinementWitness.Extends (before after : RefinementWitness) : Prop where
  locations : ∀ location address,
    before.locations.lookup? location = some address →
    after.locations.lookup? location = some address
  promotedTags : ∀ payload address,
    before.promotedTags.lookup? payload = some address →
    after.promotedTags.lookup? payload = some address
  descriptors : ∀ address descriptor,
    before.descriptors.lookup? address = some descriptor →
    after.descriptors.lookup? address = some descriptor

namespace RefinementWitness.Extends

theorem refl (witness : RefinementWitness) : witness.Extends witness := by
  exact ⟨fun _ _ found => found, fun _ _ found => found, fun _ _ found => found⟩

theorem trans {first second third : RefinementWitness}
    (left : first.Extends second) (right : second.Extends third) :
    first.Extends third := by
  exact ⟨
    fun _ _ found => right.locations _ _ (left.locations _ _ found),
    fun _ _ found => right.promotedTags _ _ (left.promotedTags _ _ found),
    fun _ _ found => right.descriptors _ _ (left.descriptors _ _ found)⟩

end RefinementWitness.Extends

/-- Binding a fresh constructor extends every old lookup. Descriptor freshness
is stated at the value-comparison boundary used by `DescriptorMap.lookup?`. -/
theorem RefinementWitness.bindConstructor_extends
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (locationFresh : witness.locations.lookup? location = none)
    (descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value) :
    witness.Extends (witness.bindConstructor location address info fieldKinds) := by
  refine {
    locations := ?_
    promotedTags := ?_
    descriptors := ?_ }
  · intro old oldAddress found
    have different : old ≠ location := by
      intro equal
      subst old
      simp [locationFresh] at found
    rw [witness.lookup_bindConstructor_location_other location old address info
      fieldKinds different]
    exact found
  · intro payload oldAddress found
    exact found
  · intro old descriptor found
    rw [witness.lookup_bindConstructor_descriptor_other location address old info
      fieldKinds (descriptorFresh old descriptor found)]
    exact found

/-- Binding one fresh heap box extends all previously visible proof metadata. -/
theorem RefinementWitness.bindBoxed_extends
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (kind : BoxedScalarKind)
    (locationFresh : witness.locations.lookup? location = none)
    (descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value) :
    witness.Extends (witness.bindBoxed location address kind) := by
  refine {
    locations := ?_
    promotedTags := ?_
    descriptors := ?_ }
  · intro old oldAddress found
    have different : old ≠ location := by
      intro equal
      subst old
      simp [locationFresh] at found
    rw [witness.lookup_bindBoxed_location_other location old address kind different]
    exact found
  · intro payload oldAddress found
    exact found
  · intro old descriptor found
    rw [witness.lookup_bindBoxed_descriptor_other location address old kind
      (descriptorFresh old descriptor found)]
    exact found

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

/-- Fresh constructor metadata preserves witness injectivity and the
location/promoted-tag address partition. -/
theorem RefinementWitness.WellFormed.bindConstructor
    {witness : RefinementWitness} (valid : witness.WellFormed)
    (location : Location) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (addressHeap : address.classify = .heap)
    (locationAddressFresh : ∀ old oldAddress,
      witness.locations.lookup? old = some oldAddress → oldAddress ≠ address)
    (promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.lookup? payload = some oldAddress → address ≠ oldAddress) :
    (witness.bindConstructor location address info fieldKinds).WellFormed := by
  refine {
    locationHeap := ?_
    locationInjective := ?_
    promotedHeap := valid.promotedHeap
    promotedInjective := valid.promotedInjective
    locationPromotionDisjoint := ?_ }
  · intro old oldAddress found
    by_cases isNew : old = location
    · subst old
      simp [RefinementWitness.bindConstructor, LocationMap.lookup?] at found
      cases found
      exact addressHeap
    · rw [witness.lookup_bindConstructor_location_other location old address info
        fieldKinds isNew] at found
      exact valid.locationHeap old oldAddress found
  · intro left right common leftFound rightFound
    by_cases leftNew : left = location
    · subst left
      simp [RefinementWitness.bindConstructor, LocationMap.lookup?] at leftFound
      have commonEq : common = address := leftFound.symm
      subst common
      by_cases rightNew : right = location
      · exact rightNew.symm
      · rw [witness.lookup_bindConstructor_location_other location right address info
          fieldKinds rightNew] at rightFound
        exact False.elim ((locationAddressFresh right address rightFound) rfl)
    · rw [witness.lookup_bindConstructor_location_other location left address info
        fieldKinds leftNew] at leftFound
      by_cases rightNew : right = location
      · subst right
        simp [RefinementWitness.bindConstructor, LocationMap.lookup?] at rightFound
        have commonEq : common = address := rightFound.symm
        subst common
        exact False.elim ((locationAddressFresh left address leftFound) rfl)
      · rw [witness.lookup_bindConstructor_location_other location right address info
          fieldKinds rightNew] at rightFound
        exact valid.locationInjective left right common leftFound rightFound
  · intro old payload left right locationFound promotedFound
    by_cases isNew : old = location
    · subst old
      simp [RefinementWitness.bindConstructor, LocationMap.lookup?] at locationFound
      have leftEq : left = address := locationFound.symm
      subst left
      exact promotedAddressFresh payload right promotedFound
    · rw [witness.lookup_bindConstructor_location_other location old address info
        fieldKinds isNew] at locationFound
      exact valid.locationPromotionDisjoint old payload left right locationFound promotedFound

/-- A fresh boxed location preserves the same heap-address injectivity and
location/promoted-tag partition as a fresh constructor. -/
theorem RefinementWitness.WellFormed.bindBoxed
    {witness : RefinementWitness} (valid : witness.WellFormed)
    (location : Location) (address : Word32) (kind : BoxedScalarKind)
    (addressHeap : address.classify = .heap)
    (locationAddressFresh : ∀ old oldAddress,
      witness.locations.lookup? old = some oldAddress → oldAddress ≠ address)
    (promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.lookup? payload = some oldAddress → address ≠ oldAddress) :
    (witness.bindBoxed location address kind).WellFormed := by
  refine {
    locationHeap := ?_
    locationInjective := ?_
    promotedHeap := valid.promotedHeap
    promotedInjective := valid.promotedInjective
    locationPromotionDisjoint := ?_ }
  · intro old oldAddress found
    by_cases isNew : old = location
    · subst old
      simp [RefinementWitness.bindBoxed, LocationMap.lookup?] at found
      cases found
      exact addressHeap
    · rw [witness.lookup_bindBoxed_location_other location old address kind isNew] at found
      exact valid.locationHeap old oldAddress found
  · intro left right common leftFound rightFound
    by_cases leftNew : left = location
    · subst left
      simp [RefinementWitness.bindBoxed, LocationMap.lookup?] at leftFound
      have commonEq : common = address := leftFound.symm
      subst common
      by_cases rightNew : right = location
      · exact rightNew.symm
      · rw [witness.lookup_bindBoxed_location_other location right address kind
          rightNew] at rightFound
        exact False.elim ((locationAddressFresh right address rightFound) rfl)
    · rw [witness.lookup_bindBoxed_location_other location left address kind
        leftNew] at leftFound
      by_cases rightNew : right = location
      · subst right
        simp [RefinementWitness.bindBoxed, LocationMap.lookup?] at rightFound
        have commonEq : common = address := rightFound.symm
        subst common
        exact False.elim ((locationAddressFresh left address leftFound) rfl)
      · rw [witness.lookup_bindBoxed_location_other location right address kind
          rightNew] at rightFound
        exact valid.locationInjective left right common leftFound rightFound
  · intro old payload left right locationFound promotedFound
    by_cases isNew : old = location
    · subst old
      simp [RefinementWitness.bindBoxed, LocationMap.lookup?] at locationFound
      have leftEq : left = address := locationFound.symm
      subst left
      exact promotedAddressFresh payload right promotedFound
    · rw [witness.lookup_bindBoxed_location_other location old address kind isNew]
        at locationFound
      exact valid.locationPromotionDisjoint old payload left right locationFound promotedFound

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

theorem HeapReferenceRel.witnessExtension
    {before after : RefinementWitness} (extension : before.Extends after)
    {word : Word32} {location : Location}
    (related : HeapReferenceRel before word location) :
    HeapReferenceRel after word location := by
  cases related with
  | mapped found => exact .mapped (extension.locations _ _ found)

theorem TaggedReferenceRel.witnessExtension
    {before after : RefinementWitness} (extension : before.Extends after)
    {word : Word32} {payload : UInt64}
    (related : TaggedReferenceRel before word payload) :
    TaggedReferenceRel after word payload := by
  cases related with
  | immediate payload fits => exact .immediate payload fits
  | promoted found => exact .promoted (extension.promotedTags _ _ found)

theorem ObjectReferenceRel.witnessExtension
    {before after : RefinementWitness} (extension : before.Extends after)
    {word : Word32} {reference : ObjectRef}
    (related : ObjectReferenceRel before word reference) :
    ObjectReferenceRel after word reference := by
  cases related with
  | heap heapRelated => exact .heap (heapRelated.witnessExtension extension)
  | tagged taggedRelated => exact .tagged (taggedRelated.witnessExtension extension)

/-- ABI-indexed value refinement is monotone in proof-only witness metadata. -/
theorem ValueRel.witnessExtension
    {before after : RefinementWitness} (extension : before.Extends after)
    {kind : AbiKind} {concrete : LaneValue} {semantic : Value}
    (related : ValueRel before kind concrete semantic) :
    ValueRel after kind concrete semantic := by
  cases related with
  | object heapRelated => exact .object (heapRelated.witnessExtension extension)
  | tagged taggedRelated => exact .tagged (taggedRelated.witnessExtension extension)
  | tobject objectRelated => exact .tobject (objectRelated.witnessExtension extension)
  | erased => exact .erased
  | reuseNone => exact .reuseNone
  | reuseSome heapRelated => exact .reuseSome (heapRelated.witnessExtension extension)
  | uint8 encoded => exact .uint8 encoded
  | uint16 encoded => exact .uint16 encoded
  | uint32 encoded => exact .uint32 encoded
  | uint64 => exact .uint64
  | usize => exact .usize

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

theorem ValueRel.new_boxed_result (witness : RefinementWitness)
    (location : Location) (address : Word32) (kind : BoxedScalarKind) :
    ValueRel (witness.bindBoxed location address kind) .tobject (.word32 address)
      (.object (.heap location)) :=
  .tobject (.heap (.mapped
    (RefinementWitness.lookup_bindBoxed_location witness location address kind)))

end Fir.Wasm.Concrete
