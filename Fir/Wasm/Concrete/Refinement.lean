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
  | closure (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
  | boxed (kind : BoxedScalarKind)
  | promotedTag (payload : UInt64)
  | natural (value : Nat)
  deriving Inhabited, BEq, Repr

abbrev DescriptorMap := List (Word32 × AllocationDescriptor)

/-- Deterministic module-level table of static closure capture descriptors.
Concrete closure headers store a checked index into this table so ownership
traversal can distinguish object captures from scalar lanes at run time. -/
abbrev ClosureDescriptorTable := Array (Array AbiKind)

def LocationMap.lookup? : LocationMap → Location → Option Word32
  | [], _ => none
  | (candidate, address) :: rest, location =>
      if candidate = location then some address else lookup? rest location

/-- One semantic tagged payload may have several immutable concrete
representations: `encodeTagged` allocates afresh rather than interning. -/
def PromotedTags.Contains (tags : PromotedTags) (payload : UInt64)
    (address : Word32) : Prop :=
  (payload, address) ∈ tags

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
  /-- The deterministic generated-function table for this module. Heap
  closure proofs consult this proof-only copy, which allocation extensions
  preserve rather than replacing per object. -/
  closureDispatch : Array Lean.Name := #[]
  /-- Static capture descriptors indexed by closure-header `aux3`. This is
  immutable module metadata and is preserved by every witness extension. -/
  closureDescriptors : ClosureDescriptorTable := #[]
  deriving Inhabited, Repr

def RefinementWitness.withClosureDispatch (witness : RefinementWitness)
    (dispatch : Array Lean.Name) : RefinementWitness :=
  { witness with closureDispatch := dispatch }

def RefinementWitness.withClosureDescriptors (witness : RefinementWitness)
    (descriptors : ClosureDescriptorTable) : RefinementWitness :=
  { witness with closureDescriptors := descriptors }

def RefinementWitness.withClosureTables (witness : RefinementWitness)
    (dispatch : Array Lean.Name) (descriptors : ClosureDescriptorTable) :
    RefinementWitness :=
  { witness with closureDispatch := dispatch, closureDescriptors := descriptors }

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

def RefinementWitness.bindClosure (witness : RefinementWitness)
    (location : Location) (address : Word32) (function : Lean.Name)
    (arity : Nat) (captureKinds : Array AbiKind) : RefinementWitness :=
  { witness with
      locations := (location, address) :: witness.locations
      descriptors := (address, .closure function arity captureKinds) ::
        witness.descriptors }

/-- Replace the proof-only active constructor descriptor at an existing
address. Location and promoted-tag identities are unchanged; the new head
entry shadows the allocation-time descriptor after successful in-place
reuse. -/
def RefinementWitness.rebindConstructor (witness : RefinementWitness)
    (address : Word32) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) : RefinementWitness :=
  { witness with
      descriptors := (address, .constructor info fieldKinds) ::
        witness.descriptors }

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

@[simp] theorem RefinementWitness.contains_promoteTag_self
    (witness : RefinementWitness) (payload : UInt64) (address : Word32) :
    (witness.promoteTag payload address).promotedTags.Contains payload address := by
  simp [RefinementWitness.promoteTag, PromotedTags.Contains]

@[simp] theorem RefinementWitness.lookup_promoteTag_descriptor
    (witness : RefinementWitness) (payload : UInt64) (address : Word32) :
    (witness.promoteTag payload address).descriptors.lookup? address =
      some (.promotedTag payload) := by
  simp [RefinementWitness.promoteTag, DescriptorMap.lookup?]

theorem RefinementWitness.lookup_promoteTag_descriptor_other
    (witness : RefinementWitness) (payload : UInt64) (address other : Word32)
    (different : address.value ≠ other.value) :
    (witness.promoteTag payload address).descriptors.lookup? other =
      witness.descriptors.lookup? other := by
  simp [RefinementWitness.promoteTag, DescriptorMap.lookup?, different]

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

@[simp] theorem RefinementWitness.lookup_rebindConstructor_descriptor
    (witness : RefinementWitness) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    (witness.rebindConstructor address info fieldKinds).descriptors.lookup? address =
      some (.constructor info fieldKinds) := by
  simp [RefinementWitness.rebindConstructor, DescriptorMap.lookup?]

theorem RefinementWitness.lookup_rebindConstructor_descriptor_other
    (witness : RefinementWitness) (address other : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (different : address.value ≠ other.value) :
    (witness.rebindConstructor address info fieldKinds).descriptors.lookup? other =
      witness.descriptors.lookup? other := by
  simp [RefinementWitness.rebindConstructor, DescriptorMap.lookup?, different]

@[simp] theorem RefinementWitness.rebindConstructor_locations
    (witness : RefinementWitness) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    (witness.rebindConstructor address info fieldKinds).locations =
      witness.locations := rfl

@[simp] theorem RefinementWitness.rebindConstructor_promotedTags
    (witness : RefinementWitness) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    (witness.rebindConstructor address info fieldKinds).promotedTags =
      witness.promotedTags := rfl

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

@[simp] theorem RefinementWitness.lookup_bindClosure_location
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind) :
    (witness.bindClosure location address function arity captureKinds).locations.lookup?
        location = some address := by
  simp [RefinementWitness.bindClosure, LocationMap.lookup?]

@[simp] theorem RefinementWitness.lookup_bindClosure_descriptor
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind) :
    (witness.bindClosure location address function arity captureKinds).descriptors.lookup?
        address = some (.closure function arity captureKinds) := by
  simp [RefinementWitness.bindClosure, DescriptorMap.lookup?]

theorem RefinementWitness.lookup_bindClosure_location_other
    (witness : RefinementWitness) (location other : Location) (address : Word32)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (different : other ≠ location) :
    (witness.bindClosure location address function arity captureKinds).locations.lookup?
        other = witness.locations.lookup? other := by
  simp [RefinementWitness.bindClosure, LocationMap.lookup?, Ne.symm different]

theorem RefinementWitness.lookup_bindClosure_descriptor_other
    (witness : RefinementWitness) (location : Location) (address other : Word32)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (different : address.value ≠ other.value) :
    (witness.bindClosure location address function arity captureKinds).descriptors.lookup?
        other = witness.descriptors.lookup? other := by
  simp [RefinementWitness.bindClosure, DescriptorMap.lookup?, different]

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
    before.promotedTags.Contains payload address →
    after.promotedTags.Contains payload address
  descriptors : ∀ address descriptor,
    before.descriptors.lookup? address = some descriptor →
    after.descriptors.lookup? address = some descriptor
  closureDispatch : after.closureDispatch = before.closureDispatch
  closureDescriptors : after.closureDescriptors = before.closureDescriptors

namespace RefinementWitness.Extends

theorem refl (witness : RefinementWitness) : witness.Extends witness := by
  exact ⟨fun _ _ found => found, fun _ _ found => found,
    fun _ _ found => found, rfl, rfl⟩

theorem trans {first second third : RefinementWitness}
    (left : first.Extends second) (right : second.Extends third) :
    first.Extends third := by
  exact ⟨
    fun _ _ found => right.locations _ _ (left.locations _ _ found),
    fun _ _ found => right.promotedTags _ _ (left.promotedTags _ _ found),
    fun _ _ found => right.descriptors _ _ (left.descriptors _ _ found),
    right.closureDispatch.trans left.closureDispatch,
    right.closureDescriptors.trans left.closureDescriptors⟩

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
    descriptors := ?_
    closureDispatch := rfl
    closureDescriptors := rfl }
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

/-- Binding a fresh closure extends every previously visible location,
promoted tag, and allocation descriptor. -/
theorem RefinementWitness.bindClosure_extends
    (witness : RefinementWitness) (location : Location) (address : Word32)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (locationFresh : witness.locations.lookup? location = none)
    (descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value) :
    witness.Extends
      (witness.bindClosure location address function arity captureKinds) := by
  refine {
    locations := ?_
    promotedTags := ?_
    descriptors := ?_
    closureDispatch := rfl
    closureDescriptors := rfl }
  · intro old oldAddress found
    have different : old ≠ location := by
      intro equal
      subst old
      simp [locationFresh] at found
    rw [witness.lookup_bindClosure_location_other location old address function
      arity captureKinds different]
    exact found
  · intro payload oldAddress found
    exact found
  · intro old descriptor found
    rw [witness.lookup_bindClosure_descriptor_other location address old function
      arity captureKinds (descriptorFresh old descriptor found)]
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
    descriptors := ?_
    closureDispatch := rfl
    closureDescriptors := rfl }
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

/-- Recording a fresh promoted representation preserves every old lookup and
every old promoted representation, including representations of the same
payload at other addresses. -/
theorem RefinementWitness.promoteTag_extends
    (witness : RefinementWitness) (payload : UInt64) (address : Word32)
    (descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value) :
    witness.Extends (witness.promoteTag payload address) := by
  refine {
    locations := fun _ _ found => found
    promotedTags := ?_
    descriptors := ?_
    closureDispatch := rfl
    closureDescriptors := rfl }
  · intro oldPayload oldAddress found
    change (oldPayload, oldAddress) ∈
      (payload, address) :: witness.promotedTags
    exact List.Mem.tail _ found
  · intro old descriptor found
    rw [witness.lookup_promoteTag_descriptor_other payload address old
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
    witness.promotedTags.Contains payload address → address.classify = .heap
  promotedInjective : ∀ left right address,
    witness.promotedTags.Contains left address →
    witness.promotedTags.Contains right address → left = right
  locationPromotionDisjoint : ∀ location payload left right,
    witness.locations.lookup? location = some left →
    witness.promotedTags.Contains payload right → left ≠ right

/-- Rebinding only a descriptor leaves all reference-identity invariants
definitionally unchanged. -/
theorem RefinementWitness.WellFormed.rebindConstructor
    {witness : RefinementWitness} (valid : witness.WellFormed)
    (address : Word32) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) :
    (witness.rebindConstructor address info fieldKinds).WellFormed := by
  refine {
    locationHeap := valid.locationHeap
    locationInjective := valid.locationInjective
    promotedHeap := valid.promotedHeap
    promotedInjective := valid.promotedInjective
    locationPromotionDisjoint := valid.locationPromotionDisjoint }

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
      witness.promotedTags.Contains payload oldAddress → address ≠ oldAddress) :
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

/-- A fresh closure uses the same location identity extension as every other
ordinary heap allocation; its descriptor does not affect witness injectivity. -/
theorem RefinementWitness.WellFormed.bindClosure
    {witness : RefinementWitness} (valid : witness.WellFormed)
    (location : Location) (address : Word32) (function : Lean.Name)
    (arity : Nat) (captureKinds : Array AbiKind)
    (addressHeap : address.classify = .heap)
    (locationAddressFresh : ∀ old oldAddress,
      witness.locations.lookup? old = some oldAddress → oldAddress ≠ address)
    (promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.Contains payload oldAddress → address ≠ oldAddress) :
    (witness.bindClosure location address function arity captureKinds).WellFormed := by
  refine {
    locationHeap := ?_
    locationInjective := ?_
    promotedHeap := valid.promotedHeap
    promotedInjective := valid.promotedInjective
    locationPromotionDisjoint := ?_ }
  · intro old oldAddress found
    by_cases isNew : old = location
    · subst old
      simp [RefinementWitness.bindClosure, LocationMap.lookup?] at found
      cases found
      exact addressHeap
    · rw [witness.lookup_bindClosure_location_other location old address function
        arity captureKinds isNew] at found
      exact valid.locationHeap old oldAddress found
  · intro left right common leftFound rightFound
    by_cases leftNew : left = location
    · subst left
      simp [RefinementWitness.bindClosure, LocationMap.lookup?] at leftFound
      have commonEq : common = address := leftFound.symm
      subst common
      by_cases rightNew : right = location
      · exact rightNew.symm
      · rw [witness.lookup_bindClosure_location_other location right address function
          arity captureKinds rightNew] at rightFound
        exact False.elim ((locationAddressFresh right address rightFound) rfl)
    · rw [witness.lookup_bindClosure_location_other location left address function
        arity captureKinds leftNew] at leftFound
      by_cases rightNew : right = location
      · subst right
        simp [RefinementWitness.bindClosure, LocationMap.lookup?] at rightFound
        have commonEq : common = address := rightFound.symm
        subst common
        exact False.elim ((locationAddressFresh left address leftFound) rfl)
      · rw [witness.lookup_bindClosure_location_other location right address function
          arity captureKinds rightNew] at rightFound
        exact valid.locationInjective left right common leftFound rightFound
  · intro old payload left right locationFound promotedFound
    by_cases isNew : old = location
    · subst old
      simp [RefinementWitness.bindClosure, LocationMap.lookup?] at locationFound
      have leftEq : left = address := locationFound.symm
      subst left
      exact promotedAddressFresh payload right promotedFound
    · rw [witness.lookup_bindClosure_location_other location old address function
        arity captureKinds isNew] at locationFound
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
      witness.promotedTags.Contains payload oldAddress → address ≠ oldAddress) :
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

/-- Adding a fresh concrete address for a promoted tag preserves witness
well-formedness even when the same payload already has another address. -/
theorem RefinementWitness.WellFormed.promoteTag
    {witness : RefinementWitness} (valid : witness.WellFormed)
    (payload : UInt64) (address : Word32)
    (addressHeap : address.classify = .heap)
    (locationAddressFresh : ∀ location oldAddress,
      witness.locations.lookup? location = some oldAddress → oldAddress ≠ address)
    (promotedAddressFresh : ∀ oldPayload oldAddress,
      witness.promotedTags.Contains oldPayload oldAddress → oldAddress ≠ address) :
    (witness.promoteTag payload address).WellFormed := by
  refine {
    locationHeap := valid.locationHeap
    locationInjective := valid.locationInjective
    promotedHeap := ?_
    promotedInjective := ?_
    locationPromotionDisjoint := ?_ }
  · intro oldPayload oldAddress found
    change (oldPayload, oldAddress) ∈
      (payload, address) :: witness.promotedTags at found
    rcases List.mem_cons.mp found with new | old
    · have addressEq : oldAddress = address := congrArg Prod.snd new
      rw [addressEq]
      exact addressHeap
    · exact valid.promotedHeap oldPayload oldAddress old
  · intro left right common leftFound rightFound
    change (left, common) ∈ (payload, address) :: witness.promotedTags at leftFound
    change (right, common) ∈ (payload, address) :: witness.promotedTags at rightFound
    rcases List.mem_cons.mp leftFound with leftNew | leftOld
    · rcases List.mem_cons.mp rightFound with rightNew | rightOld
      · exact (congrArg Prod.fst leftNew).trans (congrArg Prod.fst rightNew).symm
      · have commonEq : common = address := congrArg Prod.snd leftNew
        rw [commonEq] at rightOld
        exact False.elim ((promotedAddressFresh right address rightOld) rfl)
    · rcases List.mem_cons.mp rightFound with rightNew | rightOld
      · have commonEq : common = address := congrArg Prod.snd rightNew
        rw [commonEq] at leftOld
        exact False.elim ((promotedAddressFresh left address leftOld) rfl)
      · exact valid.promotedInjective left right common leftOld rightOld
  · intro location oldPayload left right locationFound promotedFound
    change (oldPayload, right) ∈
      (payload, address) :: witness.promotedTags at promotedFound
    rcases List.mem_cons.mp promotedFound with new | old
    · have rightEq : right = address := congrArg Prod.snd new
      rw [rightEq]
      exact locationAddressFresh location left locationFound
    · exact valid.locationPromotionDisjoint location oldPayload left right
        locationFound old

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
      (found : witness.promotedTags.Contains payload address) :
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

/-- Descriptor rebinding preserves every mapped heap reference because the
semantic-location map is unchanged. -/
theorem HeapReferenceRel.rebindConstructor
    {witness : RefinementWitness} {word : Word32} {location : Location}
    (related : HeapReferenceRel witness word location)
    (address : Word32) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) :
    HeapReferenceRel (witness.rebindConstructor address info fieldKinds)
      word location := by
  cases related with
  | mapped found =>
      exact .mapped (by
        simpa [RefinementWitness.rebindConstructor] using found)

/-- Descriptor rebinding preserves both immediate and promoted tagged-value
representations because the promoted-tag table is unchanged. -/
theorem TaggedReferenceRel.rebindConstructor
    {witness : RefinementWitness} {word : Word32} {payload : UInt64}
    (related : TaggedReferenceRel witness word payload)
    (address : Word32) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) :
    TaggedReferenceRel (witness.rebindConstructor address info fieldKinds)
      word payload := by
  cases related with
  | immediate payload fits => exact .immediate payload fits
  | promoted found =>
      exact .promoted (by
        simpa [RefinementWitness.rebindConstructor] using found)

theorem ObjectReferenceRel.rebindConstructor
    {witness : RefinementWitness} {word : Word32} {reference : ObjectRef}
    (related : ObjectReferenceRel witness word reference)
    (address : Word32) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) :
    ObjectReferenceRel (witness.rebindConstructor address info fieldKinds)
      word reference := by
  cases related with
  | heap heapRelated =>
      exact .heap (heapRelated.rebindConstructor address info fieldKinds)
  | tagged taggedRelated =>
      exact .tagged (taggedRelated.rebindConstructor address info fieldKinds)

/-- All ABI value relations survive active-descriptor rebinding; only heap
decoding, not lane/reference identity, consults descriptors. -/
theorem ValueRel.rebindConstructor
    {witness : RefinementWitness} {kind : AbiKind}
    {concrete : LaneValue} {semantic : Value}
    (related : ValueRel witness kind concrete semantic)
    (address : Word32) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) :
    ValueRel (witness.rebindConstructor address info fieldKinds)
      kind concrete semantic := by
  cases related with
  | object heapRelated =>
      exact .object (heapRelated.rebindConstructor address info fieldKinds)
  | tagged taggedRelated =>
      exact .tagged (taggedRelated.rebindConstructor address info fieldKinds)
  | tobject objectRelated =>
      exact .tobject (objectRelated.rebindConstructor address info fieldKinds)
  | erased => exact .erased
  | reuseNone => exact .reuseNone
  | reuseSome heapRelated =>
      exact .reuseSome (heapRelated.rebindConstructor address info fieldKinds)
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
    (notPromoted : ∀ address,
      ¬ witness.promotedTags.Contains payload address) :
    word ≠ Word32.zero := by
  cases related with
  | immediate payload fits => exact Word32.immediate_ne_zero payload.toNat fits
  | promoted found => exact False.elim (notPromoted _ found)

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
  .tagged (.promoted (RefinementWitness.contains_promoteTag_self witness payload address))

theorem ValueRel.new_promoted_tobject (witness : RefinementWitness)
    (payload : UInt64) (address : Word32) :
    ValueRel (witness.promoteTag payload address) .tobject (.word32 address)
      (.object (.tagged payload)) :=
  .tobject (.tagged
    (.promoted (RefinementWitness.contains_promoteTag_self witness payload address)))

theorem ValueRel.new_boxed_result (witness : RefinementWitness)
    (location : Location) (address : Word32) (kind : BoxedScalarKind) :
    ValueRel (witness.bindBoxed location address kind) .tobject (.word32 address)
      (.object (.heap location)) :=
  .tobject (.heap (.mapped
    (RefinementWitness.lookup_bindBoxed_location witness location address kind)))

end Fir.Wasm.Concrete
