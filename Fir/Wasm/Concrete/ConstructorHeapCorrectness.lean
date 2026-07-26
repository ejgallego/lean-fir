import Fir.Wasm.Concrete.ConstructorAllocationCorrectness
import Fir.Wasm.Concrete.PromotedTagCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

def semanticConstructorObject (info : LCNF.CtorInfo) (fields : Array Value) :
    ConstructorObject := {
  tag := info.cidx
  objectFields := fields
  usizeFields := Array.replicate info.usize 0
  scalarFields := [] }

def semanticConstructorCell (info : LCNF.CtorInfo) (fields : Array Value) :
    HeapCell := { object := .ctor (semanticConstructorObject info fields) }

def semanticConstructorResult (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fields : Array Value) : RuntimeState := {
  runtime with
  heap := (runtime.nextLocation, semanticConstructorCell info fields) :: runtime.heap
  nextLocation := runtime.nextLocation + 1 }

@[simp] theorem allocCtor_nonempty_eq (runtime : RuntimeState)
    (info : LCNF.CtorInfo) (fields : Array Value)
    (arity : fields.size = info.size)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)) :
    allocCtor runtime info fields = .ok
      (semanticConstructorResult runtime info fields,
        .object (.heap runtime.nextLocation)) := by
  unfold allocCtor
  simp [arity, nonempty, semanticConstructorResult, semanticConstructorCell,
    semanticConstructorObject, alloc]
  rfl

@[simp] theorem allocCtor_empty_eq (runtime : RuntimeState)
    (info : LCNF.CtorInfo) (fields : Array Value)
    (arity : fields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0) :
    allocCtor runtime info fields =
      .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  simp [allocCtor, arity, empty.1.1, empty.1.2, empty.2]
  rfl

/-- Empty constructors use the tagged representation and leave the semantic
heap unchanged. The concrete word may be immediate or a fresh promoted-tag
object; both cases preserve `LiveHeapRel` and refine the exact tagged ABI. -/
theorem allocateConstructor_empty_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fields : Array Word32) (semanticFields : Array Value) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (allocated : allocateConstructor state info fields = .ok (result, word)) :
    ∃ nextWitness,
      LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tagged (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  have encoded : encodeTagged state (UInt64.ofNat info.cidx) =
      .ok (result, word) := by
    unfold allocateConstructor at allocated
    rw [if_pos arity] at allocated
    rw [uint32Field_eq_ok "constructor tag" info.cidx tagFits] at allocated
    simp only [Bind.bind, Except.bind] at allocated
    rw [if_pos (by simp [empty.1.1, empty.1.2, empty.2])] at allocated
    simpa [UInt32.toNat_ofNat_of_lt' tagFits] using allocated
  obtain ⟨nextWitness, heapRelated, valueRelated⟩ :=
    encodeTagged_liveHeapRel state result witness runtime
      (UInt64.ofNat info.cidx) word related encoded
  exact ⟨nextWitness, heapRelated, valueRelated.tobject_tagged_to_tagged,
    allocCtor_empty_eq runtime info semanticFields semanticArity empty⟩

/-- Monotone-witness form of empty constructor allocation. It is the form
needed when a promoted tag grows the concrete heap while old locals remain
live across the generated host call. -/
theorem allocateConstructor_empty_liveHeapRel_extends
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fields : Array Word32) (semanticFields : Array Value) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (allocated : allocateConstructor state info fields = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tagged (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  have encoded : encodeTagged state (UInt64.ofNat info.cidx) =
      .ok (result, word) := by
    unfold allocateConstructor at allocated
    rw [if_pos arity] at allocated
    rw [uint32Field_eq_ok "constructor tag" info.cidx tagFits] at allocated
    simp only [Bind.bind, Except.bind] at allocated
    rw [if_pos (by simp [empty.1.1, empty.1.2, empty.2])] at allocated
    simpa [UInt32.toNat_ofNat_of_lt' tagFits] using allocated
  obtain ⟨nextWitness, extension, heapRelated, valueRelated⟩ :=
    encodeTagged_liveHeapRel_extends state result witness runtime
      (UInt64.ofNat info.cidx) word related encoded
  exact ⟨nextWitness, extension, heapRelated,
    valueRelated.tobject_tagged_to_tagged,
    allocCtor_empty_eq runtime info semanticFields semanticArity empty⟩

/-- Empty constructor allocation additionally preserves every mapped
allocation's retained extent, whether the tagged result is immediate or
promoted. -/
theorem allocateConstructor_empty_liveHeapRel_extends_with_capacity
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fields : Array Word32) (semanticFields : Array Value) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (allocated : allocateConstructor state info fields = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tagged (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) ∧
      MappedHeaderCapacityTransport state result witness := by
  have encoded : encodeTagged state (UInt64.ofNat info.cidx) =
      .ok (result, word) := by
    unfold allocateConstructor at allocated
    rw [if_pos arity] at allocated
    rw [uint32Field_eq_ok "constructor tag" info.cidx tagFits] at allocated
    simp only [Bind.bind, Except.bind] at allocated
    rw [if_pos (by simp [empty.1.1, empty.1.2, empty.2])] at allocated
    simpa [UInt32.toNat_ofNat_of_lt' tagFits] using allocated
  obtain ⟨nextWitness, extension, heapRelated, valueRelated,
      capacityTransport⟩ :=
    encodeTagged_liveHeapRel_extends_with_capacity state result witness runtime
      (UInt64.ofNat info.cidx) word related encoded
  exact ⟨nextWitness, extension, heapRelated,
    valueRelated.tobject_tagged_to_tagged,
    allocCtor_empty_eq runtime info semanticFields semanticArity empty,
    capacityTransport⟩

/-- A nonempty constructor allocation extends the complete concrete/semantic
live-heap relation and relates the returned concrete address to the fresh
semantic location.  This is the W6.1 operation-level refinement boundary
needed by the W2 constructor host contract. -/
theorem allocateConstructor_nonempty_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (fields : Array Word32)
    (semanticFields : Array Value) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (allocated : allocateConstructor state info fields = .ok (result, address)) :
    let nextWitness := witness.bindConstructor runtime.nextLocation address info fieldKinds
    LiveHeapRel result nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨middle, objectAllocation, _, _⟩ :=
    allocateConstructor_nonempty_decompose state result info fields address arity
      nonempty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have extension := allocateConstructor_nonempty_prefixExtension state result info fields
    address related.frontier arity nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit allocated
  obtain ⟨finalFrontier, objectRelated, exactHeader⟩ :=
    allocateConstructor_nonempty_objectRel state result witness info fieldKinds fields
      semanticFields address related.frontier arity semanticArity fieldKindsSize
      fieldKindsValid fieldRelated nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit allocated
  have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
    cases found : witness.locations.lookup? runtime.nextLocation with
    | none => rfl
    | some oldAddress =>
        exfalso
        obtain ⟨cell, semanticFound, _⟩ :=
          related.concreteToSemantic runtime.nextLocation oldAddress found
        have beforeNext :=
          related.locationsBeforeNext runtime.nextLocation cell semanticFound
        exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    have addressEq := freshAddress
    omega
  have witnessExtension := witness.bindConstructor_extends runtime.nextLocation address
    info fieldKinds locationFresh descriptorFresh
  have locationAddressFresh : ∀ old oldAddress,
      witness.locations.lookup? old = some oldAddress → oldAddress ≠ address := by
    intro old oldAddress found equal
    obtain ⟨cell, _, cellRelated⟩ :=
      related.concreteToSemantic old oldAddress found
    have owned := cellRelated.headerOwned
    subst oldAddress
    simp [headerBytes] at owned
    have addressEq := freshAddress
    omega
  have promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.Contains payload oldAddress → address ≠ oldAddress := by
    intro payload oldAddress found equal
    have promoted := related.promoted payload oldAddress found
    obtain ⟨header, _, _, _, _, _, extent, payloadFits⟩ := promoted.header
    subst oldAddress
    simp [headerBytes] at payloadFits extent
    have addressEq := freshAddress
    omega
  let header := Header.forAllocation .constructor
    (ConstructorLayout.ofInfo info).allocationBytes false
      (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
      (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize)
  have headerRead : result.readLiveHeader address = .ok header := by
    simpa [header] using exactHeader
  have headerKind : header.kind = .constructor := rfl
  have headerRefCount : header.refCount.toNat = 1 := rfl
  have headerPersistent : header.persistent = false := rfl
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts result address header headerRead).1
  have witnessWellFormed := related.witnessWellFormed.bindConstructor
    runtime.nextLocation address info fieldKinds addressHeap locationAddressFresh
      promotedAddressFresh
  have objectRelatedNext := objectRelated.witnessExtension witnessExtension
  obtain ⟨_, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address header headerRead
  let layout := ConstructorLayout.ofInfo info
  have layoutMinimum : headerBytes ≤ layout.allocationBytes := by
    dsimp only [layout]
    exact Nat.le_trans (by omega) (align8_ge _)
  have layoutAligned : align8 layout.allocationBytes = layout.allocationBytes := by
    apply align8_eq_of_mod_eq_zero
    simpa [target, layout] using ConstructorLayout.ofInfo_allocation_aligned info
  have allocationEq :
      align8 (headerBytes + (layout.allocationBytes - headerBytes)) =
        layout.allocationBytes := by
    rw [Nat.add_sub_of_le layoutMinimum, layoutAligned]
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state middle .constructor
      (layout.allocationBytes - headerBytes) false
      (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
      (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize) address (by
        simpa [layout] using objectAllocation)
  have allocationPost := MemoryState.allocate_spec state rawState
    (align8 (headerBytes + (layout.allocationBytes - headerBytes))) address
      rawAllocation
  have layoutLt : layout.allocationBytes < UInt32.size := by
    have endWithin := allocationPost.endWithinAddressSpace
    have allocatedBytesEq :
        align8 (align8 (headerBytes + (layout.allocationBytes - headerBytes))) =
          layout.allocationBytes := by
      rw [align8_align8, allocationEq]
    have nonzero : address.value ≠ 0 := by
      intro zero
      have addressClass := allocationPost.addressClass
      simp [Word32.classify, zero] at addressClass
    have allocatedLt :
        align8 (align8 (headerBytes + (layout.allocationBytes - headerBytes))) <
          wordModulus := by omega
    rw [allocatedBytesEq] at allocatedLt
    simpa [wordModulus] using allocatedLt
  have headerCapacity : header.allocationBytes.toNat = layout.allocationBytes := by
    simpa [header, layout, Header.forAllocation] using
      UInt32.toNat_ofNat_of_lt' layoutLt
  have newExtent :
      address.value + header.allocationBytes.toNat ≤ result.heapCursor := by
    rw [headerCapacity]
    simpa [layout] using objectRelatedNext.extent
  have newRegion : ∃ newHeader,
      Header.read result.memory address = .ok newHeader ∧
      headerBytes ≤ newHeader.allocationBytes.toNat ∧
      newHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + newHeader.allocationBytes.toNat ≤ result.heapCursor :=
    ⟨header, rawHeaderRead, headerMinimum, headerAligned, newExtent⟩
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial extension address freshAddress
      (fun other different =>
        witness.lookup_bindConstructor_descriptor_other runtime.nextLocation address
          other info fieldKinds different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindConstructor runtime.nextLocation address info fieldKinds) address
      (semanticConstructorCell info semanticFields) := by
    apply LiveCellRel.constructor
      (RefinementWitness.lookup_bindConstructor_descriptor witness runtime.nextLocation
        address info fieldKinds)
      (by rfl) objectRelatedNext headerRead headerKind
    · simpa [semanticConstructorCell] using headerRefCount
    · simpa [semanticConstructorCell] using headerPersistent
    · rfl
  refine ⟨?_, ValueRel.new_constructor_result witness runtime.nextLocation address info
    fieldKinds⟩
  refine {
    frontier := finalFrontier
    witnessWellFormed
    locationsBeforeNext := ?_
    releaseFuelBound := ?_
    descriptorsOwned := ?_
    descriptorRegion
    descriptorDisjoint
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      change runtime.nextLocation < runtime.nextLocation + 1
      exact Nat.lt_succ_self runtime.nextLocation
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticConstructorResult, findCell?, isNew, Ne.symm isNew] using found
      have oldBefore := related.locationsBeforeNext location cell oldFound
      change location < runtime.nextLocation + 1
      exact Nat.lt_trans oldBefore (Nat.lt_succ_self runtime.nextLocation)
  · have cursorGrowth : state.heapCursor + headerBytes ≤ result.heapCursor := by
      rw [← freshAddress]
      exact objectRelatedNext.headerOwned
    have oldFuel := related.releaseFuelBound
    simp [semanticConstructorResult, headerBytes] at oldFuel cursorGrowth ⊢
    omega
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact objectRelatedNext.headerOwned
    · rw [witness.lookup_bindConstructor_descriptor_other runtime.nextLocation address
        other info fieldKinds isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticConstructorCell info semanticFields := by
        simpa [semanticConstructorResult, findCell?] using found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindConstructor_location witness runtime.nextLocation
          address info fieldKinds,
        .live newCellRelated⟩
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticConstructorResult, findCell?, isNew, Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindConstructor, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticConstructorCell info semanticFields,
        by simp [semanticConstructorResult, findCell?], .live newCellRelated⟩
    · rw [witness.lookup_bindConstructor_location_other runtime.nextLocation location
        address info fieldKinds isNew] at mapped
      obtain ⟨cell, oldFound, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticConstructorResult, findCell?, isNew, Ne.symm isNew],
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro payload concreteAddress mapped
    exact ((related.promoted payload concreteAddress mapped).prefixExtension extension)
      |>.witnessExtension witnessExtension

/-- Monotone-witness form of nonempty constructor allocation. The concrete
constructor binding is fresh in both witness maps, so every pre-existing
value relation survives the allocation. -/
theorem allocateConstructor_nonempty_liveHeapRel_extends
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (fields : Array Word32)
    (semanticFields : Array Value) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (allocated : allocateConstructor state info fields = .ok (result, address)) :
    let nextWitness :=
      witness.bindConstructor runtime.nextLocation address info fieldKinds
    witness.Extends nextWitness ∧
      LiveHeapRel result nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨_, objectAllocation, _, _⟩ :=
    allocateConstructor_nonempty_decompose state result info fields address arity
      nonempty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
    cases found : witness.locations.lookup? runtime.nextLocation with
    | none => rfl
    | some oldAddress =>
        exfalso
        obtain ⟨cell, semanticFound, _⟩ :=
          related.concreteToSemantic runtime.nextLocation oldAddress found
        have beforeNext :=
          related.locationsBeforeNext runtime.nextLocation cell semanticFound
        exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    omega
  have extension := witness.bindConstructor_extends runtime.nextLocation address
    info fieldKinds locationFresh descriptorFresh
  have refined := allocateConstructor_nonempty_liveHeapRel state result witness
    runtime info fieldKinds fields semanticFields address related arity semanticArity
    fieldKindsSize fieldKindsValid fieldRelated nonempty tagFits objectFieldsFit
    usizeFieldsFit scalarBytesFit allocated
  exact ⟨extension, refined.1, refined.2⟩

end Fir.Wasm.Concrete
