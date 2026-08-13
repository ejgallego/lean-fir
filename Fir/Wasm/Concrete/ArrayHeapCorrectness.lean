import Fir.Wasm.Concrete.ArrayAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- The semantic live cell introduced by one resident generic-Array
allocation. Capacity is retained representation state; only `elements` owns
children. -/
def semanticArrayCell (elements : Array Value) (capacity : Nat) : HeapCell := {
  object := .array elements capacity }

/-- The semantic state after allocating one generic Array. -/
def semanticArrayResult (runtime : RuntimeState) (elements : Array Value)
    (capacity : Nat) : RuntimeState := {
  runtime with
  heap := (runtime.nextLocation, semanticArrayCell elements capacity) :: runtime.heap
  nextLocation := runtime.nextLocation + 1 }

@[simp] theorem alloc_array_eq (runtime : RuntimeState) (elements : Array Value)
    (capacity : Nat) :
    alloc runtime (.array elements capacity) =
      (semanticArrayResult runtime elements capacity,
        .heap runtime.nextLocation) := by
  rfl

/-- Fresh resident-Array allocation extends the complete live-heap relation.
The theorem exposes the semantic allocation result, exact fresh reference,
and a monotone witness extension; it assumes only pointwise refinement of the
live input prefix. -/
theorem allocateResidentArray_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (words : Array Word32) (elements : Array Value)
    (capacity : Nat) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (count : words.size = elements.size)
    (sizeCapacity : elements.size ≤ capacity)
    (sizeFits : elements.size < UInt32.size)
    (capacityFits : capacity < UInt32.size)
    (each : ∀ (index : Nat) (value : Value),
      elements[index]? = some value →
      ∃ word, words[index]? = some word ∧
        ValueRel witness .tobject (.word32 word) value)
    (allocated :
      allocateResidentArray state words capacity = .ok (result, address)) :
    let nextWitness :=
      witness.bindArray runtime.nextLocation address capacity
    witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel result nextWitness
        (semanticArrayResult runtime elements capacity) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      alloc runtime (.array elements capacity) =
        (semanticArrayResult runtime elements capacity,
          .heap runtime.nextLocation) := by
  dsimp only
  have wordsCapacity : words.size ≤ capacity := by omega
  have wordsFits : words.size < UInt32.size := by omega
  obtain ⟨middle, objectAllocation, _, _⟩ :=
    allocateResidentArray_decompose state result words capacity address
      wordsCapacity wordsFits capacityFits allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have memoryExtension := allocateResidentArray_prefixExtension state result words
    capacity address related.frontier wordsCapacity wordsFits capacityFits allocated
  obtain ⟨header, finalFrontier, objectRelated, refCountOne,
      ordinary, _⟩ :=
    allocateResidentArray_objectRel state result witness words elements capacity
      address related.frontier count sizeCapacity sizeFits capacityFits each allocated
  have locationFresh :
      witness.locations.lookup? runtime.nextLocation = none := by
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
    rw [freshAddress] at equal
    simp [headerBytes] at owned
    omega
  have witnessExtension := witness.bindArray_extends runtime.nextLocation address
    capacity locationFresh descriptorFresh
  have closurePersistent : ClosureAllocationsPersistent witness
      (witness.bindArray runtime.nextLocation address capacity) :=
    ClosureAllocationsPersistent.bindArray witness runtime.nextLocation address
      capacity
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
    obtain ⟨oldHeader, _, _, _, _, _, extent, payloadFits⟩ := promoted.header
    subst oldAddress
    simp [headerBytes] at payloadFits extent
    have addressEq := freshAddress
    omega
  obtain ⟨addressHeap, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address header
      objectRelated.headerRead
  have witnessWellFormed := related.witnessWellFormed.bindArray
    runtime.nextLocation address capacity addressHeap locationAddressFresh
      promotedAddressFresh
  have objectRelatedNext := objectRelated.witnessExtension witnessExtension
  have newRegion : ∃ newHeader,
      Header.read result.memory address = .ok newHeader ∧
      headerBytes ≤ newHeader.allocationBytes.toNat ∧
      newHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + newHeader.allocationBytes.toNat ≤ result.heapCursor := by
    refine ⟨header, rawHeaderRead, headerMinimum, headerAligned, ?_⟩
    rw [objectRelatedNext.allocationBytes]
    exact objectRelatedNext.extent
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial memoryExtension address freshAddress
      (fun other different =>
        witness.lookup_bindArray_descriptor_other runtime.nextLocation address
          other capacity different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindArray runtime.nextLocation address capacity) address
      (semanticArrayCell elements capacity) := by
    apply LiveCellRel.array
      (RefinementWitness.lookup_bindArray_descriptor witness runtime.nextLocation
        address capacity)
      (by rfl) objectRelatedNext
    · simpa [semanticArrayCell] using refCountOne
    · simpa [semanticArrayCell] using ordinary
    · rfl
  refine ⟨witnessExtension, closurePersistent, ?_,
    ValueRel.new_array_result witness runtime.nextLocation address capacity,
    alloc_array_eq runtime elements capacity⟩
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
        simpa [semanticArrayResult, findCell?, isNew, Ne.symm isNew] using found
      exact Nat.lt_trans (related.locationsBeforeNext location cell oldFound)
        (Nat.lt_succ_self runtime.nextLocation)
  · have cursorGrowth : state.heapCursor + headerBytes ≤ result.heapCursor := by
      rw [← freshAddress]
      exact objectRelatedNext.headerOwned
    have oldFuel := related.releaseFuelBound
    simp [semanticArrayResult, headerBytes] at oldFuel cursorGrowth ⊢
    omega
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact objectRelatedNext.headerOwned
    · rw [witness.lookup_bindArray_descriptor_other runtime.nextLocation address
        other capacity isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        memoryExtension.cursor
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticArrayCell elements capacity := by
        simpa [semanticArrayResult, findCell?] using found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindArray_location witness runtime.nextLocation
          address capacity,
        .live newCellRelated⟩
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticArrayResult, findCell?, isNew, Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension memoryExtension).witnessExtension
          witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindArray, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticArrayCell elements capacity,
        by simp [semanticArrayResult, findCell?], .live newCellRelated⟩
    · rw [witness.lookup_bindArray_location_other runtime.nextLocation location
        address capacity isNew] at mapped
      obtain ⟨cell, oldFound, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticArrayResult, findCell?, isNew, Ne.symm isNew],
        (cellRelated.prefixExtension memoryExtension).witnessExtension
          witnessExtension⟩
  · intro payload concreteAddress mapped
    exact ((related.promoted payload concreteAddress mapped).prefixExtension
      memoryExtension).witnessExtension witnessExtension

end Fir.Wasm.Concrete
