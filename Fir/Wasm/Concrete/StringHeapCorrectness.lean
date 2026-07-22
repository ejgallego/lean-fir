import Fir.Wasm.Concrete.HeapRefinement

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- The semantic heap cell introduced by one string literal. -/
def semanticStringCell (value : String) : HeapCell := {
  object := .string value }

/-- The semantic runtime state after allocating one string literal. -/
def semanticStringResult (runtime : RuntimeState) (value : String) : RuntimeState := {
  runtime with
  heap := (runtime.nextLocation, semanticStringCell value) :: runtime.heap
  nextLocation := runtime.nextLocation + 1 }

theorem semanticLiteral_string_eq (runtime : RuntimeState) (value : String) :
    literal runtime (.str value) =
      (semanticStringResult runtime value,
        .object (.heap runtime.nextLocation)) := by
  simp [literal, alloc, semanticStringResult, semanticStringCell]

/-- Fresh concrete UTF-8 allocation extends the complete live-heap relation
and relates the allocated wasm32 address to the fresh semantic string. -/
theorem allocateString_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (value : String) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (allocated : allocateString state value = .ok (result, address)) :
    let nextWitness := witness.bindString runtime.nextLocation address value
    LiveHeapRel result nextWitness (semanticStringResult runtime value) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨_, _, _, objectAllocation, _, _⟩ :=
    allocateString_decompose state result value address allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have extension := allocateString_prefixExtension state result value address
    related.frontier allocated
  obtain ⟨finalFrontier, header, objectRelated, ordinary, refCountOne⟩ :=
    allocateString_objectRel state result value address related.frontier allocated
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
  have witnessExtension := witness.bindString_extends runtime.nextLocation address
    value locationFresh descriptorFresh
  have locationAddressFresh : ∀ old oldAddress,
      witness.locations.lookup? old = some oldAddress → oldAddress ≠ address := by
    intro old oldAddress found equal
    obtain ⟨cell, _, cellRelated⟩ :=
      related.concreteToSemantic old oldAddress found
    have owned := cellRelated.headerOwned
    subst oldAddress
    simp [headerBytes] at owned
    omega
  have promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.Contains payload oldAddress → address ≠ oldAddress := by
    intro payload oldAddress found equal
    have promoted := related.promoted payload oldAddress found
    obtain ⟨oldHeader, _, _, _, _, _, extent, payloadFits⟩ := promoted.header
    subst oldAddress
    simp [headerBytes] at payloadFits extent
    omega
  obtain ⟨addressHeap, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address header
      objectRelated.headerRead
  have witnessWellFormed := related.witnessWellFormed.bindString
    runtime.nextLocation address value addressHeap locationAddressFresh
      promotedAddressFresh
  have newRegion : ∃ newHeader,
      Header.read result.memory address = .ok newHeader ∧
      headerBytes ≤ newHeader.allocationBytes.toNat ∧
      newHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + newHeader.allocationBytes.toNat ≤ result.heapCursor :=
    ⟨header, rawHeaderRead, headerMinimum, headerAligned, objectRelated.extent⟩
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial extension address freshAddress
      (fun other different =>
        witness.lookup_bindString_descriptor_other runtime.nextLocation address
          other value different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindString runtime.nextLocation address value) address
      (semanticStringCell value) := by
    apply LiveCellRel.string
      (RefinementWitness.lookup_bindString_descriptor witness runtime.nextLocation
        address value)
      (by rfl) objectRelated
    · simpa [semanticStringCell] using refCountOne
    · simpa [semanticStringCell] using ordinary
    · rfl
  refine ⟨?_, ValueRel.new_string_result witness runtime.nextLocation address value⟩
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
        simpa [semanticStringResult, findCell?, isNew, Ne.symm isNew] using found
      have oldBefore := related.locationsBeforeNext location cell oldFound
      exact Nat.lt_trans oldBefore (Nat.lt_succ_self runtime.nextLocation)
  · have cursorGrowth : state.heapCursor + headerBytes ≤ result.heapCursor := by
      rw [← freshAddress]
      exact objectRelated.headerOwned
    have oldFuel := related.releaseFuelBound
    simp [semanticStringResult, headerBytes] at oldFuel cursorGrowth ⊢
    omega
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact objectRelated.headerOwned
    · rw [witness.lookup_bindString_descriptor_other runtime.nextLocation address
        other value isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticStringCell value := by
        simpa [semanticStringResult, findCell?] using found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindString_location witness runtime.nextLocation
          address value,
        .live newCellRelated⟩
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticStringResult, findCell?, isNew, Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindString, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticStringCell value,
        by simp [semanticStringResult, findCell?], .live newCellRelated⟩
    · rw [witness.lookup_bindString_location_other runtime.nextLocation location
        address value isNew] at mapped
      obtain ⟨cell, oldFound, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticStringResult, findCell?, isNew, Ne.symm isNew],
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro payload concreteAddress mapped
    exact ((related.promoted payload concreteAddress mapped).prefixExtension extension)
      |>.witnessExtension witnessExtension

end Fir.Wasm.Concrete
