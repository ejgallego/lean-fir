import Fir.Wasm.Concrete.HeapRefinement
import Fir.Wasm.Concrete.FreshAllocationCorrectness

namespace Fir.Wasm.Concrete

/-- A successful promoted-tag allocation is one persistent natural object
followed by its immutable 64-bit payload write. -/
theorem allocatePromotedTag_decompose
    (state result : MemoryState) (payload : UInt64) (address : Word32)
    (allocated : allocatePromotedTag state payload = .ok (result, address)) :
    ∃ middle,
      state.allocateObject .natural 8 true promotedTagMarker 1 =
        .ok (middle, address) ∧
      middle.memory.writeUInt64 (address.value + headerBytes) payload =
        .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  unfold allocatePromotedTag at allocated
  dsimp only at allocated
  cases objectAllocation : state.allocateObject .natural 8 true
      promotedTagMarker 1 with
  | error failure =>
      rw [objectAllocation] at allocated
      change Except.error (ConcreteError.ofMemory failure) =
        Except.ok (result, address) at allocated
      contradiction
  | ok pair =>
      rcases pair with ⟨middle, actualAddress⟩
      rw [objectAllocation] at allocated
      change (do
        let memory ← liftMemory <| middle.memory.writeUInt64
          (actualAddress.value + headerBytes) payload
        return ({ middle with memory }, actualAddress)) =
          .ok (result, address) at allocated
      cases payloadWrite : middle.memory.writeUInt64
          (actualAddress.value + headerBytes) payload with
      | error failure =>
          rw [payloadWrite] at allocated
          change Except.error (ConcreteError.ofMemory failure) =
            Except.ok (result, address) at allocated
          contradiction
      | ok finalMemory =>
          rw [payloadWrite] at allocated
          change Except.ok ({ middle with memory := finalMemory }, actualAddress) =
            Except.ok (result, address) at allocated
          have pairEq : ({ middle with memory := finalMemory }, actualAddress) =
              (result, address) := Except.ok.inj allocated
          have resultEq : { middle with memory := finalMemory } = result :=
            congrArg Prod.fst pairEq
          have addressEq : actualAddress = address := congrArg Prod.snd pairEq
          subst result
          subst address
          exact ⟨middle, rfl, payloadWrite, rfl⟩

/-- The payload write of a promoted tag is disjoint from its common header. -/
theorem MemoryState.readLiveHeader_of_writePromotedTagPayload
    (state : MemoryState) (result : LinearMemory) (address : Word32)
    (payload : UInt64)
    (inBounds : address.value + headerBytes + 7 < state.memory.size)
    (written : state.memory.writeUInt64 (address.value + headerBytes) payload =
      .ok result) :
    ({ state with memory := result } : MemoryState).readLiveHeader address =
      state.readLiveHeader address := by
  have lane (offset : Nat) (offsetEnd : offset + 3 < headerBytes) :
      result.readUInt32 (address.value + offset) =
        state.memory.readUInt32 (address.value + offset) :=
    LinearMemory.readUInt32_of_writeUInt64_eq_ok_other state.memory result
      (address.value + headerBytes) (address.value + offset) payload inBounds written
      (by right; omega)
  have headerRead : Header.read result address = Header.read state.memory address := by
    unfold Header.read
    dsimp only
    rw [lane headerKindOffset (by decide)]
    rw [lane headerFlagsOffset (by decide)]
    rw [lane headerRefCountOffset (by decide)]
    rw [lane headerAllocationBytesOffset (by decide)]
    rw [lane headerAux0Offset (by decide)]
    rw [lane headerAux1Offset (by decide)]
    rw [lane headerAux2Offset (by decide)]
    rw [lane headerAux3Offset (by decide)]
  have sizeEq := LinearMemory.size_of_writeUInt64_eq_ok state.memory result
    (address.value + headerBytes) payload inBounds written
  unfold MemoryState.readLiveHeader
  dsimp only
  rw [headerRead, sizeEq]

/-- Installing a fresh promoted payload frames the complete old heap. -/
theorem allocatePromotedTag_prefixExtension
    (state result : MemoryState) (payload : UInt64) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocatePromotedTag state payload = .ok (result, address)) :
    state.PrefixExtension result := by
  obtain ⟨middle, objectAllocation, payloadWrite, cursorEq⟩ :=
    allocatePromotedTag_decompose state result payload address allocated
  have objectExtension := valid.allocateObject_prefixExtension objectAllocation
  have freshAddress := valid.allocateObject_address objectAllocation
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadInBounds :
      address.value + headerBytes + 7 < middle.memory.size := by
    have cursorInBounds := middleValid.cursorInBounds
    rw [middleExtent] at cursorInBounds
    simp [headerBytes, align8] at cursorInBounds ⊢
    omega
  have finalSize := LinearMemory.size_of_writeUInt64_eq_ok middle.memory result.memory
    (address.value + headerBytes) payload payloadInBounds payloadWrite
  refine {
    cursor := by simpa [cursorEq] using objectExtension.cursor
    memorySize := Nat.le_trans objectExtension.memorySize (by omega)
    readByte := ?_ }
  intro byte beforeCursor
  calc
    result.memory.readByte byte = middle.memory.readByte byte :=
      LinearMemory.readByte_of_writeUInt64_eq_ok_other middle.memory result.memory
        (address.value + headerBytes) payload payloadInBounds payloadWrite byte
        (.inl (by rw [freshAddress]; omega))
    _ = state.memory.readByte byte := objectExtension.readByte byte beforeCursor

/-- Promoted tagged values allocate only above the old frontier, so the
retained extent of every mapped semantic heap object is unchanged. -/
theorem MappedHeaderCapacityTransport.allocatePromotedTag
    (state result : MemoryState) (witness : RefinementWitness)
    (payload : UInt64) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocatePromotedTag state payload = .ok (result, address)) :
    MappedHeaderCapacityTransport state result witness :=
  .ofPrefixExtension witness
    (allocatePromotedTag_prefixExtension state result payload address valid
      allocated)

/-- Tagged encoding preserves mapped allocation capacity in both physical
representations: immediates leave the heap unchanged, while promoted tags are
fresh prefix extensions. -/
theorem MappedHeaderCapacityTransport.encodeTagged
    (state result : MemoryState) (witness : RefinementWitness)
    (payload : UInt64) (word : Word32)
    (valid : state.FrontierInvariant)
    (encoded : encodeTagged state payload = .ok (result, word)) :
    MappedHeaderCapacityTransport state result witness := by
  by_cases fits : payload.toNat ≤ maxImmediatePayload
  · rw [encodeTagged_immediate state payload fits] at encoded
    have pairEq :
        (state, Word32.encodeImmediate payload.toNat fits) = (result, word) :=
      Except.ok.inj encoded
    have stateEq : state = result := congrArg Prod.fst pairEq
    subst result
    exact .refl state witness
  · have promoted :
      Fir.Wasm.Concrete.allocatePromotedTag state payload =
          .ok (result, word) := by
      simpa [Fir.Wasm.Concrete.encodeTagged, fits] using encoded
    exact MappedHeaderCapacityTransport.allocatePromotedTag state result
      witness payload word valid promoted

/-- A fresh persistent natural establishes the exact promoted-tag relation
and preserves the zero-frontier allocator invariant. -/
theorem allocatePromotedTag_objectRel
    (state result : MemoryState) (witness : RefinementWitness)
    (payload : UInt64) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocatePromotedTag state payload = .ok (result, address)) :
    result.FrontierInvariant ∧
      PromotedTagRel result (witness.promoteTag payload address) payload address := by
  obtain ⟨middle, objectAllocation, payloadWrite, cursorEq⟩ :=
    allocatePromotedTag_decompose state result payload address allocated
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadInBounds :
      address.value + headerBytes + 7 < middle.memory.size := by
    have cursorInBounds := middleValid.cursorInBounds
    rw [middleExtent] at cursorInBounds
    simp [headerBytes, align8] at cursorInBounds ⊢
    omega
  have finalSize := LinearMemory.size_of_writeUInt64_eq_ok middle.memory result.memory
    (address.value + headerBytes) payload payloadInBounds payloadWrite
  have payloadRead := LinearMemory.readUInt64_of_writeUInt64_eq_ok middle.memory
    result.memory (address.value + headerBytes) payload payloadInBounds payloadWrite
  have stateEq : ({ middle with memory := result.memory } : MemoryState) = result := by
    cases middle
    cases result
    simp_all
  have finalValid : result.FrontierInvariant := by
    rw [← stateEq]
    refine {
      cursorAligned := middleValid.cursorAligned
      cursorInBounds := by simpa [finalSize] using middleValid.cursorInBounds
      unusedZero := ?_ }
    intro byte afterCursor finalInBounds
    have oldInBounds : byte < middle.memory.size := by
      change byte < result.memory.size at finalInBounds
      simpa [finalSize] using finalInBounds
    have oldZero := middleValid.unusedZero byte afterCursor oldInBounds
    have framed := LinearMemory.readByte_of_writeUInt64_eq_ok_other middle.memory
      result.memory (address.value + headerBytes) payload payloadInBounds
        payloadWrite byte (.inr (by
          change middle.heapCursor ≤ byte at afterCursor
          rw [middleExtent] at afterCursor
          simp [headerBytes, align8] at afterCursor ⊢
          omega))
    cases resultByte : result.memory[byte]? with
    | none => simp [LinearMemory.readByte, resultByte, oldZero] at framed
    | some value =>
        simp [LinearMemory.readByte, resultByte, oldZero] at framed
        subst value
        rfl
  let header := Header.forAllocation .natural (align8 (headerBytes + 8))
    true promotedTagMarker 1
  have headerBefore : middle.readLiveHeader address = .ok header := by
    simpa [header] using
      MemoryState.readLiveHeader_of_allocateObject_eq_ok state middle .natural 8
        true promotedTagMarker 1 0 0 address objectAllocation
  have headerFrame := middle.readLiveHeader_of_writePromotedTagPayload
    result.memory address payload payloadInBounds payloadWrite
  have headerRead : result.readLiveHeader address = .ok header := by
    rw [← stateEq, headerFrame]
    exact headerBefore
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts result address header headerRead).1
  have decoded : readTag result address = .ok payload := by
    unfold readTag
    rw [addressHeap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    simp [header, Header.forAllocation, payloadRead] <;> rfl
  have resultExtent :
      address.value + header.allocationBytes.toNat ≤ result.heapCursor := by
    rw [cursorEq, middleExtent]
    simp [header, Header.forAllocation, headerBytes, align8]
  exact ⟨finalValid, {
    mapped := RefinementWitness.contains_promoteTag_self witness payload address
    descriptor := RefinementWitness.lookup_promoteTag_descriptor witness payload address
    header := ⟨header, headerRead, rfl, rfl, rfl, rfl, resultExtent, by
      simp [header, Header.forAllocation, headerBytes, align8]⟩
    decoded }⟩

/-- Promoting a tagged value extends only concrete memory and ghost metadata;
the semantic heap is unchanged. -/
theorem allocatePromotedTag_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : Fir.LeanIR.Impure.RuntimeState)
    (payload : UInt64) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (allocated : allocatePromotedTag state payload = .ok (result, address)) :
    let nextWitness := witness.promoteTag payload address
    LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tobject (.word32 address)
        (.object (.tagged payload)) := by
  dsimp only
  obtain ⟨_, objectAllocation, _, _⟩ :=
    allocatePromotedTag_decompose state result payload address allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have extension := allocatePromotedTag_prefixExtension state result payload address
    related.frontier allocated
  obtain ⟨finalFrontier, newPromoted⟩ :=
    allocatePromotedTag_objectRel state result witness payload address
      related.frontier allocated
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    omega
  have witnessExtension := witness.promoteTag_extends payload address descriptorFresh
  have locationAddressFresh : ∀ location oldAddress,
      witness.locations.lookup? location = some oldAddress → oldAddress ≠ address := by
    intro location oldAddress found equal
    obtain ⟨cell, _, cellRelated⟩ :=
      related.concreteToSemantic location oldAddress found
    have owned := cellRelated.headerOwned
    subst oldAddress
    simp [headerBytes] at owned
    omega
  have promotedAddressFresh : ∀ oldPayload oldAddress,
      witness.promotedTags.Contains oldPayload oldAddress → oldAddress ≠ address := by
    intro oldPayload oldAddress found equal
    have oldPromoted := related.promoted oldPayload oldAddress found
    obtain ⟨header, _, _, _, _, _, extent, payloadFits⟩ := oldPromoted.header
    subst oldAddress
    simp [headerBytes] at payloadFits extent
    omega
  obtain ⟨newHeader, newHeaderRead, _, _, _, _, newExtent, _⟩ :=
    newPromoted.header
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts result address newHeader
      newHeaderRead).1
  have witnessWellFormed := related.witnessWellFormed.promoteTag payload address
    addressHeap locationAddressFresh promotedAddressFresh
  obtain ⟨_, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address newHeader
      newHeaderRead
  have newRegion : ∃ header,
      Header.read result.memory address = .ok header ∧
      headerBytes ≤ header.allocationBytes.toNat ∧
      header.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + header.allocationBytes.toNat ≤ result.heapCursor :=
    ⟨newHeader, rawHeaderRead, headerMinimum, headerAligned, newExtent⟩
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial extension address freshAddress
      (fun other different =>
        witness.lookup_promoteTag_descriptor_other payload address other different)
      newRegion
  refine ⟨?_, ValueRel.new_promoted_tobject witness payload address⟩
  refine {
    frontier := finalFrontier
    witnessWellFormed
    locationsBeforeNext := related.locationsBeforeNext
    releaseFuelBound := Nat.le_trans related.releaseFuelBound extension.cursor
    descriptorsOwned := ?_
    descriptorRegion
    descriptorDisjoint
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      obtain ⟨header, _, _, _, _, _, extent, payloadFits⟩ := newPromoted.header
      simp [headerBytes] at payloadFits extent ⊢
      omega
    · rw [witness.lookup_promoteTag_descriptor_other payload address other isNew]
        at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found
    obtain ⟨oldAddress, mapped, cellRelated⟩ :=
      related.semanticToConcrete location cell found
    exact ⟨oldAddress, mapped,
      (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro location oldAddress mapped
    obtain ⟨cell, found, cellRelated⟩ :=
      related.concreteToSemantic location oldAddress mapped
    exact ⟨cell, found,
      (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro oldPayload oldAddress mapped
    change (oldPayload, oldAddress) ∈
      (payload, address) :: witness.promotedTags at mapped
    rcases List.mem_cons.mp mapped with isNew | oldMapped
    · have payloadEq : oldPayload = payload := congrArg Prod.fst isNew
      have addressEq : oldAddress = address := congrArg Prod.snd isNew
      subst oldPayload
      subst oldAddress
      exact newPromoted
    · exact ((related.promoted oldPayload oldAddress oldMapped).prefixExtension extension)
        |>.witnessExtension witnessExtension

/-- `encodeTagged` either preserves the existing relation with an immediate
word or extends it with one fresh promoted representation. -/
theorem encodeTagged_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : Fir.LeanIR.Impure.RuntimeState)
    (payload : UInt64) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (encoded : encodeTagged state payload = .ok (result, word)) :
    ∃ nextWitness,
      LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tobject (.word32 word)
        (.object (.tagged payload)) := by
  by_cases fits : payload.toNat ≤ maxImmediatePayload
  · rw [encodeTagged_immediate state payload fits] at encoded
    have pairEq : (state, Word32.encodeImmediate payload.toNat fits) =
        (result, word) := Except.ok.inj encoded
    have stateEq := congrArg Prod.fst pairEq
    have wordEq := congrArg Prod.snd pairEq
    change state = result at stateEq
    change Word32.encodeImmediate payload.toNat fits = word at wordEq
    subst result
    subst word
    exact ⟨witness, related,
      encodeTagged_immediate_refines witness payload fits⟩
  · have promoted : allocatePromotedTag state payload = .ok (result, word) := by
      simpa [encodeTagged, fits] using encoded
    exact ⟨witness.promoteTag payload word,
      allocatePromotedTag_liveHeapRel state result witness runtime payload word
        related promoted⟩

/-- Allocation-producing clients also need the monotonicity fact for proof
metadata so pre-existing globals, trace entries, and locals remain related. -/
theorem encodeTagged_liveHeapRel_extends
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : Fir.LeanIR.Impure.RuntimeState)
    (payload : UInt64) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (encoded : encodeTagged state payload = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tobject (.word32 word)
        (.object (.tagged payload)) := by
  by_cases fits : payload.toNat ≤ maxImmediatePayload
  · rw [encodeTagged_immediate state payload fits] at encoded
    have pairEq : (state, Word32.encodeImmediate payload.toNat fits) =
        (result, word) := Except.ok.inj encoded
    have stateEq := congrArg Prod.fst pairEq
    have wordEq := congrArg Prod.snd pairEq
    change state = result at stateEq
    change Word32.encodeImmediate payload.toNat fits = word at wordEq
    subst result
    subst word
    exact ⟨witness, RefinementWitness.Extends.refl witness,
      ClosureAllocationsPersistent.refl witness, related,
      encodeTagged_immediate_refines witness payload fits⟩
  · have promoted : allocatePromotedTag state payload = .ok (result, word) := by
      simpa [encodeTagged, fits] using encoded
    obtain ⟨_, objectAllocation, _, _⟩ :=
      allocatePromotedTag_decompose state result payload word promoted
    have freshAddress := related.frontier.allocateObject_address objectAllocation
    have descriptorFresh : ∀ old descriptor,
        witness.descriptors.lookup? old = some descriptor →
        word.value ≠ old.value := by
      intro old descriptor found equal
      have owned := related.descriptorsOwned old descriptor found
      simp [headerBytes] at owned
      omega
    have extension := witness.promoteTag_extends payload word descriptorFresh
    have refined := allocatePromotedTag_liveHeapRel state result witness runtime
      payload word related promoted
    exact ⟨witness.promoteTag payload word, extension,
      ClosureAllocationsPersistent.promoteTag witness payload word,
      refined.1, refined.2⟩

/-- Monotone-witness tagged encoding additionally exposes the retained-header
transport needed by the reuse-capacity state invariant. -/
theorem encodeTagged_liveHeapRel_extends_with_capacity
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : Fir.LeanIR.Impure.RuntimeState)
    (payload : UInt64) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (encoded : encodeTagged state payload = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tobject (.word32 word)
        (.object (.tagged payload)) ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨nextWitness, extension, closureAllocationsPersistent, heapRelated,
      valueRelated⟩ :=
    encodeTagged_liveHeapRel_extends state result witness runtime payload word
      related encoded
  exact ⟨nextWitness, extension, closureAllocationsPersistent, heapRelated,
    valueRelated,
    .encodeTagged state result witness payload word related.frontier encoded⟩

end Fir.Wasm.Concrete
