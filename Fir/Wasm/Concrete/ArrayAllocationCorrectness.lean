import Fir.Wasm.Concrete.HeapRefinement
import Fir.Wasm.Concrete.ObjectFieldsCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- A successful resident-Array allocation decomposes into the common object
allocator and the verified live-prefix slot writer. -/
theorem allocateResidentArray_decompose
    (state result : MemoryState) (elements : Array Word32) (capacity : Nat)
    (address : Word32) (sizeCapacity : elements.size ≤ capacity)
    (sizeFits : elements.size < UInt32.size) (capacityFits : capacity < UInt32.size)
    (allocated :
      allocateResidentArray state elements capacity = .ok (result, address)) :
    ∃ middle,
      state.allocateObject .opaque (target.semanticSlotBytes * capacity) false
        residentArrayMarker (UInt32.ofNat elements.size)
          (UInt32.ofNat capacity) 0 = .ok (middle, address) ∧
      writeObjectFields middle.memory address.value 0 elements.toList =
        .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  unfold allocateResidentArray at allocated
  rw [if_pos sizeCapacity] at allocated
  simp [uint32Field, sizeFits, capacityFits] at allocated
  change (do
    let (middle, actualAddress) ← liftMemory <|
      state.allocateObject .opaque (target.semanticSlotBytes * capacity) false
        residentArrayMarker (UInt32.ofNat elements.size)
          (UInt32.ofNat capacity) 0
    let memory ← liftMemory <|
      writeObjectFields middle.memory actualAddress.value 0 elements.toList
    return ({ middle with memory }, actualAddress)) =
      .ok (result, address) at allocated
  cases objectAllocation : state.allocateObject .opaque
      (target.semanticSlotBytes * capacity) false residentArrayMarker
      (UInt32.ofNat elements.size) (UInt32.ofNat capacity) 0 with
  | error failure =>
      rw [objectAllocation] at allocated
      contradiction
  | ok pair =>
      rcases pair with ⟨middle, actualAddress⟩
      rw [objectAllocation] at allocated
      simp only [liftMemory, Bind.bind, Except.bind] at allocated
      cases fieldsWrite :
          writeObjectFields middle.memory actualAddress.value 0 elements.toList with
      | error failure =>
          rw [fieldsWrite] at allocated
          contradiction
      | ok memory =>
          rw [fieldsWrite] at allocated
          have pairEq := Except.ok.inj allocated
          have resultEq : { middle with memory } = result := congrArg Prod.fst pairEq
          have addressEq : actualAddress = address := congrArg Prod.snd pairEq
          subst result
          subst address
          exact ⟨middle, rfl, fieldsWrite, rfl⟩

/-- The resident allocator establishes the exact Array relation. Only live
slots require pointwise `tobject` refinement; spare capacity is retained and
allocator-zeroed but receives no semantic child relation. -/
theorem allocateResidentArray_objectRel
    (state result : MemoryState) (witness : RefinementWitness)
    (words : Array Word32) (elements : Array Value) (capacity : Nat)
    (address : Word32) (valid : state.FrontierInvariant)
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
    ∃ header,
      result.FrontierInvariant ∧
      ResidentArrayObjectRel result witness address elements capacity header ∧
      header.refCount.toNat = 1 ∧ header.persistent = false ∧
      ∀ index, words.size ≤ index → index < capacity →
        result.memory.readWord32
            (address.value + headerBytes + target.semanticSlotBytes * index) =
          .ok Word32.zero := by
  have wordsCapacity : words.size ≤ capacity := by omega
  have wordsFits : words.size < UInt32.size := by omega
  obtain ⟨middle, objectAllocation, fieldsWrite, cursorEq⟩ :=
    allocateResidentArray_decompose state result words capacity address
      wordsCapacity wordsFits capacityFits allocated
  have allocationEq :
      align8 (headerBytes + target.semanticSlotBytes * capacity) =
        residentArrayAllocationBytes capacity := by
    rfl
  have fieldsEnd :
      objectFieldAddress address.value words.toList.length ≤
        address.value +
          align8 (headerBytes + target.semanticSlotBytes * capacity) := by
    simp [objectFieldAddress, residentArrayAllocationBytes, target, wordsCapacity]
    have minimum := align8_ge (headerBytes + 8 * capacity)
    omega
  obtain ⟨finalValid, headerRead, fieldsPost, remainingZero⟩ :=
    valid.allocateObject_writeObjectFields objectAllocation fieldsEnd fieldsWrite
  let header := Header.forAllocation .opaque
    (residentArrayAllocationBytes capacity) false residentArrayMarker
      (UInt32.ofNat words.size) (UInt32.ofNat capacity) 0
  have stateEq : ({ middle with memory := result.memory } : MemoryState) = result := by
    cases middle
    cases result
    simp_all
  have exactHeader : result.readLiveHeader address = .ok header := by
    rw [← stateEq]
    simpa [header, allocationEq] using headerRead
  have objectExtent := MemoryState.allocateObject_extent objectAllocation
  have extent : address.value + residentArrayAllocationBytes capacity ≤
      result.heapCursor := by
    rw [cursorEq, objectExtent, allocationEq]
    exact Nat.le_refl _
  have sizeToNat : (UInt32.ofNat words.size).toNat = words.size :=
    UInt32.toNat_ofNat_of_lt' wordsFits
  have capacityToNat : (UInt32.ofNat capacity).toNat = capacity :=
    UInt32.toNat_ofNat_of_lt' capacityFits
  refine ⟨header, by simpa [stateEq] using finalValid, ?_, ?_, ?_, ?_⟩
  · refine {
      headerRead := exactHeader
      headerKind := rfl
      marker := rfl
      logicalSize := by
        change (UInt32.ofNat words.size).toNat = elements.size
        rw [sizeToNat, count]
      physicalCapacity := by
        change (UInt32.ofNat capacity).toNat = capacity
        exact capacityToNat
      reserved := rfl
      sizeCapacity
      allocationBytes := by
        have allocationLt : residentArrayAllocationBytes capacity < UInt32.size := by
          obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
            MemoryState.allocateObject_header state middle .opaque
              (target.semanticSlotBytes * capacity) false residentArrayMarker
              (UInt32.ofNat words.size) (UInt32.ofNat capacity) 0 address
                objectAllocation
          have post := MemoryState.allocate_spec state rawState
            (align8 (headerBytes + target.semanticSlotBytes * capacity)) address
              rawAllocation
          have endWithin := post.endWithinAddressSpace
          have addressPositive : address.value ≠ 0 := by
            intro zero
            have addressClass := post.addressClass
            simp [Word32.classify, zero] at addressClass
          have allocatedLt :
              align8 (align8
                (headerBytes + target.semanticSlotBytes * capacity)) <
                wordModulus := by omega
          simpa only [residentArrayAllocationBytes, align8_align8,
            wordModulus] using allocatedLt
        change (UInt32.ofNat (residentArrayAllocationBytes capacity)).toNat =
          residentArrayAllocationBytes capacity
        exact UInt32.toNat_ofNat_of_lt' allocationLt
      headerOwned := by
        have minimum : headerBytes ≤ residentArrayAllocationBytes capacity :=
          Nat.le_trans (Nat.le_add_right _ _)
            (align8_ge (headerBytes + target.semanticSlotBytes * capacity))
        exact Nat.le_trans (Nat.add_le_add_left minimum address.value) extent
      extent
      liveElements := ?_ }
    intro index value valueAt
    obtain ⟨word, wordAt, valueRelated⟩ := each index value valueAt
    have listAt : words.toList[index]? = some word := by simpa using wordAt
    have read := fieldsPost.fieldAt index word listAt
    exact ⟨word, by simpa [objectFieldAddress] using read, valueRelated⟩
  · rfl
  · rfl
  · intro index afterLive beforeCapacity
    have zeroByte (offset : Nat) (offsetLt : offset < 4) :
        result.memory[
            address.value + headerBytes + target.semanticSlotBytes * index +
              offset]? = some 0 := by
      apply remainingZero
      · simp [objectFieldAddress, target]
        omega
      · have aligned := align8_ge
          (headerBytes + target.semanticSlotBytes * capacity)
        simp [target] at aligned ⊢
        omega
    have h0 : result.memory[
        address.value + headerBytes + target.semanticSlotBytes * index]? = some 0 := by
      simpa using zeroByte 0 (by decide)
    have h1 : result.memory[
        address.value + headerBytes + target.semanticSlotBytes * index + 1]? =
          some 0 := zeroByte 1 (by decide)
    have h2 : result.memory[
        address.value + headerBytes + target.semanticSlotBytes * index + 2]? =
          some 0 := zeroByte 2 (by decide)
    have h3 : result.memory[
        address.value + headerBytes + target.semanticSlotBytes * index + 3]? =
          some 0 := zeroByte 3 (by decide)
    unfold LinearMemory.readWord32 LinearMemory.readUInt32 LinearMemory.readByte
    rw [h0, h1, h2, h3]
    rfl

end Fir.Wasm.Concrete
