import Fir.Wasm.Concrete.NaturalAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

@[simp] theorem integerMagnitude_ofNat (value : Nat) :
    integerMagnitude (.ofNat value) = value := rfl

@[simp] theorem integerMagnitude_negSucc (value : Nat) :
    integerMagnitude (.negSucc value) = value + 1 := rfl

/--
Exact wasm32 frontier cost of constructing one concrete heap integer.

Unlike naturals, the current arbitrary-precision `Int` representation always
uses an ordinary sign-magnitude heap object, including for zero and small
values. The cost is therefore exactly the aligned header-plus-limb extent.
-/
def integerAllocationBytes (value : Int) : Nat :=
  align8
    (headerBytes + target.semanticSlotBytes *
      (naturalLimbs (integerMagnitude value)).length)

theorem integerOfSignMagnitude_roundtrip (value : Int) :
    integerOfSignMagnitude (integerSign value == 1)
      (integerMagnitude value) = value := by
  cases value <;> simp [integerSign, integerMagnitude,
    integerOfSignMagnitude] <;> omega

theorem integerMagnitude_ne_zero_of_negative {value : Int}
    (negative : integerSign value = 1) : integerMagnitude value ≠ 0 := by
  cases value with
  | ofNat value => simp [integerSign] at negative
  | negSucc value => simp [integerMagnitude]

/--
One exact source-path budget makes heap-integer construction constructive and
transports the residual address-space budget across the allocation and
little-endian magnitude write.
-/
theorem MemoryState.FrontierInvariant.allocateInteger_eq_ok_of_budget
    {state : MemoryState} (valid : state.FrontierInvariant) (value : Int)
    {remainingBytes : Nat}
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : integerAllocationBytes value ≤ remainingBytes) :
    ∃ result address,
      allocateInteger state value = .ok (result, address) ∧
        result.AddressSpaceBudget
          (remainingBytes - integerAllocationBytes value) := by
  let limbs := naturalLimbs (integerMagnitude value)
  have allocationFits :
      align8 (headerBytes + target.semanticSlotBytes * limbs.length) ≤
        remainingBytes := by
    simpa [integerAllocationBytes, limbs] using fits
  have limbCountFits : limbs.length < UInt32.size := by
    have endWithin :
        state.heapCursor +
            align8
              (align8
                (headerBytes + target.semanticSlotBytes * limbs.length)) ≤
          wordModulus := by
      simpa [limbs] using
        (budget.allocationCapacity (by
          simpa only [align8_align8] using allocationFits)).endWithinAddressSpace
    simp only [align8_align8] at endWithin
    have extent :=
      align8_ge (headerBytes + target.semanticSlotBytes * limbs.length)
    have cursorPositive := budget.cursorPositive
    have belowWordModulus : limbs.length < wordModulus := by
      simp [target] at endWithin extent
      omega
    simpa [wordModulus] using belowWordModulus
  have limbCount :
      uint32Field "integer limb count" limbs.length =
        .ok (UInt32.ofNat limbs.length) := by
    simp [uint32Field, limbCountFits]
  obtain ⟨middle, address, objectAllocation⟩ :=
    state.allocateObject_eq_ok_of_capacity .integer
      (target.semanticSlotBytes * limbs.length) false
      integerSignMagnitudeMarker (UInt32.ofNat limbs.length)
      (integerSign value) 0 valid.cursorAligned
      (budget.allocationCapacity (by
        simpa only [align8_align8] using allocationFits))
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadInBounds :
      address.value + headerBytes +
          target.semanticSlotBytes * (0 + limbs.length) ≤
        middle.memory.size := by
    have payloadEnd :
        address.value + headerBytes +
            target.semanticSlotBytes * (0 + limbs.length) ≤
          middle.heapCursor := by
      simp only [Nat.zero_add]
      rw [middleExtent]
      have extent :=
        align8_ge (headerBytes + target.semanticSlotBytes * limbs.length)
      simpa [Nat.add_assoc] using Nat.add_le_add_left extent address.value
    exact Nat.le_trans payloadEnd middleValid.cursorInBounds
  obtain ⟨memory, payloadWrite, _⟩ :=
    writeNaturalLimbs_spec middle.memory address.value 0 limbs payloadInBounds
  let result : MemoryState := { middle with memory }
  have allocated :
      allocateInteger state value = .ok (result, address) := by
    unfold allocateInteger
    dsimp only
    change
      (do
        let limbCount ← uint32Field "integer limb count" limbs.length
        let (state, address) ← liftMemory <|
          state.allocateObject .integer
            (target.semanticSlotBytes * limbs.length) false
            integerSignMagnitudeMarker limbCount (integerSign value) 0
        let memory ← liftMemory <|
          Fir.Wasm.Concrete.writeNaturalLimbs
            state.memory address.value 0 limbs
        return ({ state with memory }, address)) =
        .ok (result, address)
    rw [limbCount]
    simp only [Bind.bind, Except.bind]
    rw [objectAllocation]
    simp only [liftMemory]
    rw [payloadWrite]
    rfl
  have middleBudget :=
    budget.allocateObject valid.cursorAligned allocationFits objectAllocation
  have resultBudget :
      result.AddressSpaceBudget
        (remainingBytes -
          align8 (headerBytes + target.semanticSlotBytes * limbs.length)) := {
    cursorPositive := middleBudget.cursorPositive
    endWithinAddressSpace := middleBudget.endWithinAddressSpace }
  exact ⟨result, address, allocated, by
    simpa [integerAllocationBytes, limbs] using resultBudget⟩

/-- A successful heap-Int allocation is one checked ordinary object allocation
followed by the shared little-endian magnitude writer. -/
theorem allocateInteger_decompose
    (state result : MemoryState) (value : Int) (address : Word32)
    (allocated : allocateInteger state value = .ok (result, address)) :
    let limbs := naturalLimbs (integerMagnitude value)
    ∃ limbCount middle,
      uint32Field "integer limb count" limbs.length = .ok limbCount ∧
      state.allocateObject .integer
        (target.semanticSlotBytes * limbs.length) false
        integerSignMagnitudeMarker limbCount (integerSign value) 0 =
          .ok (middle, address) ∧
      writeNaturalLimbs middle.memory address.value 0 limbs =
        .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  dsimp only
  unfold allocateInteger at allocated
  dsimp only at allocated
  cases countResult : uint32Field "integer limb count"
      (naturalLimbs (integerMagnitude value)).length with
  | error failure =>
      rw [countResult] at allocated
      contradiction
  | ok limbCount =>
      rw [countResult] at allocated
      simp only [Bind.bind, Except.bind] at allocated
      cases objectAllocation : state.allocateObject .integer
          (target.semanticSlotBytes *
            (naturalLimbs (integerMagnitude value)).length)
          false integerSignMagnitudeMarker limbCount (integerSign value) 0 with
      | error failure =>
          rw [objectAllocation] at allocated
          change Except.error (ConcreteError.ofMemory failure) =
            .ok (result, address) at allocated
          contradiction
      | ok pair =>
          rcases pair with ⟨middle, actualAddress⟩
          rw [objectAllocation] at allocated
          simp only [liftMemory] at allocated
          cases limbWrite : writeNaturalLimbs middle.memory actualAddress.value 0
              (naturalLimbs (integerMagnitude value)) with
          | error failure =>
              rw [limbWrite] at allocated
              change Except.error (ConcreteError.ofMemory failure) =
                .ok (result, address) at allocated
              contradiction
          | ok finalMemory =>
              rw [limbWrite] at allocated
              change Except.ok ({ middle with memory := finalMemory }, actualAddress) =
                Except.ok (result, address) at allocated
              have pairEq : ({ middle with memory := finalMemory }, actualAddress) =
                  (result, address) := Except.ok.inj allocated
              have resultEq : { middle with memory := finalMemory } = result :=
                congrArg Prod.fst pairEq
              have addressEq : actualAddress = address := congrArg Prod.snd pairEq
              subst result
              subst address
              exact ⟨limbCount, middle, rfl, objectAllocation, limbWrite, rfl⟩

/-- Heap-Int allocation appends fresh bytes and preserves the complete old
concrete heap prefix. -/
theorem allocateInteger_prefixExtension
    (state result : MemoryState) (value : Int) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocateInteger state value = .ok (result, address)) :
    state.PrefixExtension result := by
  obtain ⟨limbCount, middle, _, objectAllocation, limbWrite, cursorEq⟩ :=
    allocateInteger_decompose state result value address allocated
  have objectExtension := valid.allocateObject_prefixExtension objectAllocation
  have freshAddress := valid.allocateObject_address objectAllocation
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadEnd : address.value + headerBytes +
      target.semanticSlotBytes *
        (0 + (naturalLimbs (integerMagnitude value)).length) ≤
        middle.heapCursor := by
    simp only [Nat.zero_add]
    rw [middleExtent]
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes *
        (naturalLimbs (integerMagnitude value)).length)
    simpa [Nat.add_assoc] using Nat.add_le_add_left aligned address.value
  have payloadPost := writeNaturalLimbs_post middle.memory result.memory
    address.value 0 (naturalLimbs (integerMagnitude value))
    (Nat.le_trans payloadEnd middleValid.cursorInBounds) limbWrite
  refine {
    cursor := by simpa [cursorEq] using objectExtension.cursor
    memorySize := Nat.le_trans objectExtension.memorySize (by
      rw [payloadPost.size]
      exact Nat.le_refl _)
    readByte := ?_ }
  intro byte beforeCursor
  calc
    result.memory.readByte byte = middle.memory.readByte byte :=
      payloadPost.byteFrame byte (.inl (by
        rw [freshAddress]
        simp [target]
        omega))
    _ = state.memory.readByte byte := objectExtension.readByte byte beforeCursor

/-- Allocation establishes the checked read boundary, a valid frontier, and
old-prefix framing. No compatibility promise is attached to the header lanes. -/
theorem allocateInteger_objectRel
    (state result : MemoryState) (value : Int) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocateInteger state value = .ok (result, address)) :
    result.FrontierInvariant ∧ state.PrefixExtension result ∧
      ∃ header, IntegerObjectRel result address value header ∧
        header.refCount.toNat = 1 ∧ header.persistent = false := by
  obtain ⟨limbCount, middle, countEncoded, objectAllocation, limbWrite,
      cursorEq⟩ := allocateInteger_decompose state result value address allocated
  obtain ⟨countFits, countEq⟩ := uint32Field_success
    "integer limb count" (naturalLimbs (integerMagnitude value)).length
      limbCount countEncoded
  have countToNat : limbCount.toNat =
      (naturalLimbs (integerMagnitude value)).length := by
    rw [countEq]
    exact UInt32.toNat_ofNat_of_lt' countFits
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadEnd : address.value + headerBytes +
      target.semanticSlotBytes *
        (0 + (naturalLimbs (integerMagnitude value)).length) ≤
        middle.heapCursor := by
    simp only [Nat.zero_add]
    rw [middleExtent]
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes *
        (naturalLimbs (integerMagnitude value)).length)
    simpa [Nat.add_assoc] using Nat.add_le_add_left aligned address.value
  have payloadInBounds : address.value + headerBytes +
      target.semanticSlotBytes *
        (0 + (naturalLimbs (integerMagnitude value)).length) ≤
        middle.memory.size := Nat.le_trans payloadEnd middleValid.cursorInBounds
  have payloadPost := writeNaturalLimbs_post middle.memory result.memory
    address.value 0 (naturalLimbs (integerMagnitude value)) payloadInBounds limbWrite
  have stateEq : ({ middle with memory := result.memory } : MemoryState) = result := by
    cases middle
    cases result
    simp_all
  have finalValid : result.FrontierInvariant := by
    rw [← stateEq]
    exact middleValid.writeNaturalLimbs payloadEnd limbWrite
  let allocationBytes := align8
    (headerBytes + target.semanticSlotBytes *
      (naturalLimbs (integerMagnitude value)).length)
  let header := Header.forAllocation .integer allocationBytes false
    integerSignMagnitudeMarker limbCount (integerSign value) 0
  have headerBefore : middle.readLiveHeader address = .ok header := by
    simpa [header, allocationBytes] using
      MemoryState.readLiveHeader_of_allocateObject_eq_ok state middle .integer
        (target.semanticSlotBytes *
          (naturalLimbs (integerMagnitude value)).length)
        false integerSignMagnitudeMarker limbCount (integerSign value) 0
        address objectAllocation
  have headerFrame := middle.readLiveHeader_of_writeNaturalLimbs result.memory
    address (naturalLimbs (integerMagnitude value)) payloadPost
  have headerRead : result.readLiveHeader address = .ok header := by
    rw [← stateEq, headerFrame]
    exact headerBefore
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state middle .integer
      (target.semanticSlotBytes *
        (naturalLimbs (integerMagnitude value)).length)
      false integerSignMagnitudeMarker limbCount (integerSign value) 0
      address objectAllocation
  have allocationPost := MemoryState.allocate_spec state rawState allocationBytes
    address (by simpa [allocationBytes] using rawAllocation)
  have addressNonzero : address.value ≠ 0 := by
    intro zero
    have heap := allocationPost.addressClass
    simp [Word32.classify, zero] at heap
  have allocationLt : allocationBytes < UInt32.size := by
    have within := allocationPost.endWithinAddressSpace
    have aligned : align8 allocationBytes = allocationBytes := by
      simp [allocationBytes]
    rw [aligned] at within
    have belowWordModulus : allocationBytes < wordModulus := by omega
    simpa [wordModulus] using belowWordModulus
  have allocationToNat : (UInt32.ofNat allocationBytes).toNat = allocationBytes :=
    UInt32.toNat_ofNat_of_lt' allocationLt
  have resultExtent : address.value + allocationBytes ≤ result.heapCursor := by
    rw [cursorEq, middleExtent]
    exact Nat.le_refl _
  have addressHeap : address.classify = .heap := by
    have checked := headerRead
    unfold MemoryState.readLiveHeader at checked
    split at checked
    next heap => exact heap
    next => contradiction
  have decodedLimbs := readNaturalLimbs_of_write_eq_ok middle.memory result.memory
    address.value 0 (naturalLimbs (integerMagnitude value)) payloadInBounds limbWrite
  have limbCountPositive : 0 <
      (naturalLimbs (integerMagnitude value)).length := by
    unfold naturalLimbs
    split <;> simp
  have decoded : readInteger result address = .ok value := by
    unfold readInteger
    simp only [addressHeap, ↓reduceIte, Bind.bind, Except.bind]
    rw [headerRead]
    simp only [liftMemory]
    have accepted : header.kind == ObjectKind.integer &&
        header.aux0 == integerSignMagnitudeMarker := by
      simp [header, Header.forAllocation]
      change (ObjectKind.integer == ObjectKind.integer) = true
      decide
    rw [accepted]
    simp only [↓reduceIte]
    have signValid : integerSign value = 0 ∨ integerSign value = 1 := by
      cases value <;> simp [integerSign]
    have metadata :
        ((header.aux2 == 0 || header.aux2 == 1) && header.aux3 == 0 &&
          decide (0 < header.aux1.toNat) &&
          decide (header.allocationBytes.toNat = align8
            (headerBytes + target.semanticSlotBytes * header.aux1.toNat))) = true := by
      simp [header, Header.forAllocation, countToNat, allocationToNat,
        allocationBytes, limbCountPositive, signValid]
    rw [metadata]
    simp only [↓reduceIte]
    change (do
      let magnitude ← liftMemory <|
        readNaturalLimbs result.memory address.value 0 header.aux1.toNat
      if header.aux2 == 1 then
        if magnitude == 0 then
          throw (ConcreteError.target (.malformedIntegerHeader address.value))
        else return integerOfSignMagnitude true magnitude
      else return integerOfSignMagnitude false magnitude) = .ok value
    rw [show header.aux1.toNat =
        (naturalLimbs (integerMagnitude value)).length by
      simp [header, Header.forAllocation, countToNat]]
    rw [decodedLimbs]
    simp only [naturalLimbs_value]
    cases value with
    | ofNat magnitude =>
        change (.ok (integerOfSignMagnitude false magnitude) :
          Except ConcreteError Int) = .ok (.ofNat magnitude)
        rfl
    | negSucc magnitude =>
        change (if magnitude + 1 == 0 then
          (Except.error (ConcreteError.target
            (.malformedIntegerHeader address.value)) : Except ConcreteError Int)
        else Except.ok (integerOfSignMagnitude true (magnitude + 1))) =
          Except.ok (.negSucc magnitude)
        simp [integerOfSignMagnitude]
        omega
  refine ⟨finalValid, allocateInteger_prefixExtension state result value address
    valid allocated, header, {
      headerRead
      headerKind := rfl
      marker := rfl
      limbCount := countToNat
      sign := rfl
      reserved := rfl
      allocationBytes := by
        simp [header, Header.forAllocation, allocationToNat, allocationBytes]
      extent := by
        simpa [header, Header.forAllocation, allocationToNat] using resultExtent
      decoded },
    by simp [header, Header.forAllocation],
    by simp [header, Header.forAllocation]⟩

/-- The semantic heap cell introduced for one arbitrary-precision integer
result. -/
def semanticIntegerCell (value : Int) : HeapCell := {
  object := .integer value }

/-- Source runtime after allocating one heap-backed integer result. -/
def semanticIntegerResult (runtime : RuntimeState) (value : Int) : RuntimeState := {
  runtime with
  heap := (runtime.nextLocation, semanticIntegerCell value) :: runtime.heap
  nextLocation := runtime.nextLocation + 1 }

/-- Fresh concrete heap-integer allocation extends the complete live-heap
relation and relates its address to the new semantic integer location. -/
theorem allocateInteger_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (value : Int) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (allocated : allocateInteger state value = .ok (result, address)) :
    let nextWitness := witness.bindInteger runtime.nextLocation address value
    witness.Extends nextWitness ∧
      LiveHeapRel result nextWitness (semanticIntegerResult runtime value) ∧
      ValueRel nextWitness .tobject (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨_, _, _, objectAllocation, _, _⟩ :=
    allocateInteger_decompose state result value address allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have extension := allocateInteger_prefixExtension state result value address
    related.frontier allocated
  obtain ⟨finalFrontier, _, header, objectRelated, refCountOne, ordinary⟩ :=
    allocateInteger_objectRel state result value address related.frontier allocated
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
  have witnessExtension := witness.bindInteger_extends runtime.nextLocation
    address value locationFresh descriptorFresh
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
  have headerOwned : address.value + headerBytes ≤ result.heapCursor :=
    Nat.le_trans (Nat.add_le_add_left headerMinimum address.value)
      objectRelated.extent
  have witnessWellFormed := related.witnessWellFormed.bindInteger
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
        witness.lookup_bindInteger_descriptor_other runtime.nextLocation address
          other value different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindInteger runtime.nextLocation address value) address
      (semanticIntegerCell value) := by
    apply LiveCellRel.integer
      (RefinementWitness.lookup_bindInteger_descriptor witness runtime.nextLocation
        address value)
      (by rfl) objectRelated
    · simpa [semanticIntegerCell] using refCountOne
    · simpa [semanticIntegerCell] using ordinary
    · rfl
  refine ⟨witnessExtension, ?_,
    ValueRel.new_integer_result witness runtime.nextLocation address value⟩
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
        simpa [semanticIntegerResult, findCell?, isNew, Ne.symm isNew] using found
      have oldBefore := related.locationsBeforeNext location cell oldFound
      exact Nat.lt_trans oldBefore (Nat.lt_succ_self runtime.nextLocation)
  · have cursorGrowth : state.heapCursor + headerBytes ≤ result.heapCursor := by
      rw [← freshAddress]
      exact headerOwned
    have oldFuel := related.releaseFuelBound
    simp [semanticIntegerResult, headerBytes] at oldFuel cursorGrowth ⊢
    omega
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact headerOwned
    · rw [witness.lookup_bindInteger_descriptor_other runtime.nextLocation
        address other value isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticIntegerCell value := by
        simpa [semanticIntegerResult, findCell?] using found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindInteger_location witness runtime.nextLocation
          address value,
        .live newCellRelated⟩
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticIntegerResult, findCell?, isNew, Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindInteger, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticIntegerCell value,
        by simp [semanticIntegerResult, findCell?], .live newCellRelated⟩
    · rw [witness.lookup_bindInteger_location_other runtime.nextLocation location
        address value isNew] at mapped
      obtain ⟨cell, oldFound, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticIntegerResult, findCell?, isNew, Ne.symm isNew],
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro payload concreteAddress mapped
    exact ((related.promoted payload concreteAddress mapped).prefixExtension extension)
      |>.witnessExtension witnessExtension

end Fir.Wasm.Concrete
