import Fir.Wasm.Concrete.NaturalAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

@[simp] theorem integerMagnitude_ofNat (value : Nat) :
    integerMagnitude (.ofNat value) = value := rfl

@[simp] theorem integerMagnitude_negSucc (value : Nat) :
    integerMagnitude (.negSucc value) = value + 1 := rfl

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

/-- Local decoded relation for the current experimental heap-Int layout. It is
the intended client boundary; individual header lanes remain replaceable. -/
structure IntegerObjectRel (state : MemoryState) (address : Word32)
    (value : Int) (header : Header) : Prop where
  headerRead : state.readLiveHeader address = .ok header
  headerKind : header.kind = .integer
  ordinary : header.persistent = false
  marker : header.aux0 = integerSignMagnitudeMarker
  limbCount : header.aux1.toNat =
    (naturalLimbs (integerMagnitude value)).length
  sign : header.aux2 = integerSign value
  reserved : header.aux3 = 0
  allocationBytes : header.allocationBytes.toNat =
    align8 (headerBytes + target.semanticSlotBytes *
      (naturalLimbs (integerMagnitude value)).length)
  extent : address.value + header.allocationBytes.toNat ≤ state.heapCursor
  decoded : readInteger state address = .ok value
  refCountOne : header.refCount.toNat = 1

/-- Allocation establishes the checked read boundary, a valid frontier, and
old-prefix framing. No compatibility promise is attached to the header lanes. -/
theorem allocateInteger_objectRel
    (state result : MemoryState) (value : Int) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocateInteger state value = .ok (result, address)) :
    result.FrontierInvariant ∧ state.PrefixExtension result ∧
      ∃ header, IntegerObjectRel result address value header := by
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
      ordinary := rfl
      marker := rfl
      limbCount := countToNat
      sign := rfl
      reserved := rfl
      allocationBytes := by
        simp [header, Header.forAllocation, allocationToNat, allocationBytes]
      extent := by
        simpa [header, Header.forAllocation, allocationToNat] using resultExtent
      decoded
      refCountOne := rfl }⟩

end Fir.Wasm.Concrete
