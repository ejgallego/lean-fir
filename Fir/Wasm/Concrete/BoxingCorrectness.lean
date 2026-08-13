import Fir.Wasm.Concrete.PromotedTagCorrectness
import Fir.Wasm.Concrete.NaturalAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/--
Uniform address-space reservation for integer boxing.

An immediate result allocates nothing. A promoted tagged result and an
ordinary heap box both occupy exactly one common header plus one semantic
slot, so this fixed extent is a sound declaration-local upper bound.
-/
def boxScalarAllocationBytes : Nat :=
  align8 (headerBytes + target.semanticSlotBytes)

/-- A successful heap-backed box is exactly one checked object allocation
followed by one canonical 64-bit payload write. -/
theorem allocateBoxedScalar_decompose
    (state result : MemoryState) (scalar : BoxedScalar) (address : Word32)
    (allocated : allocateBoxedScalar state scalar = .ok (result, address)) :
    ∃ middle,
      state.allocateObject .boxed target.semanticSlotBytes false scalar.kind.code
        (UInt32.ofNat scalar.kind.payloadBytes) = .ok (middle, address) ∧
      middle.memory.writeUInt64 (address.value + headerBytes) scalar.payload =
        .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  unfold allocateBoxedScalar at allocated
  dsimp only at allocated
  cases objectAllocation : state.allocateObject .boxed target.semanticSlotBytes false
      scalar.kind.code (UInt32.ofNat scalar.kind.payloadBytes) with
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
          (actualAddress.value + headerBytes) scalar.payload
        return ({ middle with memory }, actualAddress)) =
          .ok (result, address) at allocated
      cases payloadWrite : middle.memory.writeUInt64
          (actualAddress.value + headerBytes) scalar.payload with
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

/--
One uniform source reservation makes concrete boxing constructive.

The source-tagged branch reuses the natural allocator's immediate/promoted
split. The source-heap branch constructs the canonical boxed object directly.
An immediate result spends no physical bytes, but the residual proof budget
is weakened to the declaration's uniform reservation.
-/
theorem MemoryState.FrontierInvariant.boxScalar_eq_ok_of_budget
    {state : MemoryState} (valid : state.FrontierInvariant)
    (scalar : BoxedScalar) {remainingBytes : Nat}
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : boxScalarAllocationBytes ≤ remainingBytes) :
    ∃ result word,
      boxScalar state scalar = .ok (result, word) ∧
        result.AddressSpaceBudget
          (remainingBytes - boxScalarAllocationBytes) := by
  by_cases tagged : scalar.payload.toNat ≤ maxTaggedPayload
  · have naturalCost :
        naturalAllocationBytes scalar.payload.toNat ≤
          boxScalarAllocationBytes := by
      simp [naturalAllocationBytes, tagged, boxScalarAllocationBytes]
      split <;> omega
    have naturalFits :
        naturalAllocationBytes scalar.payload.toNat ≤ remainingBytes :=
      Nat.le_trans naturalCost fits
    obtain ⟨result, word, allocated, resultBudget⟩ :=
      valid.allocateNatural_eq_ok_of_budget scalar.payload.toNat budget
        naturalFits
    have encoded :
        encodeTagged state scalar.payload = .ok (result, word) := by
      simpa [allocateNatural, tagged, UInt64.ofNat_toNat] using allocated
    have boxed : boxScalar state scalar = .ok (result, word) := by
      rw [boxScalar_of_tagged state scalar tagged]
      exact encoded
    refine ⟨result, word, boxed, resultBudget.weaken ?_⟩
    exact Nat.sub_le_sub_left naturalCost remainingBytes
  · have heap : maxTaggedPayload < scalar.payload.toNat :=
      Nat.lt_of_not_ge tagged
    obtain ⟨middle, address, objectAllocation⟩ :=
      state.allocateObject_eq_ok_of_capacity .boxed
        target.semanticSlotBytes false scalar.kind.code
        (UInt32.ofNat scalar.kind.payloadBytes) 0 0 valid.cursorAligned
        (budget.allocationCapacity (by
          simpa only [boxScalarAllocationBytes, align8_align8] using fits))
    have middleValid := valid.allocateObject objectAllocation
    have middleExtent := MemoryState.allocateObject_extent objectAllocation
    have payloadInBounds :
        address.value + headerBytes + 7 < middle.memory.size := by
      have cursorInBounds := middleValid.cursorInBounds
      rw [middleExtent] at cursorInBounds
      simp [target, headerBytes, align8] at cursorInBounds ⊢
      omega
    obtain ⟨low, lowWrite, lowSize, _, _, _, _, _⟩ :=
      LinearMemory.writeUInt32_spec middle.memory
        (address.value + headerBytes) scalar.payload.toUInt32 (by omega)
    obtain ⟨memory, highWrite, _, _, _, _, _, _⟩ :=
      LinearMemory.writeUInt32_spec low
        (address.value + headerBytes + 4)
        (scalar.payload >>> (32 : UInt64)).toUInt32 (by
          simpa [lowSize] using payloadInBounds)
    have payloadWrite :
        middle.memory.writeUInt64 (address.value + headerBytes)
            scalar.payload =
          .ok memory := by
      unfold LinearMemory.writeUInt64
      rw [lowWrite]
      exact highWrite
    let result : MemoryState := { middle with memory }
    have allocated :
        allocateBoxedScalar state scalar = .ok (result, address) := by
      unfold allocateBoxedScalar
      dsimp only
      rw [objectAllocation]
      simp only [liftMemory, Bind.bind, Except.bind]
      rw [payloadWrite]
      rfl
    have boxed : boxScalar state scalar = .ok (result, address) := by
      rw [boxScalar_of_heap state scalar heap]
      exact allocated
    have middleBudget :=
      budget.allocateObject valid.cursorAligned (by
        simpa only [boxScalarAllocationBytes] using fits) objectAllocation
    exact ⟨result, address, boxed, {
      cursorPositive := middleBudget.cursorPositive
      endWithinAddressSpace := middleBudget.endWithinAddressSpace }⟩

/-- Writing a boxed payload immediately after the common header preserves the
complete checked header decoder. -/
theorem MemoryState.readLiveHeader_of_writeBoxedPayload
    (state : MemoryState) (result : LinearMemory) (address : Word32)
    (value : UInt64)
    (inBounds : address.value + headerBytes + 7 < state.memory.size)
    (written : state.memory.writeUInt64 (address.value + headerBytes) value =
      .ok result) :
    ({ state with memory := result } : MemoryState).readLiveHeader address =
      state.readLiveHeader address := by
  have lane (offset : Nat) (offsetEnd : offset + 3 < headerBytes) :
      result.readUInt32 (address.value + offset) =
        state.memory.readUInt32 (address.value + offset) :=
    LinearMemory.readUInt32_of_writeUInt64_eq_ok_other state.memory result
      (address.value + headerBytes) (address.value + offset) value inBounds written
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
    (address.value + headerBytes) value inBounds written
  unfold MemoryState.readLiveHeader
  dsimp only
  rw [headerRead, sizeEq]

/-- Installing a fresh heap-box payload preserves every previously owned byte
and therefore frames the complete pre-existing live heap. -/
theorem allocateBoxedScalar_prefixExtension
    (state result : MemoryState) (scalar : BoxedScalar) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocateBoxedScalar state scalar = .ok (result, address)) :
    state.PrefixExtension result := by
  obtain ⟨middle, objectAllocation, payloadWrite, cursorEq⟩ :=
    allocateBoxedScalar_decompose state result scalar address allocated
  have objectExtension := valid.allocateObject_prefixExtension objectAllocation
  have freshAddress := valid.allocateObject_address objectAllocation
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadInBounds :
      address.value + headerBytes + 7 < middle.memory.size := by
    have cursorInBounds := middleValid.cursorInBounds
    rw [middleExtent] at cursorInBounds
    simp [target, headerBytes, align8] at cursorInBounds ⊢
    omega
  have finalSize := LinearMemory.size_of_writeUInt64_eq_ok middle.memory result.memory
    (address.value + headerBytes) scalar.payload payloadInBounds payloadWrite
  refine {
    cursor := by simpa [cursorEq] using objectExtension.cursor
    memorySize := Nat.le_trans objectExtension.memorySize (by omega)
    readByte := ?_ }
  intro byte beforeCursor
  calc
    result.memory.readByte byte = middle.memory.readByte byte :=
      LinearMemory.readByte_of_writeUInt64_eq_ok_other middle.memory result.memory
        (address.value + headerBytes) scalar.payload payloadInBounds payloadWrite byte
        (.inl (by rw [freshAddress]; omega))
    _ = state.memory.readByte byte := objectExtension.readByte byte beforeCursor

/-- A successful heap-box allocation establishes the exact checked boxed
object relation and preserves the allocator's zero-frontier invariant. -/
theorem allocateBoxedScalar_objectRel
    (state result : MemoryState) (scalar : BoxedScalar) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocateBoxedScalar state scalar = .ok (result, address)) :
    result.FrontierInvariant ∧
      ∃ header,
        BoxedObjectRel result address scalar.kind scalar header ∧
        header.refCount.toNat = 1 ∧ header.persistent = false := by
  obtain ⟨middle, objectAllocation, payloadWrite, cursorEq⟩ :=
    allocateBoxedScalar_decompose state result scalar address allocated
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadInBounds :
      address.value + headerBytes + 7 < middle.memory.size := by
    have cursorInBounds := middleValid.cursorInBounds
    rw [middleExtent] at cursorInBounds
    simp [target, headerBytes, align8] at cursorInBounds ⊢
    omega
  have finalSize := LinearMemory.size_of_writeUInt64_eq_ok middle.memory result.memory
    (address.value + headerBytes) scalar.payload payloadInBounds payloadWrite
  have payloadRead := LinearMemory.readUInt64_of_writeUInt64_eq_ok middle.memory
    result.memory (address.value + headerBytes) scalar.payload payloadInBounds payloadWrite
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
      result.memory (address.value + headerBytes) scalar.payload payloadInBounds
        payloadWrite byte (.inr (by
          change middle.heapCursor ≤ byte at afterCursor
          rw [middleExtent] at afterCursor
          simp [target, headerBytes, align8] at afterCursor ⊢
          omega))
    cases resultByte : result.memory[byte]? with
    | none => simp [LinearMemory.readByte, resultByte, oldZero] at framed
    | some value =>
        simp [LinearMemory.readByte, resultByte, oldZero] at framed
        subst value
        rfl
  let header := Header.forAllocation .boxed
    (align8 (headerBytes + target.semanticSlotBytes)) false scalar.kind.code
      (UInt32.ofNat scalar.kind.payloadBytes)
  have headerBefore : middle.readLiveHeader address = .ok header := by
    simpa [header] using
      MemoryState.readLiveHeader_of_allocateObject_eq_ok state middle .boxed
        target.semanticSlotBytes false scalar.kind.code
          (UInt32.ofNat scalar.kind.payloadBytes) 0 0 address objectAllocation
  have headerFrame := middle.readLiveHeader_of_writeBoxedPayload result.memory address
    scalar.payload payloadInBounds payloadWrite
  have headerRead : result.readLiveHeader address = .ok header := by
    rw [← stateEq, headerFrame]
    exact headerBefore
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts result address header headerRead).1
  have decoded : readBoxedScalar result scalar.kind address = .ok scalar := by
    unfold readBoxedScalar
    rw [addressHeap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    have boxedBeq : (header.kind == ObjectKind.boxed) = true := by
      change (ObjectKind.boxed == ObjectKind.boxed) = true
      decide
    rw [boxedBeq]
    simp only [if_true]
    simpa [header] using
      readHeapBoxedScalar_forAllocation result address scalar payloadRead
  have resultExtent :
      address.value + header.allocationBytes.toNat ≤ result.heapCursor := by
    rw [cursorEq, middleExtent]
    simp [header, Header.forAllocation, target, headerBytes, align8]
  refine ⟨finalValid, header, ?_, ?_, ?_⟩
  · exact {
      scalarKind := rfl
      headerRead
      headerKind := rfl
      allocationBytes := by simp [header, Header.forAllocation, target, headerBytes]
      kindCode := rfl
      payloadBytes := rfl
      reserved2 := rfl
      reserved3 := rfl
      headerOwned := by
        have := resultExtent
        simp [header, Header.forAllocation, target, headerBytes, align8] at this ⊢
        omega
      extent := resultExtent
      decoded }
  · rfl
  · rfl

def semanticBoxCell (scalar : BoxedScalar) : HeapCell := {
  object := .boxed scalar.kind.semanticType scalar.semanticValue }

def semanticBoxResult (runtime : RuntimeState) (scalar : BoxedScalar) : RuntimeState := {
  runtime with
  heap := (runtime.nextLocation, semanticBoxCell scalar) :: runtime.heap
  nextLocation := runtime.nextLocation + 1 }

/-- Every scalar kind implemented by the concrete boxing runtime is an
integer kind, so the shared semantic predicate reduces to the historical
payload-size split. Floating boxes use a separate heap-only path. -/
@[simp] theorem boxUsesTaggedRepresentation_boxedScalar (scalar : BoxedScalar) :
    boxUsesTaggedRepresentation scalar.kind.semanticType scalar.payload =
      decide (scalar.payload.toNat ≤ maxTaggedPayload) := by
  cases scalar <;> simp [boxUsesTaggedRepresentation, BoxedScalar.kind,
    BoxedScalarKind.semanticType, BoxedScalar.payload,
    Lean.Compiler.LCNF.ImpureType.uint8, Lean.Compiler.LCNF.ImpureType.uint16,
    Lean.Compiler.LCNF.ImpureType.uint32, Lean.Compiler.LCNF.ImpureType.uint64,
    Lean.Compiler.LCNF.ImpureType.usize, Lean.Compiler.LCNF.ImpureType.float32,
    Lean.Compiler.LCNF.ImpureType.float] <;>
    intro <;> constructor <;> native_decide

/-- Concrete integer boxing sees the shared semantic box operation through
the same payload-size split as before the float-only heap rule was added. -/
theorem semanticBox_split (runtime : RuntimeState) (scalar : BoxedScalar) :
    Fir.LeanIR.Impure.box runtime scalar.kind.semanticType scalar.semanticValue =
      if scalar.payload.toNat ≤ maxTaggedPayload then
        .ok (runtime, .object (.tagged scalar.payload))
      else
        .ok (semanticBoxResult runtime scalar,
          .object (.heap runtime.nextLocation)) := by
  have nonfloating :
      (scalar.kind.semanticType == Lean.Compiler.LCNF.ImpureType.float32) = false ∧
      (scalar.kind.semanticType == Lean.Compiler.LCNF.ImpureType.float) = false := by
    cases scalar <;> simp only [BoxedScalar.kind, BoxedScalarKind.semanticType] <;>
      constructor <;> native_decide
  rcases nonfloating with ⟨notF32, notF64⟩
  cases scalar <;>
    simp only [BoxedScalar.kind, BoxedScalarKind.semanticType] at notF32 notF64 <;>
    simp [Fir.LeanIR.Impure.box, BoxedScalar.kind,
      BoxedScalarKind.semanticType, BoxedScalar.semanticValue,
      BoxedScalar.payload, ScalarValue.rawBits, ScalarValue.toUInt64,
      boxUsesTaggedRepresentation, notF32, notF64, alloc,
      semanticBoxResult, semanticBoxCell, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  all_goals
    rename_i value
    by_cases small : value.toNat ≤ maxTaggedPayload <;> simp [small]

theorem semanticBox_heap_eq (runtime : RuntimeState) (scalar : BoxedScalar)
    (heap : maxTaggedPayload < scalar.payload.toNat) :
    Fir.LeanIR.Impure.box runtime scalar.kind.semanticType scalar.semanticValue =
      .ok (semanticBoxResult runtime scalar,
        .object (.heap runtime.nextLocation)) := by
  rw [semanticBox_split, if_neg (Nat.not_le.mpr heap)]

/-- Heap-backed boxing extends the complete concrete/semantic live-heap
relation and relates the returned wasm32 address to the fresh semantic box. -/
theorem allocateBoxedScalar_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (scalar : BoxedScalar) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (allocated : allocateBoxedScalar state scalar = .ok (result, address)) :
    let nextWitness := witness.bindBoxed runtime.nextLocation address scalar.kind
    LiveHeapRel result nextWitness (semanticBoxResult runtime scalar) ∧
      ValueRel nextWitness .tobject (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨_, objectAllocation, _, _⟩ :=
    allocateBoxedScalar_decompose state result scalar address allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have extension := allocateBoxedScalar_prefixExtension state result scalar address
    related.frontier allocated
  obtain ⟨finalFrontier, header, objectRelated, headerRefCount, headerPersistent⟩ :=
    allocateBoxedScalar_objectRel state result scalar address related.frontier allocated
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
  have witnessExtension := witness.bindBoxed_extends runtime.nextLocation address
    scalar.kind locationFresh descriptorFresh
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
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts result address header
      objectRelated.headerRead).1
  have witnessWellFormed := related.witnessWellFormed.bindBoxed
    runtime.nextLocation address scalar.kind addressHeap locationAddressFresh
      promotedAddressFresh
  obtain ⟨_, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address header
      objectRelated.headerRead
  have newRegion : ∃ newHeader,
      Header.read result.memory address = .ok newHeader ∧
      headerBytes ≤ newHeader.allocationBytes.toNat ∧
      newHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + newHeader.allocationBytes.toNat ≤ result.heapCursor :=
    ⟨header, rawHeaderRead, headerMinimum, headerAligned, objectRelated.extent⟩
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial extension address freshAddress
      (fun other different =>
        witness.lookup_bindBoxed_descriptor_other runtime.nextLocation address other
          scalar.kind different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindBoxed runtime.nextLocation address scalar.kind) address
      (semanticBoxCell scalar) := by
    apply LiveCellRel.boxed
      (RefinementWitness.lookup_bindBoxed_descriptor witness runtime.nextLocation
        address scalar.kind)
      (by rfl) objectRelated
    · simpa [semanticBoxCell] using headerRefCount
    · simpa [semanticBoxCell] using headerPersistent
    · rfl
  refine ⟨?_, ValueRel.new_boxed_result witness runtime.nextLocation address scalar.kind⟩
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
        simpa [semanticBoxResult, findCell?, isNew, Ne.symm isNew] using found
      have oldBefore := related.locationsBeforeNext location cell oldFound
      exact Nat.lt_trans oldBefore (Nat.lt_succ_self runtime.nextLocation)
  · have cursorGrowth : state.heapCursor + headerBytes ≤ result.heapCursor := by
      rw [← freshAddress]
      exact objectRelated.headerOwned
    have oldFuel := related.releaseFuelBound
    simp [semanticBoxResult, headerBytes] at oldFuel cursorGrowth ⊢
    omega
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact objectRelated.headerOwned
    · rw [witness.lookup_bindBoxed_descriptor_other runtime.nextLocation address
        other scalar.kind isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticBoxCell scalar := by
        simpa [semanticBoxResult, findCell?] using found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindBoxed_location witness runtime.nextLocation
          address scalar.kind,
        .live newCellRelated⟩
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticBoxResult, findCell?, isNew, Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindBoxed, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticBoxCell scalar,
        by simp [semanticBoxResult, findCell?], .live newCellRelated⟩
    · rw [witness.lookup_bindBoxed_location_other runtime.nextLocation location
        address scalar.kind isNew] at mapped
      obtain ⟨cell, oldFound, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticBoxResult, findCell?, isNew, Ne.symm isNew],
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro payload concreteAddress mapped
    exact ((related.promoted payload concreteAddress mapped).prefixExtension extension)
      |>.witnessExtension witnessExtension

theorem scalarFromType_boxedScalarKind (kind : BoxedScalarKind) (payload : UInt64) :
    scalarFromType kind.semanticType payload =
      .ok (BoxedScalar.ofPayload kind payload).semanticValue := by
  cases kind with
  | uint8 =>
      unfold scalarFromType
      rw [if_pos (by native_decide)]
      rfl
  | uint16 =>
      unfold scalarFromType
      rw [if_neg (by native_decide), if_pos (by native_decide)]
      rfl
  | uint32 =>
      unfold scalarFromType
      rw [if_neg (by native_decide), if_neg (by native_decide),
        if_pos (by native_decide)]
      rfl
  | uint64 =>
      unfold scalarFromType
      rw [if_neg (by native_decide), if_neg (by native_decide),
        if_neg (by native_decide), if_pos (by native_decide)]
      rfl
  | usize =>
      unfold scalarFromType
      rw [if_neg (by native_decide), if_neg (by native_decide),
        if_neg (by native_decide), if_neg (by native_decide),
        if_pos (by native_decide)]
      rfl

/-- Checked heap-box decoding refines the actual semantic `unbox` operation
for a mapped live boxed cell. The descriptor fixes the ABI result kind; the
semantic heap branch intentionally returns the stored scalar value. -/
theorem LiveHeapRel.readBoxedScalar_heap_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {kind : BoxedScalarKind}
    {value : Value}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (descriptor : witness.descriptors.lookup? address = some (.boxed kind))
    (unboxed : Fir.LeanIR.Impure.unbox runtime kind.semanticType
      (.object (.heap location)) = .ok value) :
    ∃ scalar,
      readBoxedScalar state kind address = .ok scalar ∧
      value = scalar.semanticValue ∧
      ValueRel witness kind.abiKind scalar.lane value := by
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  have live : cell.live = true := by
    cases liveEq : cell.live with
    | false =>
        simp [Fir.LeanIR.Impure.unbox, getLiveCell, found, liveEq,
          Bind.bind, Except.bind] at unboxed
    | true => rfl
  have cellRelated := cellRelation.live_of_eq_true live
  cases cellRelated
  case constructor storedDescriptor objectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  case boxed storedDescriptor objectRelated objectEq refCount persistent cellLive =>
      rw [storedDescriptor] at descriptor
      have kindEq := AllocationDescriptor.boxed.inj (Option.some.inj descriptor)
      cases kindEq
      rename_i actualScalar actualHeader
      simp [Fir.LeanIR.Impure.unbox, getLiveCell, found, live] at unboxed
      simp only [Bind.bind, Except.bind] at unboxed
      rw [objectEq] at unboxed
      change Except.ok _ = Except.ok value at unboxed
      have returned := Except.ok.inj unboxed
      refine ⟨actualScalar, objectRelated.decoded, returned.symm, ?_⟩
      have resultRel := BoxedScalar.valueRel witness actualScalar
      rw [objectRelated.scalarKind] at resultRel
      simpa [returned] using resultRel
  case natural storedDescriptor objectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  case integer storedDescriptor objectEq objectRelated refCount persistent cellLive =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  case string storedDescriptor objectEq objectRelated refCount persistent cellLive =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  case array storedDescriptor objectEq objectRelated refCount persistent cellLive =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  case closure closureRelated =>
      obtain ⟨function, arity, captureKinds, storedDescriptor⟩ :=
        closureRelated.descriptor
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible

/-- The public concrete boxing operation and FIR's semantic boxing operation
take the same heap branch above the 63-bit tagged limit. -/
theorem boxScalar_heap_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (scalar : BoxedScalar) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (heap : maxTaggedPayload < scalar.payload.toNat)
    (boxed : boxScalar state scalar = .ok (result, address)) :
    Fir.LeanIR.Impure.box runtime scalar.kind.semanticType scalar.semanticValue =
        .ok (semanticBoxResult runtime scalar,
          .object (.heap runtime.nextLocation)) ∧
      let nextWitness := witness.bindBoxed runtime.nextLocation address scalar.kind
      LiveHeapRel result nextWitness (semanticBoxResult runtime scalar) ∧
        ValueRel nextWitness .tobject (.word32 address)
          (.object (.heap runtime.nextLocation)) := by
  have allocated : allocateBoxedScalar state scalar = .ok (result, address) := by
    rw [← boxScalar_of_heap state scalar heap]
    exact boxed
  exact ⟨semanticBox_heap_eq runtime scalar heap,
    allocateBoxedScalar_liveHeapRel state result witness runtime scalar address
      related allocated⟩

/-- Below FIR's 63-bit tagged limit, semantic boxing leaves the heap unchanged
and returns the tagged payload for every supported integer scalar kind. -/
theorem semanticBox_tagged_eq (runtime : RuntimeState) (scalar : BoxedScalar)
    (tagged : scalar.payload.toNat ≤ maxTaggedPayload) :
    Fir.LeanIR.Impure.box runtime scalar.kind.semanticType scalar.semanticValue =
      .ok (runtime, .object (.tagged scalar.payload)) := by
  rw [semanticBox_split, if_pos tagged]

/-- The public concrete boxing operation and semantic boxing agree throughout
the tagged range, whether wasm32 can use a direct immediate or must allocate a
persistent promoted representation. -/
theorem boxScalar_tagged_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (scalar : BoxedScalar) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (tagged : scalar.payload.toNat ≤ maxTaggedPayload)
    (boxed : boxScalar state scalar = .ok (result, word)) :
    Fir.LeanIR.Impure.box runtime scalar.kind.semanticType scalar.semanticValue =
        .ok (runtime, .object (.tagged scalar.payload)) ∧
      ∃ nextWitness,
        LiveHeapRel result nextWitness runtime ∧
        ValueRel nextWitness .tobject (.word32 word)
          (.object (.tagged scalar.payload)) := by
  have encoded : encodeTagged state scalar.payload = .ok (result, word) := by
    rw [← boxScalar_of_tagged state scalar tagged]
    exact boxed
  exact ⟨semanticBox_tagged_eq runtime scalar tagged,
    encodeTagged_liveHeapRel state result witness runtime scalar.payload word
      related encoded⟩

/-- Direct immediates and persistent promoted naturals decode identically at
the typed scalar boundary. -/
theorem LiveHeapRel.readBoxedScalar_tagged_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload)
    (kind : BoxedScalarKind) :
    let scalar := BoxedScalar.ofPayload kind payload
    readBoxedScalar state kind word = .ok scalar ∧
      Fir.LeanIR.Impure.unbox runtime kind.semanticType
        (.object (.tagged payload)) = .ok scalar.semanticValue ∧
      ValueRel witness kind.abiKind scalar.lane scalar.semanticValue := by
  dsimp only
  have semantic : Fir.LeanIR.Impure.unbox runtime kind.semanticType
      (.object (.tagged payload)) =
        .ok (BoxedScalar.ofPayload kind payload).semanticValue := by
    unfold Fir.LeanIR.Impure.unbox
    exact scalarFromType_boxedScalarKind kind payload
  have valueRelated := BoxedScalar.valueRel witness
    (BoxedScalar.ofPayload kind payload)
  simp only [BoxedScalar.kind_ofPayload] at valueRelated
  refine ⟨?_, semantic, valueRelated⟩
  cases tagged with
  | immediate actualPayload fits =>
      unfold readBoxedScalar
      simp [Word32.classify_encodeImmediate, Word32.decode_encodeImmediate]
      rfl
  | promoted found =>
      have promoted := related.promoted payload word found
      obtain ⟨header, headerRead, headerKind, persistent, _, marker, _, _⟩ :=
        promoted.header
      have addressHeap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state word header
          headerRead).1
      have notBoxed : (header.kind == ObjectKind.boxed) = false := by
        rw [headerKind]
        decide
      have isPromoted :
          (header.kind == ObjectKind.natural && header.persistent &&
            header.aux0 == promotedTagMarker) = true := by
        rw [headerKind, persistent, marker]
        decide
      unfold readBoxedScalar
      rw [addressHeap]
      simp only
      rw [headerRead]
      simp only [Bind.bind, Except.bind, liftMemory]
      rw [if_neg (by simp [notBoxed])]
      rw [if_pos (by simpa using isPromoted)]
      rw [promoted.decoded]
      rfl

/-- A released mapped object is rejected before the concrete boxed-kind
decoder inspects its header metadata. -/
theorem DeadCellRel.readBoxedScalar_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (kind : BoxedScalarKind) :
    readBoxedScalar state kind address =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨_, _, addressHeap, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    related.header
  unfold readBoxedScalar
  rw [addressHeap]
  simp only
  rw [related.readLiveHeader_eq]
  rfl

/-- Stale semantic and concrete heap references agree at the typed unbox
boundary, retaining the witness-related physical address/source location pair.
-/
theorem LiveHeapRel.readBoxedScalar_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) (kind : BoxedScalarKind) :
    readBoxedScalar state kind address =
        .error (.sourceAddress (.deadObject address)) ∧
      Fir.LeanIR.Impure.unbox runtime kind.semanticType
          (.object (.heap location)) =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  exact ⟨deadRelated.readBoxedScalar_eq kind, by
    simp [Fir.LeanIR.Impure.unbox, getLiveCell, found, dead]
    rfl⟩

/-- A representation-polymorphic object rejected by FIR as a non-scalar is
rejected by the concrete typed decoder with the same source fault. Tagged
representations and live boxes are eliminated by the source failure premise;
every represented live non-box heap shape fails after the common live-header
read. -/
theorem LiveHeapRel.readBoxedScalar_expectedScalar_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {word : Word32} {value : Value} (kind : BoxedScalarKind)
    (related : LiveHeapRel state witness runtime)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (unboxFailed :
      Fir.LeanIR.Impure.unbox runtime kind.semanticType value =
        .error .expectedScalar) :
    readBoxedScalar state kind word =
      .error (.source .expectedScalar) := by
  have failOfHeader (header : Header)
      (headerRead : state.readLiveHeader word = .ok header)
      (notBoxed : header.kind ≠ .boxed)
      (notPromoted : header.isPromotedTag = false) :
      readBoxedScalar state kind word =
        .error (.source .expectedScalar) := by
    have heap :=
      (MemoryState.PrefixExtension.readLiveHeader_facts state word header
        headerRead).1
    unfold readBoxedScalar
    rw [heap]
    simp only [headerRead, Bind.bind, Except.bind, liftMemory]
    have boxedFalse : (header.kind == .boxed) = false := by
      cases kindEq : header.kind
      case boxed => contradiction
      all_goals native_decide
    rw [boxedFalse]
    have promotedFalse :
        (header.kind == ObjectKind.natural && header.persistent &&
          header.aux0 == promotedTagMarker) = false := by
      simpa [Header.isPromotedTag] using notPromoted
    simp [promotedFalse]
    rfl
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | tagged taggedRelated =>
          obtain ⟨_, semantic, _⟩ :=
            related.readBoxedScalar_tagged_refines taggedRelated kind
          rw [unboxFailed] at semantic
          contradiction
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨cell, found, cellRelation⟩ :=
                related.concreteToSemantic _ _ mapped
              have live : cell.live = true := by
                cases liveEq : cell.live with
                | false =>
                    simp [Fir.LeanIR.Impure.unbox, getLiveCell, found, liveEq]
                      at unboxFailed
                    simp only [Bind.bind, Except.bind] at unboxFailed
                    have faultEq := Except.error.inj unboxFailed
                    cases faultEq
                | true => rfl
              have liveRelated := cellRelation.live_of_eq_true live
              cases liveRelated with
              | constructor descriptor objectEq objectRelated headerRead
                  headerKind refCount persistent cellLive =>
                  have different :
                      (ObjectKind.constructor == ObjectKind.natural) = false := by
                    decide
                  exact failOfHeader _ headerRead (by simp [headerKind])
                    (by simp [Header.isPromotedTag, headerKind, different])
              | boxed descriptor objectEq objectRelated refCount persistent
                  cellLive =>
                  simp [Fir.LeanIR.Impure.unbox, getLiveCell, found, live]
                    at unboxFailed
                  simp only [Bind.bind, Except.bind] at unboxFailed
                  rw [objectEq] at unboxFailed
                  contradiction
              | natural descriptor objectEq headerRead headerKind marker extent
                  limbsFit decoded refCount persistent cellLive =>
                  exact failOfHeader _ headerRead (by simp [headerKind])
                    (by simp [Header.isPromotedTag, headerKind, marker,
                      bigNaturalMarker, promotedTagMarker])
              | integer descriptor objectEq objectRelated refCount persistent
                  cellLive =>
                  have different :
                      (ObjectKind.integer == ObjectKind.natural) = false := by
                    decide
                  exact failOfHeader _ objectRelated.headerRead
                    (by simp [objectRelated.headerKind])
                    (by simp [Header.isPromotedTag, objectRelated.headerKind,
                      different])
              | string descriptor objectEq objectRelated refCount persistent
                  cellLive =>
                  have different :
                      (ObjectKind.string == ObjectKind.natural) = false := by
                    decide
                  exact failOfHeader _ objectRelated.headerRead
                    (by simp [objectRelated.headerKind])
                    (by simp [Header.isPromotedTag, objectRelated.headerKind,
                      different])
              | array descriptor objectEq objectRelated refCount persistent
                  cellLive =>
                  have different :
                      (ObjectKind.opaque == ObjectKind.natural) = false := by
                    decide
                  exact failOfHeader _ objectRelated.headerRead
                    (by simp [objectRelated.headerKind])
                    (by simp [Header.isPromotedTag, objectRelated.headerKind,
                      different])
              | closure closureRelated =>
                  cases closureRelated with
                  | closure objectEq objectRelated headerRead headerKind
                      descriptorLookup fixedCount extent refCount persistent
                      cellLive =>
                      have different :
                          (ObjectKind.closure == ObjectKind.natural) = false := by
                        decide
                      exact failOfHeader _ headerRead (by simp [headerKind])
                        (by simp [Header.isPromotedTag, headerKind, different])

end Fir.Wasm.Concrete
