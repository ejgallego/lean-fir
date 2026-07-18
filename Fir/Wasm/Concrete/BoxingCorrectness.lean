import Fir.Wasm.Concrete.HeapRefinement
import Fir.Wasm.Concrete.FreshAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

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
      change Except.error (ConcreteError.target failure) =
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
          change Except.error (ConcreteError.target failure) =
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
      ordinary := rfl
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

theorem semanticBox_heap_eq (runtime : RuntimeState) (scalar : BoxedScalar)
    (heap : maxTaggedPayload < scalar.payload.toNat) :
    Fir.LeanIR.Impure.box runtime scalar.kind.semanticType scalar.semanticValue =
      .ok (semanticBoxResult runtime scalar,
        .object (.heap runtime.nextLocation)) := by
  cases scalar with
  | uint8 value =>
      have bound := value.toNat_lt
      simp [BoxedScalar.payload, maxTaggedPayload] at heap
      omega
  | uint16 value =>
      have bound := value.toNat_lt
      simp [BoxedScalar.payload, maxTaggedPayload] at heap
      omega
  | uint32 value =>
      have bound := value.toNat_lt
      simp [BoxedScalar.payload, maxTaggedPayload] at heap
      omega
  | uint64 value =>
      change maxTaggedPayload < value.toNat at heap
      unfold Fir.LeanIR.Impure.box
      simp only [BoxedScalar.kind, BoxedScalarKind.semanticType,
        BoxedScalar.semanticValue, ScalarValue.toUInt64, Bind.bind, Except.bind]
      rw [if_neg (Nat.not_le.mpr heap)]
      simp [alloc, semanticBoxResult, semanticBoxCell]
      rfl
  | usize value =>
      change maxTaggedPayload < value.toNat at heap
      unfold Fir.LeanIR.Impure.box
      simp only [BoxedScalar.kind, BoxedScalarKind.semanticType,
        BoxedScalar.semanticValue, Bind.bind, Except.bind]
      rw [if_neg (Nat.not_le.mpr heap)]
      simp [alloc, semanticBoxResult, semanticBoxCell]
      rfl

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
        obtain ⟨cell, semanticFound, _, _⟩ :=
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
    obtain ⟨cell, _, _, cellRelated⟩ :=
      related.concreteToSemantic old oldAddress found
    have owned := cellRelated.headerOwned
    subst oldAddress
    simp [headerBytes] at owned
    omega
  have promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.lookup? payload = some oldAddress → address ≠ oldAddress := by
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
    descriptorsOwned := ?_
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
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact objectRelated.headerOwned
    · rw [witness.lookup_bindBoxed_descriptor_other runtime.nextLocation address
        other scalar.kind isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found live
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticBoxCell scalar := by
        simpa [semanticBoxResult, findCell?] using found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindBoxed_location witness runtime.nextLocation
          address scalar.kind,
        newCellRelated⟩
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticBoxResult, findCell?, isNew, Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound live
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindBoxed, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticBoxCell scalar,
        by simp [semanticBoxResult, findCell?], rfl, newCellRelated⟩
    · rw [witness.lookup_bindBoxed_location_other runtime.nextLocation location
        address scalar.kind isNew] at mapped
      obtain ⟨cell, oldFound, live, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticBoxResult, findCell?, isNew, Ne.symm isNew],
        live, (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro payload concreteAddress mapped
    have oldMapped : witness.promotedTags.lookup? payload = some concreteAddress := mapped
    exact ((related.promoted payload concreteAddress oldMapped).prefixExtension extension)
      |>.witnessExtension witnessExtension

theorem scalarFromType_boxedScalarKind (kind : BoxedScalarKind) (payload : UInt64) :
    scalarFromType kind.semanticType payload =
      .ok (BoxedScalar.ofPayload kind payload).semanticValue := by
  cases kind with
  | uint8 =>
      unfold scalarFromType
      simp only [BoxedScalarKind.semanticType, BoxedScalar.ofPayload,
        BoxedScalar.semanticValue]
      rw [if_pos (by native_decide)]
  | uint16 =>
      unfold scalarFromType
      simp only [BoxedScalarKind.semanticType, BoxedScalar.ofPayload,
        BoxedScalar.semanticValue]
      rw [if_neg (by native_decide), if_pos (by native_decide)]
  | uint32 =>
      unfold scalarFromType
      simp only [BoxedScalarKind.semanticType, BoxedScalar.ofPayload,
        BoxedScalar.semanticValue]
      rw [if_neg (by native_decide), if_neg (by native_decide),
        if_pos (by native_decide)]
  | uint64 =>
      unfold scalarFromType
      simp only [BoxedScalarKind.semanticType, BoxedScalar.ofPayload,
        BoxedScalar.semanticValue]
      rw [if_neg (by native_decide), if_neg (by native_decide),
        if_neg (by native_decide), if_pos (by native_decide)]
  | usize =>
      unfold scalarFromType
      simp only [BoxedScalarKind.semanticType, BoxedScalar.ofPayload,
        BoxedScalar.semanticValue]
      rw [if_neg (by native_decide), if_neg (by native_decide),
        if_neg (by native_decide), if_neg (by native_decide),
        if_pos (by native_decide)]

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
  obtain ⟨cell, found, live, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
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
  case natural storedDescriptor objectEq headerRead headerKind ordinary marker extent
      limbsFit decoded refCount persistent cellLive =>
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

end Fir.Wasm.Concrete
