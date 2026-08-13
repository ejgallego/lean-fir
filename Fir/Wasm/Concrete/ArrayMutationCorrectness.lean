import Fir.Wasm.Concrete.ArrayHeapCorrectness
import Fir.Wasm.Concrete.PayloadMutationFrameCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- One ownership-neutral low-word replacement updates exactly one live Array
element, preserves the complete retained allocation boundary, and leaves the
frontier invariant intact. -/
theorem ResidentArrayObjectRel.writeElementRaw_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {elements : Array Value} {capacity : Nat} {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (valid : state.FrontierInvariant)
    (index : Nat) (value : Value) (word : Word32)
    (indexValid : index < elements.size)
    (valueRelated : ValueRel witness .tobject (.word32 word) value) :
    ∃ result,
      writeResidentArrayElementRaw state address index word = .ok result ∧
      state.TargetMutationFrame result address header.allocationBytes.toNat ∧
      result.FrontierInvariant ∧
      ResidentArrayObjectRel result witness address
        (elements.set index value indexValid) capacity header := by
  let offset := address.value + headerBytes + target.semanticSlotBytes * index
  have writeInBounds : offset + 3 < state.memory.size := by
    have allocationInMemory :
        address.value + residentArrayAllocationBytes capacity ≤ state.memory.size :=
      Nat.le_trans related.extent valid.cursorInBounds
    have sizeCapacity := related.sizeCapacity
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * capacity)
    simp [offset, residentArrayAllocationBytes, target] at allocationInMemory aligned ⊢
    omega
  obtain ⟨memory, written, memorySize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec state.memory offset (UInt32.ofNat word.value)
      writeInBounds
  have wordWritten : state.memory.writeWord32 offset word = .ok memory := written
  let result : MemoryState := { state with memory }
  have operation :
      writeResidentArrayElementRaw state address index word = .ok result := by
    unfold writeResidentArrayElementRaw
    rw [related.readHeader]
    simp only [Bind.bind, Except.bind]
    rw [if_pos (by simpa [related.logicalSize] using indexValid)]
    change (do
      let nextMemory ← liftMemory (state.memory.writeWord32 offset word)
      return ({ state with memory := nextMemory } : MemoryState)) = .ok result
    rw [wordWritten]
    rfl
  have afterHeader : address.value + headerBytes ≤ offset := by
    simp [offset]
  have insideTarget :
      offset + 4 ≤ address.value + header.allocationBytes.toNat := by
    rw [related.allocationBytes]
    have sizeCapacity := related.sizeCapacity
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * capacity)
    simp [offset, residentArrayAllocationBytes, target] at aligned ⊢
    omega
  have targetFrame :
      state.TargetMutationFrame result address header.allocationBytes.toNat :=
    MemoryState.TargetMutationFrame.ofWriteUInt32 rfl writeInBounds written
      afterHeader insideTarget
  have finalValid : result.FrontierInvariant :=
    valid.writeUInt32 (Nat.le_trans insideTarget (by
      rw [related.allocationBytes]
      exact related.extent)) written
  have targetRead : memory.readWord32 offset = .ok word :=
    LinearMemory.readWord32_of_writeWord32_eq_ok state.memory memory offset word
      writeInBounds wordWritten
  have readOther : ∀ other, other ≠ index →
      memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * other) =
        state.memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * other) := by
    intro other different
    unfold LinearMemory.readWord32
    rw [LinearMemory.readUInt32_of_writeUInt32_eq_ok_other state.memory memory
      offset (address.value + headerBytes + target.semanticSlotBytes * other)
      (UInt32.ofNat word.value) writeInBounds written (by
        simp [offset, target]
        omega)]
  refine ⟨result, operation, targetFrame, finalValid, ?_⟩
  refine {
    headerRead := by rw [targetFrame.targetLiveHeader]; exact related.headerRead
    headerKind := related.headerKind
    marker := related.marker
    logicalSize := by simpa using related.logicalSize
    physicalCapacity := related.physicalCapacity
    reserved := related.reserved
    sizeCapacity := by simpa using related.sizeCapacity
    allocationBytes := related.allocationBytes
    headerOwned := by rw [targetFrame.cursor]; exact related.headerOwned
    extent := by rw [targetFrame.cursor]; exact related.extent
    liveElements := ?_ }
  intro other semanticValue valueAt
  by_cases same : other = index
  · subst other
    have valueEq : semanticValue = value := by
      rw [Array.getElem?_set_self indexValid] at valueAt
      exact (Option.some.inj valueAt).symm
    subst semanticValue
    exact ⟨word, by simpa [offset] using targetRead, valueRelated⟩
  · have oldValueAt : elements[other]? = some semanticValue := by
      rw [Array.getElem?_set_ne indexValid (Ne.symm same)] at valueAt
      exact valueAt
    obtain ⟨oldWord, oldRead, oldRelated⟩ :=
      related.liveElements other semanticValue oldValueAt
    exact ⟨oldWord, by rw [readOther other same]; exact oldRead, oldRelated⟩

/-- Writing a currently-spare capacity slot preserves the complete live Array
relation while producing a target-allocation frame. -/
theorem ResidentArrayObjectRel.writeCapacityElementRaw_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {elements : Array Value} {capacity : Nat} {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (valid : state.FrontierInvariant)
    (index : Nat) (word : Word32)
    (afterLive : elements.size ≤ index) (beforeCapacity : index < capacity) :
    ∃ result,
      writeResidentArrayCapacityElementRaw state address index word = .ok result ∧
      state.TargetMutationFrame result address header.allocationBytes.toNat ∧
      result.FrontierInvariant ∧
      ResidentArrayObjectRel result witness address elements capacity header ∧
      result.memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * index) =
        .ok word := by
  let offset := address.value + headerBytes + target.semanticSlotBytes * index
  have writeInBounds : offset + 3 < state.memory.size := by
    have allocationInMemory :
        address.value + residentArrayAllocationBytes capacity ≤ state.memory.size :=
      Nat.le_trans related.extent valid.cursorInBounds
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * capacity)
    simp [offset, residentArrayAllocationBytes, target] at allocationInMemory aligned ⊢
    omega
  obtain ⟨memory, written, _, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec state.memory offset (UInt32.ofNat word.value)
      writeInBounds
  have wordWritten : state.memory.writeWord32 offset word = .ok memory := written
  let result : MemoryState := { state with memory }
  have operation :
      writeResidentArrayCapacityElementRaw state address index word = .ok result := by
    unfold writeResidentArrayCapacityElementRaw
    rw [related.readHeader]
    simp only [Bind.bind, Except.bind]
    rw [if_pos (by simpa [related.physicalCapacity] using beforeCapacity)]
    change (do
      let nextMemory ← liftMemory (state.memory.writeWord32 offset word)
      return ({ state with memory := nextMemory } : MemoryState)) = .ok result
    rw [wordWritten]
    rfl
  have afterHeader : address.value + headerBytes ≤ offset := by simp [offset]
  have insideTarget :
      offset + 4 ≤ address.value + header.allocationBytes.toNat := by
    rw [related.allocationBytes]
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * capacity)
    simp [offset, residentArrayAllocationBytes, target] at aligned ⊢
    omega
  have targetFrame :
      state.TargetMutationFrame result address header.allocationBytes.toNat :=
    MemoryState.TargetMutationFrame.ofWriteUInt32 rfl writeInBounds written
      afterHeader insideTarget
  have finalValid : result.FrontierInvariant :=
    valid.writeUInt32 (Nat.le_trans insideTarget (by
      rw [related.allocationBytes]
      exact related.extent)) written
  have targetRead : memory.readWord32 offset = .ok word :=
    LinearMemory.readWord32_of_writeWord32_eq_ok state.memory memory offset word
      writeInBounds wordWritten
  have liveRelated :
      ResidentArrayObjectRel result witness address elements capacity header := by
    refine {
      headerRead := by rw [targetFrame.targetLiveHeader]; exact related.headerRead
      headerKind := related.headerKind
      marker := related.marker
      logicalSize := related.logicalSize
      physicalCapacity := related.physicalCapacity
      reserved := related.reserved
      sizeCapacity := related.sizeCapacity
      allocationBytes := related.allocationBytes
      headerOwned := by rw [targetFrame.cursor]; exact related.headerOwned
      extent := by rw [targetFrame.cursor]; exact related.extent
      liveElements := ?_ }
    intro other value valueAt
    obtain ⟨oldWord, oldRead, oldRelated⟩ :=
      related.liveElements other value valueAt
    have otherLt : other < elements.size :=
      (Array.getElem?_eq_some_iff.mp valueAt).1
    have different : other ≠ index := by omega
    have readFrame : memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * other) =
        state.memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * other) := by
      unfold LinearMemory.readWord32
      rw [LinearMemory.readUInt32_of_writeUInt32_eq_ok_other state.memory memory
        offset (address.value + headerBytes + target.semanticSlotBytes * other)
        (UInt32.ofNat word.value) writeInBounds written (by
          simp [offset, target]
          omega)]
    exact ⟨oldWord, by rw [readFrame]; exact oldRead, oldRelated⟩
  exact ⟨result, operation, targetFrame, finalValid, liveRelated,
    by simpa [offset] using targetRead⟩

/-- Changing only `aux1` establishes the exact relation for a caller-supplied
live prefix whose slots are already related in memory. This theorem is valid
for growth after ownership transfer and for shrink after removed children
have been released. -/
theorem ResidentArrayObjectRel.writeLogicalSizeRaw
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {elements nextElements : Array Value} {capacity : Nat} {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (valid : state.FrontierInvariant) (nextSize : Nat)
    (nextCount : nextElements.size = nextSize)
    (nextCapacity : nextSize ≤ capacity)
    (nextFits : nextSize < UInt32.size)
    (each : ∀ (index : Nat) (value : Value),
      nextElements[index]? = some value →
      ∃ word,
        state.memory.readWord32
            (address.value + headerBytes + target.semanticSlotBytes * index) =
          .ok word ∧
        ValueRel witness .tobject (.word32 word) value) :
    ∃ result updatedHeader memory,
      writeResidentArrayLogicalSizeRaw state address nextSize = .ok result ∧
      updatedHeader = { header with aux1 := UInt32.ofNat nextSize } ∧
      result = { state with memory } ∧
      updatedHeader.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      ResidentArrayObjectRel result witness address nextElements capacity
        updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      related.headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans related.headerOwned valid.cursorInBounds
  let updatedHeader : Header := { header with aux1 := UInt32.ofNat nextSize }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation :
      writeResidentArrayLogicalSizeRaw state address nextSize = .ok result := by
    unfold writeResidentArrayLogicalSizeRaw
    rw [related.readHeader]
    simp only [Bind.bind, Except.bind]
    rw [if_pos (by simpa [related.physicalCapacity] using nextCapacity)]
    rw [uint32Field_eq_ok "Array logical size" nextSize nextFits]
    change writeLiveHeader state address updatedHeader = .ok result
    unfold writeLiveHeader
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory,
      nextCount, nextCapacity]
    rfl
  have finalValid : result.FrontierInvariant :=
    valid.writeHeader related.headerOwned headerWrite
  refine ⟨result, updatedHeader, memory, operation, rfl, rfl, headerWrite,
    finalValid, ?_⟩
  refine {
    headerRead := headerReadAfter
    headerKind := by simpa [updatedHeader] using related.headerKind
    marker := by simpa [updatedHeader] using related.marker
    logicalSize := by
      change (UInt32.ofNat nextSize).toNat = nextElements.size
      rw [UInt32.toNat_ofNat_of_lt' nextFits, nextCount]
    physicalCapacity := by simpa [updatedHeader] using related.physicalCapacity
    reserved := by simpa [updatedHeader] using related.reserved
    sizeCapacity := by omega
    allocationBytes := by simpa [updatedHeader] using related.allocationBytes
    headerOwned := related.headerOwned
    extent := related.extent
    liveElements := ?_ }
  intro index value valueAt
  obtain ⟨word, readBefore, valueRelated⟩ := each index value valueAt
  refine ⟨word, ?_, valueRelated⟩
  change memory.readWord32 _ = .ok word
  rw [Header.readWord32_of_write_eq_ok_payload state.memory memory address
    updatedHeader
    (address.value + headerBytes + target.semanticSlotBytes * index)
    headerInBounds headerWrite (by omega)]
  exact readBefore

/-- Unique in-place push first initializes the spare slot and only then makes
 it live. The composed local theorem therefore never exposes an uninitialized
 semantic child. -/
theorem ResidentArrayObjectRel.pushElementInPlaceRaw
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {elements : Array Value} {capacity : Nat} {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (valid : state.FrontierInvariant) (value : Value) (word : Word32)
    (spare : elements.size < capacity)
    (valueRelated : ValueRel witness .tobject (.word32 word) value) :
    ∃ middle result updatedHeader memory,
      pushResidentArrayElementInPlaceRaw state address word = .ok result ∧
      writeResidentArrayCapacityElementRaw state address elements.size word =
        .ok middle ∧
      state.TargetMutationFrame middle address header.allocationBytes.toNat ∧
      middle.FrontierInvariant ∧
      ResidentArrayObjectRel middle witness address elements capacity header ∧
      updatedHeader = {
        header with aux1 := UInt32.ofNat (elements.size + 1) } ∧
      result = { middle with memory } ∧
      updatedHeader.write middle.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      ResidentArrayObjectRel result witness address (elements.push value)
        capacity updatedHeader := by
  obtain ⟨middle, capacityWrite, capacityFrame, middleValid, middleRelated,
      newRead⟩ :=
    related.writeCapacityElementRaw_targetFrame valid elements.size word
      (Nat.le_refl _) spare
  have nextFits : elements.size + 1 < UInt32.size := by
    have capacityFits : capacity < UInt32.size := by
      rw [← related.physicalCapacity]
      exact UInt32.toNat_lt_size header.aux2
    omega
  have pushedSize : (elements.push value).size = elements.size + 1 := by simp
  have pushedEach : ∀ (index : Nat) (semanticValue : Value),
      (elements.push value)[index]? = some semanticValue →
      ∃ concreteWord,
        middle.memory.readWord32
            (address.value + headerBytes + target.semanticSlotBytes * index) =
          .ok concreteWord ∧
        ValueRel witness .tobject (.word32 concreteWord) semanticValue := by
    intro index semanticValue valueAt
    rw [Array.getElem?_push] at valueAt
    by_cases isNew : index = elements.size
    · rw [if_pos isNew] at valueAt
      have valueEq : semanticValue = value := (Option.some.inj valueAt).symm
      subst semanticValue
      subst index
      exact ⟨word, newRead, valueRelated⟩
    · rw [if_neg isNew] at valueAt
      exact middleRelated.liveElements index semanticValue valueAt
  obtain ⟨result, updatedHeader, finalMemory, sizeWrite, updatedEq, resultEq,
      headerWrite, finalValid, finalRelated⟩ :=
    middleRelated.writeLogicalSizeRaw middleValid (elements.size + 1) pushedSize
      (by omega) nextFits pushedEach
  have operation :
      pushResidentArrayElementInPlaceRaw state address word = .ok result := by
    unfold pushResidentArrayElementInPlaceRaw
    rw [related.readSize]
    simp only [Bind.bind, Except.bind]
    rw [capacityWrite]
    exact sizeWrite
  exact ⟨middle, result, updatedHeader, finalMemory, operation, capacityWrite,
    capacityFrame, middleValid, middleRelated, updatedEq, resultEq, headerWrite,
    finalValid, finalRelated⟩

/-- Lowering logical size by one establishes the exact semantic `Array.pop`
prefix. Releasing the removed child is intentionally a later step: once this
header write succeeds, the Array no longer owns that child. -/
theorem ResidentArrayObjectRel.writeLogicalSizeRaw_pop
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {elements : Array Value} {capacity : Nat} {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (valid : state.FrontierInvariant) (nonempty : 0 < elements.size) :
    ∃ result updatedHeader memory,
      writeResidentArrayLogicalSizeRaw state address (elements.size - 1) =
        .ok result ∧
      updatedHeader = {
        header with aux1 := UInt32.ofNat (elements.size - 1) } ∧
      result = { state with memory } ∧
      updatedHeader.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      ResidentArrayObjectRel result witness address elements.pop capacity
        updatedHeader := by
  have poppedSize : elements.pop.size = elements.size - 1 := by simp
  have nextFits : elements.size - 1 < UInt32.size := by
    have sizeFits : elements.size < UInt32.size := by
      rw [← related.logicalSize]
      exact UInt32.toNat_lt_size header.aux1
    omega
  have each : ∀ (index : Nat) (value : Value),
      elements.pop[index]? = some value →
      ∃ word,
        state.memory.readWord32
            (address.value + headerBytes + target.semanticSlotBytes * index) =
          .ok word ∧
        ValueRel witness .tobject (.word32 word) value := by
    intro index value valueAt
    rw [Array.getElem?_pop] at valueAt
    split at valueAt
    · exact related.liveElements index value valueAt
    · contradiction
  exact related.writeLogicalSizeRaw valid (elements.size - 1) poppedSize
    (by have := related.sizeCapacity; omega) nextFits each

/-- Popping an empty resident Array is the exact concrete identity. No header,
payload, ownership, or frontier component changes. -/
theorem ResidentArrayObjectRel.popElementInPlace_empty
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {elements : Array Value} {capacity : Nat} {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (empty : elements.size = 0) :
    popResidentArrayElementInPlace state address = .ok state := by
  unfold popResidentArrayElementInPlace
  rw [related.readSize, empty]
  rfl

/-- Public checked release for one Array-owned `tobject` word. This is the
representation-polymorphic ownership boundary shared by pop and future
container-consuming helpers. -/
theorem LiveHeapRel.releaseTObject_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime nextRuntime : RuntimeState}
    {word : Word32} {value : Value}
    (related : LiveHeapRel state witness runtime)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (semanticOperation :
      Fir.LeanIR.Impure.decValueOnce runtime value true = .ok nextRuntime) :
    ∃ result,
      decrementReferenceOnce state word true witness.closureDescriptors =
        .ok result ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness := by
  cases valueRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              exact related.decrementReferenceOnce_refines_with_capacity mapped
                true (by simpa [Fir.LeanIR.Impure.decValueOnce] using
                  semanticOperation)
      | tagged taggedRelated =>
          have runtimeEq : nextRuntime = runtime := by
            simpa [Fir.LeanIR.Impure.decValueOnce] using
              (Except.ok.inj semanticOperation).symm
          subst nextRuntime
          refine ⟨state, ?_, related, .refl state witness⟩
          simpa using related.decrementReferenceOnce_tagged taggedRelated true
            (descriptors := witness.closureDescriptors)

/-- Complete successful nonempty exclusive-pop path. The semantic operation
is written as the same two observable ownership steps as the concrete helper:
first replace the Array by its popped prefix, then release the removed value.
This partial-correctness boundary intentionally assumes the semantic release
succeeds; the fault-refinement lane handles failing releases. -/
theorem LiveHeapRel.popResidentArrayElementInPlace_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime nextRuntime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {elements : Array Value} {capacity : Nat} {removed : Value}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .array elements capacity)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.array capacity))
    (nonempty : 0 < elements.size)
    (removedAt : elements[elements.size - 1]? = some removed)
    (semanticOperation :
      (do
        let next ← setCell runtime location
          { cell with object := .array elements.pop capacity }
        Fir.LeanIR.Impure.decValueOnce next removed true) = .ok nextRuntime) :
    ∃ result,
      popResidentArrayElementInPlace state address witness.closureDescriptors =
        .ok result ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness ∧
      result.heapCursor = state.heapCursor := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let replacement : HeapCell := {
    cell with object := .array elements.pop capacity }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive => rw [objectEq] at storedObjectEq; contradiction
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent limbsFit
      decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | integer descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | array descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have objectParts := HeapObject.array.inj storedObjectEq
      cases objectParts.1
      cases objectParts.2
      obtain ⟨removedWord, removedRead, removedRelated⟩ :=
        objectRelated.readElementBorrowed removedAt
      obtain ⟨middle, updatedHeader, memory, shrinkOperation, updatedEq,
          resultEq, headerWrite, middleValid, middleObjectRel⟩ :=
        objectRelated.writeLogicalSizeRaw_pop related.frontier nonempty
      obtain ⟨_, targetRawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _
          objectRelated.headerRead
      have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
        Nat.le_trans objectRelated.headerOwned related.frontier.cursorInBounds
      have middleCellRel : CellRel middle witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.array descriptor (by rfl)
          (by simpa [replacement] using middleObjectRel)
        · rw [updatedEq]
          simpa [replacement] using refCount
        · rw [updatedEq]
          simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨middleRuntime, semanticSet, middleHeapRel⟩ :=
        related.setCell_of_headerWrite mapped found descriptor targetRawRead
          resultEq headerInBounds headerWrite (by rw [updatedEq]) middleValid
            middleCellRel
      have semanticComposed :
          (do
            let next ← setCell runtime location replacement
            Fir.LeanIR.Impure.decValueOnce next removed true) =
              .ok nextRuntime := by
        simpa [replacement] using semanticOperation
      have semanticRelease :
          Fir.LeanIR.Impure.decValueOnce middleRuntime removed true =
            .ok nextRuntime := by
        rw [semanticSet] at semanticComposed
        exact semanticComposed
      obtain ⟨result, concreteRelease, finalHeapRel, releaseCapacity⟩ :=
        middleHeapRel.releaseTObject_refines removedRelated semanticRelease
      have concreteOperation :
          popResidentArrayElementInPlace state address witness.closureDescriptors =
            .ok result := by
        unfold popResidentArrayElementInPlace
        rw [objectRelated.readSize]
        simp only [Bind.bind, Except.bind]
        rw [if_neg (by omega)]
        rw [removedRead]
        simp only
        rw [shrinkOperation]
        exact concreteRelease
      have shrinkCapacity :=
        related.mappedHeaderCapacity_of_headerWrite descriptor targetRawRead
          resultEq headerInBounds headerWrite (by rw [updatedEq])
      have finalCursor : result.heapCursor = state.heapCursor := by
        calc
          result.heapCursor = middle.heapCursor :=
            decrementReferenceOnce_preserves_heapCursor concreteRelease
          _ = state.heapCursor := by rw [resultEq]
      exact ⟨result, concreteOperation, finalHeapRel,
        shrinkCapacity.trans releaseCapacity, finalCursor⟩
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- Replacing a found semantic cell by itself is the identity. This local
lemma lets a concrete spare-slot initialization cross the whole-heap frame
without inventing an observable semantic step. -/
private theorem replaceCell_same_of_find
    {heap : Heap} {location : Location} {cell : HeapCell}
    (found : findCell? heap location = some cell) :
    replaceCell heap location cell = some heap := by
  induction heap with
  | nil => simp [findCell?] at found
  | cons entry rest ih =>
      obtain ⟨candidate, current⟩ := entry
      by_cases here : candidate = location
      · subst candidate
        simp [findCell?] at found
        subst current
        simp [replaceCell]
      · have tailFound : findCell? rest location = some cell := by
          simpa [findCell?, here] using found
        simp [replaceCell, here, ih tailFound]

private theorem setCell_same_of_find
    {runtime : RuntimeState} {location : Location} {cell : HeapCell}
    (found : findCell? runtime.heap location = some cell) :
    setCell runtime location cell = .ok runtime := by
  unfold setCell
  rw [replaceCell_same_of_find found]

/-- Whole-heap refinement for a unique in-place Array push. The concrete
helper initializes the old spare slot without a semantic change, then the
logical-size header write performs exactly one semantic `Array.push`.

`valueRelated` is the ownership-transfer boundary: retain/copy policy is a
caller obligation, while this theorem proves the raw mutation itself. -/
theorem LiveHeapRel.pushResidentArrayElementInPlaceRaw_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {elements : Array Value} {capacity : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .array elements capacity)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.array capacity))
    (value : Value) (word : Word32) (spare : elements.size < capacity)
    (valueRelated : ValueRel witness .tobject (.word32 word) value) :
    ∃ result nextRuntime,
      pushResidentArrayElementInPlaceRaw state address word = .ok result ∧
      setCell runtime location
          { cell with object := .array (elements.push value) capacity } =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness ∧
      result.heapCursor = state.heapCursor := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let replacement : HeapCell := {
    cell with object := .array (elements.push value) capacity }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive => rw [objectEq] at storedObjectEq; contradiction
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent limbsFit
      decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | integer descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | array descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have objectParts := HeapObject.array.inj storedObjectEq
      cases objectParts.1
      cases objectParts.2
      obtain ⟨middle, result, updatedHeader, memory, operation, capacityWrite,
          capacityFrame, middleValid, middleObjectRel, updatedEq, resultEq,
          headerWrite, finalValid, finalObjectRel⟩ :=
        objectRelated.pushElementInPlaceRaw related.frontier value word spare
          valueRelated
      obtain ⟨_, targetRawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _
          objectRelated.headerRead
      have middleCellRel : CellRel middle witness address cell := by
        apply CellRel.live
        apply LiveCellRel.array descriptor objectEq middleObjectRel
        · simpa using refCount
        · simpa using persistent
        · simpa using cellLive
      obtain ⟨sameRuntime, semanticSame, middleHeapRel⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          capacityFrame middleValid middleCellRel
      have semanticIdentity : setCell runtime location cell = .ok runtime :=
        setCell_same_of_find found
      rw [semanticIdentity] at semanticSame
      have sameRuntimeEq : sameRuntime = runtime :=
        (Except.ok.inj semanticSame).symm
      subst sameRuntime
      obtain ⟨_, middleRawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts middle address _
          middleObjectRel.headerRead
      have headerInBounds :
          address.value + headerBytes ≤ middle.memory.size :=
        Nat.le_trans middleObjectRel.headerOwned middleValid.cursorInBounds
      have finalCellRel : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.array descriptor (by rfl)
          (by simpa [replacement] using finalObjectRel)
        · rw [updatedEq]
          simpa [replacement] using refCount
        · rw [updatedEq]
          simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, finalHeapRel⟩ :=
        middleHeapRel.setCell_of_headerWrite mapped found descriptor middleRawRead
          resultEq headerInBounds headerWrite (by rw [updatedEq]) finalValid
            finalCellRel
      have firstCapacity :=
        related.mappedHeaderCapacity_of_targetMutation descriptor targetRawRead
          capacityFrame
      have secondCapacity :=
        middleHeapRel.mappedHeaderCapacity_of_headerWrite descriptor middleRawRead
          resultEq headerInBounds headerWrite (by rw [updatedEq])
      have finalCursor : result.heapCursor = state.heapCursor := by
        rw [resultEq]
        exact capacityFrame.cursor
      exact ⟨result, nextRuntime, operation, by
          simpa [replacement] using semanticSet,
        finalHeapRel, firstCapacity.trans secondCapacity, finalCursor⟩
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- Whole-heap form of ownership-neutral Array replacement. The semantic side
uses the common `setCell` primitive explicitly, keeping retain/release duties
outside this raw store theorem. -/
theorem LiveHeapRel.writeResidentArrayElementRaw_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {elements : Array Value} {capacity : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .array elements capacity)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.array capacity))
    (index : Nat) (value : Value) (word : Word32)
    (indexValid : index < elements.size)
    (valueRelated : ValueRel witness .tobject (.word32 word) value) :
    ∃ result nextRuntime,
      writeResidentArrayElementRaw state address index word = .ok result ∧
      setCell runtime location
          { cell with object := .array (elements.set index value indexValid) capacity } =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness ∧
      result.heapCursor = state.heapCursor := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let replacement : HeapCell := {
    cell with object := .array (elements.set index value indexValid) capacity }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive => rw [objectEq] at storedObjectEq; contradiction
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent limbsFit
      decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | integer descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | array descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have objectParts := HeapObject.array.inj storedObjectEq
      cases objectParts.1
      cases objectParts.2
      obtain ⟨result, operation, targetFrame, finalValid, objectAfter⟩ :=
        objectRelated.writeElementRaw_targetFrame related.frontier index value word
          indexValid valueRelated
      obtain ⟨_, targetRawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _
          objectRelated.headerRead
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.array descriptor (by rfl)
          (by simpa [replacement] using objectAfter)
        · simpa [replacement] using refCount
        · simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          targetFrame finalValid targetAfter
      have capacityTransport :=
        related.mappedHeaderCapacity_of_targetMutation descriptor targetRawRead
          targetFrame
      exact ⟨result, nextRuntime, operation, by
          simpa [replacement] using semanticSet,
        heapRelated, capacityTransport, targetFrame.cursor⟩
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- The two raw stores used by resident `Array.swap` implement Lean's exact
semantic Array swap and compose to one complete target-allocation frame. -/
theorem ResidentArrayObjectRel.swapElementsRaw_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {elements : Array Value} {capacity : Nat} {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (valid : state.FrontierInvariant)
    (left right : Nat) (leftValid : left < elements.size)
    (rightValid : right < elements.size) :
    ∃ result,
      swapResidentArrayElementsRaw state address left right = .ok result ∧
      state.TargetMutationFrame result address header.allocationBytes.toNat ∧
      result.FrontierInvariant ∧
      ResidentArrayObjectRel result witness address
        (elements.swap left right leftValid rightValid) capacity header := by
  let leftValue := elements[left]
  let rightValue := elements[right]
  have leftAt : elements[left]? = some leftValue :=
    Array.getElem?_eq_getElem leftValid
  have rightAt : elements[right]? = some rightValue :=
    Array.getElem?_eq_getElem rightValid
  obtain ⟨leftWord, leftRead, leftRelated⟩ :=
    related.readElementBorrowed leftAt
  obtain ⟨rightWord, rightRead, rightRelated⟩ :=
    related.readElementBorrowed rightAt
  obtain ⟨middle, leftWrite, leftFrame, middleValid, middleRelated⟩ :=
    related.writeElementRaw_targetFrame valid left rightValue rightWord leftValid
      rightRelated
  have rightValidMiddle :
      right < (elements.set left rightValue leftValid).size := by simpa
  obtain ⟨result, rightWrite, rightFrame, finalValid, finalRelated⟩ :=
    middleRelated.writeElementRaw_targetFrame middleValid right leftValue leftWord
      rightValidMiddle (leftRelated.witnessExtension (RefinementWitness.Extends.refl witness))
  have operation :
      swapResidentArrayElementsRaw state address left right = .ok result := by
    unfold swapResidentArrayElementsRaw
    rw [leftRead, rightRead]
    simp only [Bind.bind, Except.bind]
    rw [leftWrite]
    simp only
    exact rightWrite
  have arrayEq :
      (elements.set left rightValue leftValid).set right leftValue
          rightValidMiddle = elements.swap left right leftValid rightValid := by
    rfl
  refine ⟨result, operation, leftFrame.trans rightFrame, finalValid, ?_⟩
  simpa [arrayEq] using finalRelated

/-- Whole-heap refinement for ownership-neutral resident Array swap. The
semantic cell changes by `Array.swap`; reference counts are unchanged because
the operation only permutes already-owned children. -/
theorem LiveHeapRel.swapResidentArrayElementsRaw_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {elements : Array Value} {capacity : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .array elements capacity)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.array capacity))
    (left right : Nat) (leftValid : left < elements.size)
    (rightValid : right < elements.size) :
    ∃ result nextRuntime,
      swapResidentArrayElementsRaw state address left right = .ok result ∧
      setCell runtime location
          { cell with
            object := .array
              (elements.swap left right leftValid rightValid) capacity } =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness ∧
      result.heapCursor = state.heapCursor := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let replacement : HeapCell := {
    cell with
    object := .array (elements.swap left right leftValid rightValid) capacity }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive => rw [objectEq] at storedObjectEq; contradiction
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent limbsFit
      decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | integer descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq; contradiction
  | array descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have objectParts := HeapObject.array.inj storedObjectEq
      cases objectParts.1
      cases objectParts.2
      obtain ⟨result, operation, targetFrame, finalValid, objectAfter⟩ :=
        objectRelated.swapElementsRaw_targetFrame related.frontier left right
          leftValid rightValid
      obtain ⟨_, targetRawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _
          objectRelated.headerRead
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.array descriptor (by rfl)
          (by simpa [replacement] using objectAfter)
        · simpa [replacement] using refCount
        · simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          targetFrame finalValid targetAfter
      have capacityTransport :=
        related.mappedHeaderCapacity_of_targetMutation descriptor targetRawRead
          targetFrame
      exact ⟨result, nextRuntime, operation, by
          simpa [replacement] using semanticSet,
        heapRelated, capacityTransport, targetFrame.cursor⟩
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

end Fir.Wasm.Concrete
