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

end Fir.Wasm.Concrete
