import Fir.Wasm.Concrete.PayloadMutationFrameCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Successful checked object-field decoding exposes the canonical zero high
word that a narrow wasm32 replacement must preserve. -/
private theorem readObjectField_padding_of_eq_ok
    {state : MemoryState} {object : Word32} {index : Nat} {header : Header}
    {value : Word32}
    (headerRead : readConstructorHeader state object = .ok header)
    (indexValid : index < header.aux1.toNat)
    (read : readObjectField state object index = .ok value) :
    state.memory.readUInt32
        (object.value + headerBytes + target.semanticSlotBytes * index + 4) =
      .ok 0 := by
  unfold readObjectField at read
  rw [headerRead] at read
  simp only [Bind.bind, Except.bind] at read
  rw [if_pos indexValid] at read
  cases wordRead : state.memory.readWord32
      (object.value + headerBytes + target.semanticSlotBytes * index) with
  | error failure => simp [liftMemory, wordRead] at read
  | ok word =>
      simp only [liftMemory, wordRead] at read
      cases paddingRead : state.memory.readUInt32
          (object.value + headerBytes + target.semanticSlotBytes * index + 4) with
      | error failure => simp [paddingRead] at read
      | ok padding =>
          simp only [paddingRead] at read
          by_cases zero : padding = 0
          · subst padding
            rfl
          · simp [zero] at read

/-- One checked wasm32 object-slot replacement preserves the complete local
constructor decoder and provides the generic allocation frame used by the
whole-heap refinement. -/
theorem ConstructorObjectRel.writeObjectField_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (valid : state.FrontierInvariant)
    (index : Nat) (kind : AbiKind) (value : Value) (word : Word32)
    (indexValid : index < semantic.objectFields.size)
    (kindAt : fieldKinds[index]? = some kind)
    (valueRelated : ValueRel witness kind (.word32 word) value) :
    ∃ result,
      writeObjectField state address index word = .ok result ∧
      state.TargetMutationFrame result address
        (ConstructorLayout.ofInfo info).allocationBytes ∧
      result.FrontierInvariant ∧
      ConstructorObjectRel result witness address info fieldKinds
        { semantic with
          objectFields := semantic.objectFields.set index value indexValid } := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  have infoIndexValid : index < info.size := by
    rw [← related.semanticObjectFields]
    exact indexValid
  let oldValue := semantic.objectFields[index]
  have oldValueAt : semantic.objectFields[index]? = some oldValue :=
    Array.getElem?_eq_getElem indexValid
  obtain ⟨oldWord, oldRead, _⟩ :=
    related.objectFields index kind oldValue kindAt oldValueAt
  have constructorHeaderBefore : readConstructorHeader state address = .ok header :=
    readConstructorHeader_eq_ok_of_readLiveHeader state address header headerRead
      headerKind
  let offset := objectFieldAddress address.value index
  have writeInBounds : offset + 3 < state.memory.size := by
    have layoutInMemory :
        address.value + (ConstructorLayout.ofInfo info).allocationBytes ≤
          state.memory.size :=
      Nat.le_trans related.extent valid.cursorInBounds
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [ConstructorLayout.ofInfo, target] at layoutInMemory layoutBound
    simp [offset, objectFieldAddress, target]
    omega
  obtain ⟨memory, written, memorySize, _, _, _, _, byteFrame⟩ :=
    LinearMemory.writeUInt32_spec state.memory offset (UInt32.ofNat word.value)
      writeInBounds
  have wordWritten : state.memory.writeWord32 offset word = .ok memory := by
    exact written
  let result : MemoryState := { state with memory }
  have operation : writeObjectField state address index word = .ok result := by
    unfold writeObjectField
    rw [oldRead]
    simp only [Bind.bind, Except.bind]
    change (do
      let nextMemory ← liftMemory (state.memory.writeWord32 offset word)
      return ({ state with memory := nextMemory } : MemoryState)) = .ok result
    rw [wordWritten]
    rfl
  have afterHeader : address.value + headerBytes ≤ offset := by
    simp [offset, objectFieldAddress, target]
  have insideTarget :
      offset + 4 ≤ address.value + (ConstructorLayout.ofInfo info).allocationBytes := by
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [offset, objectFieldAddress, ConstructorLayout.ofInfo, target] at aligned ⊢
    omega
  have targetFrame : state.TargetMutationFrame result address
      (ConstructorLayout.ofInfo info).allocationBytes :=
    MemoryState.TargetMutationFrame.ofWriteUInt32 rfl writeInBounds written
      afterHeader insideTarget
  have finalValid : result.FrontierInvariant :=
    valid.writeUInt32 (by
      exact Nat.le_trans insideTarget related.extent) written
  have headerAfter : result.readLiveHeader address = .ok header := by
    rw [targetFrame.targetLiveHeader]
    exact headerRead
  have constructorHeaderAfter : readConstructorHeader result address = .ok header :=
    readConstructorHeader_eq_ok_of_readLiveHeader result address header headerAfter
      headerKind
  have byteReadFrame (other : Nat)
      (separated : offset + 3 < other ∨ other < offset) :
      memory.readByte other = state.memory.readByte other := by
    exact byteFrame other (by omega) (by omega) (by omega) (by omega)
  have readUInt16Frame (other : Nat)
      (separated : offset + 3 < other ∨ other + 1 < offset) :
      memory.readUInt16 other = state.memory.readUInt16 other := by
    unfold LinearMemory.readUInt16
    rw [byteReadFrame other (by omega)]
    rw [byteReadFrame (other + 1) (by omega)]
  have readUInt32Frame (other : Nat)
      (separated : offset + 3 < other ∨ other + 3 < offset) :
      memory.readUInt32 other = state.memory.readUInt32 other :=
    LinearMemory.readUInt32_of_writeUInt32_eq_ok_other state.memory memory offset
      other (UInt32.ofNat word.value) writeInBounds written separated
  have readUInt64Frame (other : Nat)
      (separated : offset + 3 < other ∨ other + 7 < offset) :
      memory.readUInt64 other = state.memory.readUInt64 other := by
    unfold LinearMemory.readUInt64
    rw [readUInt32Frame other (by omega)]
    rw [readUInt32Frame (other + 4) (by omega)]
  have readWord32Frame (other : Nat)
      (separated : offset + 3 < other ∨ other + 3 < offset) :
      memory.readWord32 other = state.memory.readWord32 other := by
    unfold LinearMemory.readWord32
    rw [readUInt32Frame other separated]
  have paddingBefore := readObjectField_padding_of_eq_ok constructorHeaderBefore
    (by simpa [objectCount] using infoIndexValid) oldRead
  have targetRead : readObjectField result address index = .ok word := by
    have lowRead : memory.readWord32 offset = .ok word :=
      LinearMemory.readWord32_of_writeWord32_eq_ok state.memory memory offset word
        writeInBounds wordWritten
    have paddingAfter : memory.readUInt32 (offset + 4) = .ok 0 := by
      rw [readUInt32Frame (offset + 4) (by omega)]
      simpa [offset, objectFieldAddress] using paddingBefore
    unfold readObjectField
    rw [constructorHeaderAfter]
    simp only [Bind.bind, Except.bind]
    rw [objectCount, if_pos infoIndexValid]
    change (do
      let field ← liftMemory (memory.readWord32 offset)
      let padding ← liftMemory (memory.readUInt32 (offset + 4))
      if padding == 0 then pure field
      else throw (ConcreteError.target
        (.nonzeroPadding (offset + 4) padding.toNat))) = .ok word
    rw [lowRead, paddingAfter]
    rfl
  have objectFieldFrame (other : Nat) (otherValid : other < info.size)
      (different : other ≠ index) :
      readObjectField result address other = readObjectField state address other := by
    dsimp [result]
    unfold readObjectField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    simp only [objectCount, if_pos otherValid]
    have separated :
        offset + 3 < objectFieldAddress address.value other ∨
          objectFieldAddress address.value other + 3 < offset := by
      simp [offset, objectFieldAddress, target]
      omega
    have paddingSeparated :
        offset + 3 < objectFieldAddress address.value other + 4 ∨
          objectFieldAddress address.value other + 4 + 3 < offset := by
      simp [offset, objectFieldAddress, target]
      omega
    have lowFrame : memory.readUInt32
        (address.value + headerBytes + target.semanticSlotBytes * other) =
      state.memory.readUInt32
        (address.value + headerBytes + target.semanticSlotBytes * other) := by
      simpa [objectFieldAddress] using
        readUInt32Frame (objectFieldAddress address.value other) separated
    have paddingFrame : memory.readUInt32
        (address.value + headerBytes + target.semanticSlotBytes * other + 4) =
      state.memory.readUInt32
        (address.value + headerBytes + target.semanticSlotBytes * other + 4) := by
      simpa [objectFieldAddress] using
        readUInt32Frame (objectFieldAddress address.value other + 4)
          paddingSeparated
    unfold LinearMemory.readWord32
    rw [lowFrame, paddingFrame]
  have usizeFieldFrame (other : Nat) (otherValid : other < info.usize) :
      readUSizeField result address other = readUSizeField state address other := by
    dsimp [result]
    unfold readUSizeField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    simp only [objectCount, usizeCount, if_pos otherValid]
    rw [readUInt64Frame
      (address.value + headerBytes + target.semanticSlotBytes * (info.size + other))
      (by simp [offset, objectFieldAddress, target]; omega)]
  have scalarFieldsAfter : ∀ field, field ∈ semantic.scalarFields →
      match field.value with
      | .uint8 scalar =>
          field.width = info.size + info.usize ∧
          field.offset + 1 ≤ info.ssize ∧
          readScalarUInt8Field result address field.width field.offset = .ok scalar
      | .uint16 scalar =>
          field.width = info.size + info.usize ∧
          field.offset + 2 ≤ info.ssize ∧
          readScalarUInt16Field result address field.width field.offset = .ok scalar
      | .uint32 scalar =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field result address field.width field.offset = .ok scalar
      | .uint64 scalar =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field result address field.width field.offset = .ok scalar
      | .float32Bits bits =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field result address field.width field.offset = .ok bits
      | .float64Bits bits =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field result address field.width field.offset = .ok bits := by
    intro field member
    have beforeField := related.semanticScalarFields field member
    cases valueEq : field.value with
    | uint8 scalar =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        unfold readScalarUInt8Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind] at readBefore ⊢
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 1 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        rw [scalarAddress] at readBefore ⊢
        change liftMemory (memory.readByte _) = .ok scalar
        rw [byteReadFrame _ (by
          rw [widthEq]
          simp [offset, objectFieldAddress, target]
          omega)]
        exact readBefore
    | uint16 scalar =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        unfold readScalarUInt16Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind] at readBefore ⊢
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 2 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        rw [scalarAddress] at readBefore ⊢
        change liftMemory (memory.readUInt16 _) = .ok scalar
        rw [readUInt16Frame _ (by
          rw [widthEq]
          simp [offset, objectFieldAddress, target]
          omega)]
        exact readBefore
    | uint32 scalar =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        unfold readScalarUInt32Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind] at readBefore ⊢
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 4 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        rw [scalarAddress] at readBefore ⊢
        change liftMemory (memory.readUInt32 _) = .ok scalar
        rw [readUInt32Frame _ (by
          left
          rw [widthEq]
          simp [offset, objectFieldAddress, target]
          omega)]
        exact readBefore
    | uint64 scalar =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        unfold readScalarUInt64Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind] at readBefore ⊢
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 8 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        rw [scalarAddress] at readBefore ⊢
        change liftMemory (memory.readUInt64 _) = .ok scalar
        rw [readUInt64Frame _ (by
          left
          rw [widthEq]
          simp [offset, objectFieldAddress, target]
          omega)]
        exact readBefore
    | float32Bits bits =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        unfold readScalarUInt32Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind] at readBefore ⊢
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 4 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        rw [scalarAddress] at readBefore ⊢
        change liftMemory (memory.readUInt32 _) = .ok bits
        rw [readUInt32Frame _ (by
          left
          rw [widthEq]
          simp [offset, objectFieldAddress, target]
          omega)]
        exact readBefore
    | float64Bits bits =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        unfold readScalarUInt64Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind] at readBefore ⊢
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 8 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        rw [scalarAddress] at readBefore ⊢
        change liftMemory (memory.readUInt64 _) = .ok bits
        rw [readUInt64Frame _ (by
          left
          rw [widthEq]
          simp [offset, objectFieldAddress, target]
          omega)]
        exact readBefore
  refine ⟨result, operation, targetFrame, finalValid, ?_⟩
  refine {
    header := ⟨header, headerAfter, headerKind, allocationBytes,
      tag, objectCount, usizeCount, scalarCount⟩
    headerOwned := related.headerOwned
    extent := related.extent
    semanticObjectFields := by simp [related.semanticObjectFields]
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := scalarFieldsAfter
    fieldKindsSize := related.fieldKindsSize
    fieldKindsValid := related.fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · intro other otherKind semanticValue otherKindAt valueAt
    by_cases same : other = index
    · subst other
      have kindEq : otherKind = kind := by
        rw [kindAt] at otherKindAt
        exact (Option.some.inj otherKindAt).symm
      subst otherKind
      have valueEq : semanticValue = value := by
        rw [Array.getElem?_set_self indexValid] at valueAt
        exact (Option.some.inj valueAt).symm
      subst semanticValue
      exact ⟨word, targetRead, valueRelated⟩
    · have oldValueAt : semantic.objectFields[other]? = some semanticValue := by
        rw [Array.getElem?_set_ne indexValid (Ne.symm same)] at valueAt
        exact valueAt
      have otherValid : other < info.size := by
        obtain ⟨otherLt, _⟩ := Array.getElem?_eq_some_iff.mp oldValueAt
        rw [related.semanticObjectFields] at otherLt
        exact otherLt
      obtain ⟨otherWord, readBefore, otherRelated⟩ :=
        related.objectFields other otherKind semanticValue otherKindAt oldValueAt
      exact ⟨otherWord, by rw [objectFieldFrame other otherValid same]; exact readBefore,
        otherRelated⟩
  · intro other usize valueAt
    have otherValid : other < info.usize := by
      obtain ⟨otherLt, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
      rw [related.semanticUSizeFields] at otherLt
      exact otherLt
    rw [usizeFieldFrame other otherValid]
    exact related.usizeFields other usize valueAt

/-- Complete-heap refinement for successful one-field object mutation,
including preservation of every mapped allocation's physical extent. -/
theorem LiveHeapRel.writeObjectField_refines_with_capacity
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (index : Nat) (kind : AbiKind) (value : Value) (word : Word32)
    (indexValid : index < semantic.objectFields.size)
    (kindAt : fieldKinds[index]? = some kind)
    (valueRelated : ValueRel witness kind (.word32 word) value) :
    ∃ result nextRuntime,
      writeObjectField state address index word = .ok result ∧
      Fir.LeanIR.Impure.setObjectField runtime (.object (.heap location)) index value =
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
  let updatedSemantic : ConstructorObject := {
    semantic with objectFields := semantic.objectFields.set index value indexValid }
  let replacement : HeapCell := { cell with object := .ctor updatedSemantic }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      obtain ⟨result, operation, targetFrame, finalValid, objectAfter⟩ :=
        objectRelated.writeObjectField_targetFrame related.frontier index kind value
          word indexValid kindAt valueRelated
      obtain ⟨objectHeader, objectHeaderRead, _, retainedCapacity, _, _, _, _⟩ :=
        objectRelated.header
      rw [headerRead] at objectHeaderRead
      have objectHeaderEq := Except.ok.inj objectHeaderRead
      subst objectHeader
      obtain ⟨_, targetRawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead
      have physicalFrame := targetFrame.widen retainedCapacity
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.constructor descriptor (by rfl)
          (by simpa [updatedSemantic] using objectAfter)
          (by rw [targetFrame.targetLiveHeader]; exact headerRead) headerKind
        · simpa [replacement] using refCount
        · simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          physicalFrame finalValid targetAfter
      have sourceOperation :
          Fir.LeanIR.Impure.setObjectField runtime (.object (.heap location)) index
            value = .ok nextRuntime := by
        simp [Fir.LeanIR.Impure.setObjectField, modifyConstructor, getConstructor,
          getLiveCell, Bind.bind, Except.bind, found, live, objectEq]
        simp only [pure, Except.pure]
        rw [dif_pos indexValid]
        change setCell runtime location replacement = .ok nextRuntime
        exact semanticSet
      have capacity :=
        related.mappedHeaderCapacity_of_targetMutation descriptor targetRawRead
          physicalFrame
      exact ⟨result, nextRuntime, operation, sourceOperation, heapRelated,
        capacity, targetFrame.cursor⟩
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | integer descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | array descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

theorem LiveHeapRel.writeObjectField_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (index : Nat) (kind : AbiKind) (value : Value) (word : Word32)
    (indexValid : index < semantic.objectFields.size)
    (kindAt : fieldKinds[index]? = some kind)
    (valueRelated : ValueRel witness kind (.word32 word) value) :
    ∃ result nextRuntime,
      writeObjectField state address index word = .ok result ∧
      Fir.LeanIR.Impure.setObjectField runtime (.object (.heap location)) index value =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, nextRuntime, concrete, semanticOperation, finalRelated, _, _⟩ :=
    related.writeObjectField_refines_with_capacity mapped found live objectEq
      descriptorFound index kind value word indexValid kindAt valueRelated
  exact ⟨result, nextRuntime, concrete, semanticOperation, finalRelated⟩

end Fir.Wasm.Concrete
