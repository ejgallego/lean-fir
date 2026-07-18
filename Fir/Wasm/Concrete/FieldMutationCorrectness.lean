import Fir.Wasm.Concrete.TagMutationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- A checked `USize` slot replacement preserves the decoded constructor
relation and changes exactly the selected semantic field. -/
theorem ConstructorObjectRel.writeUSizeField
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (index : Nat) (value : UInt64) (indexValid : index < info.usize) :
    ∃ result,
      Fir.Wasm.Concrete.writeUSizeField state address index value = .ok result ∧
      ConstructorObjectRel result witness address info fieldKinds
        { semantic with
          usizeFields := semantic.usizeFields.set index value (by
            rw [related.semanticUSizeFields]
            exact indexValid) } := by
  obtain ⟨header, headerRead, headerKind, allocationBytes, persistent,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header
  obtain ⟨heap, decodedBefore, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * (header.aux1.toNat + index)
  have offsetEq : offset = address.value + headerBytes +
      target.semanticSlotBytes * (info.size + index) := by
    simp [offset, objectCount]
  have writeInBounds : offset + 7 < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    rw [allocationBytes] at extentInMemory
    rw [offsetEq]
    simp [ConstructorLayout.ofInfo, target] at extentInMemory layoutBound ⊢
    omega
  obtain ⟨middle, lowWrite, middleSize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec state.memory offset value.toUInt32 (by omega)
  obtain ⟨memory, highWrite, memorySize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec middle (offset + 4)
      (value >>> (32 : UInt64)).toUInt32 (by omega)
  have fieldWrite : state.memory.writeUInt64 offset value = .ok memory := by
    unfold LinearMemory.writeUInt64
    rw [lowWrite]
    change middle.writeUInt32 (offset + 4) (value >>> (32 : UInt64)).toUInt32 =
      .ok memory
    exact highWrite
  have finalSize : memory.size = state.memory.size := memorySize.trans middleSize
  let result : MemoryState := { state with memory }
  have operation : Fir.Wasm.Concrete.writeUSizeField state address index value =
      .ok result := by
    unfold Fir.Wasm.Concrete.writeUSizeField
    rw [constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    simp [indexValid, usizeCount, objectCount]
    rw [← offsetEq]
    change (do
      let memory ← liftMemory (state.memory.writeUInt64 offset value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [fieldWrite]
    rfl
  have readUInt32Frame (other : Nat)
      (disjoint : offset + 7 < other ∨ other + 3 < offset) :
      memory.readUInt32 other = state.memory.readUInt32 other :=
    LinearMemory.readUInt32_of_writeUInt64_eq_ok_other state.memory memory offset other
      value writeInBounds fieldWrite disjoint
  have readByteFrame (other : Nat) (afterField : offset + 7 < other) :
      memory.readByte other = state.memory.readByte other := by
    rw [LinearMemory.readByte_of_writeUInt32_eq_ok middle memory (offset + 4)
      (value >>> (32 : UInt64)).toUInt32 (by omega) highWrite other
      (by omega) (by omega) (by omega) (by omega)]
    rw [LinearMemory.readByte_of_writeUInt32_eq_ok state.memory middle offset
      value.toUInt32 (by omega) lowWrite other
      (by omega) (by omega) (by omega) (by omega)]
  have readUInt16Frame (other : Nat) (afterField : offset + 7 < other) :
      memory.readUInt16 other = state.memory.readUInt16 other := by
    unfold LinearMemory.readUInt16
    rw [readByteFrame other afterField]
    rw [readByteFrame (other + 1) (by omega)]
  have decodedAfter : Header.read memory address = .ok header := by
    unfold Header.read at decodedBefore ⊢
    dsimp only at decodedBefore ⊢
    rw [readUInt32Frame (address.value + headerKindOffset) (by
      simp [offset, headerKindOffset, headerBytes, target]; omega)]
    rw [readUInt32Frame (address.value + headerFlagsOffset) (by
      simp [offset, headerFlagsOffset, headerBytes, target]; omega)]
    rw [readUInt32Frame (address.value + headerRefCountOffset) (by
      simp [offset, headerRefCountOffset, headerBytes, target]; omega)]
    rw [readUInt32Frame (address.value + headerAllocationBytesOffset) (by
      simp [offset, headerAllocationBytesOffset, headerBytes, target]; omega)]
    rw [readUInt32Frame (address.value + headerAux0Offset) (by
      simp [offset, headerAux0Offset, headerBytes, target]; omega)]
    rw [readUInt32Frame (address.value + headerAux1Offset) (by
      simp [offset, headerAux1Offset, headerBytes, target]; omega)]
    rw [readUInt32Frame (address.value + headerAux2Offset) (by
      simp [offset, headerAux2Offset, headerBytes, target]; omega)]
    rw [readUInt32Frame (address.value + headerAux3Offset) (by
      simp [offset, headerAux3Offset, headerBytes, target]; omega)]
    exact decodedBefore
  have headerReadAfter : result.readLiveHeader address = .ok header := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedAfter]
    simp only [Bind.bind, Except.bind]
    simp [live, minimum, aligned, finalSize, extentInMemory]
    rfl
  have constructorHeaderAfter : readConstructorHeader result address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerReadAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have readWord32Frame (other : Nat) (beforeField : other + 3 < offset) :
      memory.readWord32 other = state.memory.readWord32 other := by
    unfold LinearMemory.readWord32
    rw [readUInt32Frame other (.inr beforeField)]
  have objectFieldFrame (fieldIndex : Nat) (fieldValid : fieldIndex < info.size) :
      readObjectField result address fieldIndex =
        readObjectField state address fieldIndex := by
    unfold readObjectField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    rw [objectCount]
    simp [fieldValid]
    rw [readWord32Frame
      (address.value + headerBytes + target.semanticSlotBytes * fieldIndex) (by
        simp [offset, target]
        omega)]
    rw [readUInt32Frame
      (address.value + headerBytes + target.semanticSlotBytes * fieldIndex + 4) (by
        simp [offset, target]
        omega)]
  have readUInt64Frame (other : Nat)
      (disjoint : offset + 7 < other ∨ other + 7 < offset) :
      memory.readUInt64 other = state.memory.readUInt64 other := by
    unfold LinearMemory.readUInt64
    rw [readUInt32Frame other (by omega)]
    rw [readUInt32Frame (other + 4) (by omega)]
  have usizeFieldSame : readUSizeField result address index = .ok value := by
    unfold readUSizeField
    rw [constructorHeaderAfter]
    simp only [Bind.bind, Except.bind]
    simp [indexValid, usizeCount, objectCount]
    rw [← offsetEq]
    change liftMemory (memory.readUInt64 offset) = .ok value
    rw [LinearMemory.readUInt64_of_writeUInt64_eq_ok state.memory memory offset value
      writeInBounds fieldWrite]
    rfl
  have usizeFieldFrame (other : Nat) (otherValid : other < info.usize)
      (different : other ≠ index) :
      readUSizeField result address other = readUSizeField state address other := by
    unfold readUSizeField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    rw [usizeCount, objectCount]
    simp [otherValid]
    rw [readUInt64Frame
      (address.value + headerBytes + target.semanticSlotBytes * (info.size + other)) (by
        rw [offsetEq]
        simp [target]
        omega)]
  refine ⟨result, operation, ?_⟩
  refine {
    header := ⟨header, headerReadAfter, headerKind, allocationBytes,
      persistent, tag, objectCount, usizeCount, scalarCount⟩
    headerOwned := related.headerOwned
    extent := related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := by simp [related.semanticUSizeFields]
    semanticScalarFields := ?_
    fieldKindsSize := related.fieldKindsSize
    objectFields := ?_
    usizeFields := ?_ }
  · intro field member
    have beforeField := related.semanticScalarFields field member
    cases valueEq : field.value with
    | uint8 scalar =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 1 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        unfold readScalarUInt8Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        simp only [Bind.bind, Except.bind] at readBefore
        rw [scalarAddress] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind]
        rw [scalarAddress]
        change liftMemory (memory.readByte _) = .ok scalar
        rw [readByteFrame _ (by
          rw [offsetEq, widthEq]
          simp [target]
          omega)]
        exact readBefore
    | uint16 scalar =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 2 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        unfold readScalarUInt16Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        simp only [Bind.bind, Except.bind] at readBefore
        rw [scalarAddress] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind]
        rw [scalarAddress]
        change liftMemory (memory.readUInt16 _) = .ok scalar
        rw [readUInt16Frame _ (by
          rw [offsetEq, widthEq]
          simp [target]
          omega)]
        exact readBefore
    | uint32 scalar =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 4 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        unfold readScalarUInt32Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        simp only [Bind.bind, Except.bind] at readBefore
        rw [scalarAddress] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind]
        rw [scalarAddress]
        change liftMemory (memory.readUInt32 _) = .ok scalar
        rw [readUInt32Frame _ (by
          left
          rw [offsetEq, widthEq]
          simp [target]
          omega)]
        exact readBefore
    | uint64 scalar =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have scalarAddress : scalarFieldAddress address header field.width
            field.offset 8 = .ok (address.value + headerBytes +
              target.semanticSlotBytes * field.width + field.offset) := by
          unfold scalarFieldAddress
          simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
          rfl
        unfold readScalarUInt64Field at readBefore ⊢
        rw [constructorHeaderBefore] at readBefore
        simp only [Bind.bind, Except.bind] at readBefore
        rw [scalarAddress] at readBefore
        rw [constructorHeaderAfter]
        simp only [Bind.bind, Except.bind]
        rw [scalarAddress]
        change liftMemory (memory.readUInt64 _) = .ok scalar
        rw [readUInt64Frame _ (by
          left
          rw [offsetEq, widthEq]
          simp [target]
          omega)]
        exact readBefore
  · intro fieldIndex kind semanticValue kindAt valueAt
    change semantic.objectFields[fieldIndex]? = some semanticValue at valueAt
    have fieldValid : fieldIndex < info.size := by
      obtain ⟨_, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
      rw [related.semanticObjectFields] at *
      omega
    obtain ⟨word, readBefore, valueRelated⟩ :=
      related.objectFields fieldIndex kind semanticValue kindAt valueAt
    exact ⟨word, by rw [objectFieldFrame fieldIndex fieldValid]; exact readBefore,
      valueRelated⟩
  · intro other semanticValue valueAt
    have semanticIndexValid : index < semantic.usizeFields.size := by
      rw [related.semanticUSizeFields]
      exact indexValid
    by_cases same : other = index
    · subst other
      have valueEq : semanticValue = value := by
        rw [Array.getElem?_set_self semanticIndexValid] at valueAt
        exact (Option.some.inj valueAt).symm
      subst semanticValue
      exact usizeFieldSame
    · have oldValueAt : semantic.usizeFields[other]? = some semanticValue := by
        rw [Array.getElem?_set_ne semanticIndexValid (Ne.symm same)] at valueAt
        exact valueAt
      have otherValid : other < info.usize := by
        obtain ⟨_, _⟩ := Array.getElem?_eq_some_iff.mp oldValueAt
        rw [related.semanticUSizeFields] at *
        omega
      rw [usizeFieldFrame other otherValid same]
      exact related.usizeFields other semanticValue oldValueAt

end Fir.Wasm.Concrete
