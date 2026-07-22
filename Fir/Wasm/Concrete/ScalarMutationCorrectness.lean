import Fir.Wasm.Concrete.FieldMutationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- A sequence of earlier writes to exactly one packed coordinate is fully
removed by the source runtime's replacement filter. This is the reusable
premise for repeated concrete writes at that coordinate. -/
theorem scalarFields_filter_same_coordinate
    (fields : List ScalarField) (slotIndex byteOffset : Nat)
    (same : ∀ field ∈ fields,
      field.width = slotIndex ∧ field.offset = byteOffset) :
    fields.filter (fun old =>
      old.width != slotIndex || old.offset != byteOffset) = [] := by
  induction fields with
  | nil => rfl
  | cons field fields induction =>
      have head := same field (by simp)
      have tail : ∀ old ∈ fields,
          old.width = slotIndex ∧ old.offset = byteOffset := by
        intro old member
        exact same old (by simp [member])
      simp [head.1, head.2, induction tail]

/-- Concrete byte width of one semantic packed scalar. -/
def scalarValueByteSize : ScalarValue → Nat
  | .uint8 _ => 1
  | .uint16 _ => 2
  | .uint32 _ => 4
  | .uint64 _ => 8

/-- If every earlier write names the replaced coordinate, the retained-field
disjointness premise is vacuous. -/
theorem scalarFields_retainedDisjoint_same_coordinate
    (fields : List ScalarField) (slotIndex byteOffset bytes : Nat)
    (same : ∀ field ∈ fields,
      field.width = slotIndex ∧ field.offset = byteOffset) :
    ∀ field ∈ fields,
      field.width ≠ slotIndex ∨ field.offset ≠ byteOffset →
      field.offset + scalarValueByteSize field.value ≤ byteOffset ∨
        byteOffset + bytes ≤ field.offset := by
  intro field member different
  have coordinate := same field member
  rcases different with widthNe | offsetNe
  · exact (widthNe coordinate.1).elim
  · exact (offsetNe coordinate.2).elim

/-- A compiler-shaped packed `UInt64` replacement reads back exactly and
frames every previously implemented constructor observation. -/
theorem ConstructorObjectRel.writeScalarUInt64Field
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (slotIndex byteOffset : Nat) (value : UInt64)
    (retainedDisjoint : ∀ field ∈ semantic.scalarFields,
      field.width ≠ slotIndex ∨ field.offset ≠ byteOffset →
      field.offset + scalarValueByteSize field.value ≤ byteOffset ∨
        byteOffset + 8 ≤ field.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 8 ≤ info.ssize) :
    ∃ result,
      Fir.Wasm.Concrete.writeScalarUInt64Field state address slotIndex byteOffset value =
        .ok result ∧
      readScalarUInt64Field result address slotIndex byteOffset = .ok value ∧
      readTag result address = readTag state address ∧
      (∀ index, readObjectField result address index =
        readObjectField state address index) ∧
      (∀ index, readUSizeField result address index =
        readUSizeField state address index) ∧
      ConstructorObjectRel result witness address info fieldKinds
        { semantic with
          scalarFields := {
            width := slotIndex
            offset := byteOffset
            value := .uint64 value } :: semantic.scalarFields.filter fun old =>
              old.width != slotIndex || old.offset != byteOffset } := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, decodedBefore, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * slotIndex + byteOffset
  have writeInBounds : offset + 7 < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    have layoutInMemory :
        address.value + (ConstructorLayout.ofInfo info).allocationBytes ≤
          state.memory.size :=
      Nat.le_trans (Nat.add_le_add_left allocationBytes address.value)
        extentInMemory
    simp [ConstructorLayout.ofInfo, target] at layoutInMemory
    simp [target] at layoutBound
    dsimp [offset]
    rw [slotIndexEq]
    simp [target]
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
  have scalarAddress : scalarFieldAddress address header slotIndex byteOffset 8 =
      .ok offset := by
    unfold scalarFieldAddress
    simp [slotIndexEq, objectCount, usizeCount, fieldFits, scalarCount, offset]
    rfl
  have operation : Fir.Wasm.Concrete.writeScalarUInt64Field state address slotIndex
      byteOffset value = .ok result := by
    unfold Fir.Wasm.Concrete.writeScalarUInt64Field
    rw [constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    change (do
      let fieldAddress ← scalarFieldAddress address header slotIndex byteOffset 8
      let memory ← liftMemory (state.memory.writeUInt64 fieldAddress value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [scalarAddress]
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
  have scalarAddressAfter : scalarFieldAddress address header slotIndex byteOffset 8 =
      .ok offset := scalarAddress
  have readBack : readScalarUInt64Field result address slotIndex byteOffset =
      .ok value := by
    unfold readScalarUInt64Field
    rw [constructorHeaderAfter]
    simp only [Bind.bind, Except.bind]
    change (do
      let fieldAddress ← scalarFieldAddress address header slotIndex byteOffset 8
      liftMemory (memory.readUInt64 fieldAddress)) = .ok value
    rw [scalarAddressAfter]
    change liftMemory (memory.readUInt64 offset) = .ok value
    rw [LinearMemory.readUInt64_of_writeUInt64_eq_ok state.memory memory offset value
      writeInBounds fieldWrite]
    rfl
  have tagFrame : readTag result address = readTag state address := by
    unfold readTag
    simp [heap]
    rw [headerReadAfter, headerRead]
    simp only [liftMemory, Bind.bind, Except.bind]
    rw [headerKind]
    have constructorBranch :
        (ObjectKind.constructor == ObjectKind.constructor) = true := by decide
    simp only [if_pos constructorBranch]
  have readWord32Frame (other : Nat) (beforeField : other + 3 < offset) :
      memory.readWord32 other = state.memory.readWord32 other := by
    unfold LinearMemory.readWord32
    rw [readUInt32Frame other (.inr beforeField)]
  have objectFieldFrame (index : Nat) :
      readObjectField result address index = readObjectField state address index := by
    unfold readObjectField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    split <;> rename_i inBounds
    · rw [readWord32Frame
        (address.value + headerBytes + target.semanticSlotBytes * index) (by
          simp [offset, slotIndexEq, target]
          omega)]
      rw [readUInt32Frame
        (address.value + headerBytes + target.semanticSlotBytes * index + 4) (by
          right
          simp [offset, slotIndexEq, target]
          omega)]
    · rfl
  have readByteFrame (other : Nat)
      (disjoint : other < offset ∨ offset + 7 < other) :
      memory.readByte other = state.memory.readByte other :=
    LinearMemory.readByte_of_writeUInt64_eq_ok_other state.memory memory offset
      value writeInBounds fieldWrite other disjoint
  have readUInt16Frame (other : Nat)
      (disjoint : offset + 7 < other ∨ other + 1 < offset) :
      memory.readUInt16 other = state.memory.readUInt16 other := by
    unfold LinearMemory.readUInt16
    rw [readByteFrame other (by omega)]
    rw [readByteFrame (other + 1) (by omega)]
  have readUInt64Frame (other : Nat)
      (disjoint : offset + 7 < other ∨ other + 7 < offset) :
      memory.readUInt64 other = state.memory.readUInt64 other := by
    unfold LinearMemory.readUInt64
    rw [readUInt32Frame other (by omega)]
    rw [readUInt32Frame (other + 4) (by omega)]
  have usizeFieldFrame (index : Nat) :
      readUSizeField result address index = readUSizeField state address index := by
    unfold readUSizeField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    split <;> rename_i inBounds
    · rw [readUInt64Frame
        (address.value + headerBytes +
          target.semanticSlotBytes * (header.aux1.toNat + index)) (by
            right
            simp [offset, slotIndexEq, objectCount, target]
            omega)]
    · rfl
  have relationAfter : ConstructorObjectRel result witness address info fieldKinds
      { semantic with
        scalarFields := {
          width := slotIndex
          offset := byteOffset
          value := .uint64 value } :: semantic.scalarFields.filter fun old =>
            old.width != slotIndex || old.offset != byteOffset } := by
    refine {
      header := ⟨header, headerReadAfter, headerKind, allocationBytes,
        tag, objectCount, usizeCount, scalarCount⟩
      headerOwned := related.headerOwned
      extent := related.extent
      semanticObjectFields := related.semanticObjectFields
      semanticUSizeFields := related.semanticUSizeFields
      semanticScalarFields := ?_
      fieldKindsSize := related.fieldKindsSize
      fieldKindsValid := related.fieldKindsValid
      objectFields := ?_
      usizeFields := ?_ }
    · intro field member
      simp only [List.mem_cons, List.mem_filter] at member
      rcases member with fieldEq | ⟨oldMember, retained⟩
      · subst field
        exact ⟨slotIndexEq, fieldFits, readBack⟩
      · have different :
            field.width ≠ slotIndex ∨ field.offset ≠ byteOffset := by
          simpa using retained
        have separated := retainedDisjoint field oldMember different
        have oldRelated := related.semanticScalarFields field oldMember
        let other := address.value + headerBytes +
          target.semanticSlotBytes * field.width + field.offset
        cases valueEq : field.value with
        | uint8 oldValue =>
            have oldRelated' := oldRelated
            simp only [valueEq] at oldRelated'
            simp only [valueEq, scalarValueByteSize] at separated
            obtain ⟨oldWidth, oldFits, oldRead⟩ := oldRelated'
            have oldAddress : scalarFieldAddress address header field.width
                field.offset 1 = .ok other := by
              unfold scalarFieldAddress
              simp [oldWidth, objectCount, usizeCount, oldFits, scalarCount,
                other]
              rfl
            have physicalDisjoint : other < offset ∨ offset + 7 < other := by
              rcases separated with before | after
              · left
                simp [other, offset, oldWidth, slotIndexEq, target]
                omega
              · right
                simp [other, offset, oldWidth, slotIndexEq, target]
                omega
            refine ⟨oldWidth, oldFits, ?_⟩
            calc
              readScalarUInt8Field result address field.width field.offset =
                  liftMemory (memory.readByte other) := by
                    unfold readScalarUInt8Field
                    rw [constructorHeaderAfter]
                    simp only [Bind.bind, Except.bind]
                    rw [oldAddress]
              _ = liftMemory (state.memory.readByte other) := by
                    rw [readByteFrame other physicalDisjoint]
              _ = readScalarUInt8Field state address field.width field.offset := by
                    unfold readScalarUInt8Field
                    rw [constructorHeaderBefore]
                    simp only [Bind.bind, Except.bind]
                    rw [oldAddress]
              _ = .ok oldValue := oldRead
        | uint16 oldValue =>
            have oldRelated' := oldRelated
            simp only [valueEq] at oldRelated'
            simp only [valueEq, scalarValueByteSize] at separated
            obtain ⟨oldWidth, oldFits, oldRead⟩ := oldRelated'
            have oldAddress : scalarFieldAddress address header field.width
                field.offset 2 = .ok other := by
              unfold scalarFieldAddress
              simp [oldWidth, objectCount, usizeCount, oldFits, scalarCount,
                other]
              rfl
            have physicalDisjoint :
                offset + 7 < other ∨ other + 1 < offset := by
              rcases separated with before | after
              · right
                simp [other, offset, oldWidth, slotIndexEq, target]
                omega
              · left
                simp [other, offset, oldWidth, slotIndexEq, target]
                omega
            refine ⟨oldWidth, oldFits, ?_⟩
            calc
              readScalarUInt16Field result address field.width field.offset =
                  liftMemory (memory.readUInt16 other) := by
                    unfold readScalarUInt16Field
                    rw [constructorHeaderAfter]
                    simp only [Bind.bind, Except.bind]
                    rw [oldAddress]
              _ = liftMemory (state.memory.readUInt16 other) := by
                    rw [readUInt16Frame other physicalDisjoint]
              _ = readScalarUInt16Field state address field.width field.offset := by
                    unfold readScalarUInt16Field
                    rw [constructorHeaderBefore]
                    simp only [Bind.bind, Except.bind]
                    rw [oldAddress]
              _ = .ok oldValue := oldRead
        | uint32 oldValue =>
            have oldRelated' := oldRelated
            simp only [valueEq] at oldRelated'
            simp only [valueEq, scalarValueByteSize] at separated
            obtain ⟨oldWidth, oldFits, oldRead⟩ := oldRelated'
            have oldAddress : scalarFieldAddress address header field.width
                field.offset 4 = .ok other := by
              unfold scalarFieldAddress
              simp [oldWidth, objectCount, usizeCount, oldFits, scalarCount,
                other]
              rfl
            have physicalDisjoint :
                offset + 7 < other ∨ other + 3 < offset := by
              rcases separated with before | after
              · right
                simp [other, offset, oldWidth, slotIndexEq, target]
                omega
              · left
                simp [other, offset, oldWidth, slotIndexEq, target]
                omega
            refine ⟨oldWidth, oldFits, ?_⟩
            calc
              readScalarUInt32Field result address field.width field.offset =
                  liftMemory (memory.readUInt32 other) := by
                    unfold readScalarUInt32Field
                    rw [constructorHeaderAfter]
                    simp only [Bind.bind, Except.bind]
                    rw [oldAddress]
              _ = liftMemory (state.memory.readUInt32 other) := by
                    rw [readUInt32Frame other physicalDisjoint]
              _ = readScalarUInt32Field state address field.width field.offset := by
                    unfold readScalarUInt32Field
                    rw [constructorHeaderBefore]
                    simp only [Bind.bind, Except.bind]
                    rw [oldAddress]
              _ = .ok oldValue := oldRead
        | uint64 oldValue =>
            have oldRelated' := oldRelated
            simp only [valueEq] at oldRelated'
            simp only [valueEq, scalarValueByteSize] at separated
            obtain ⟨oldWidth, oldFits, oldRead⟩ := oldRelated'
            have oldAddress : scalarFieldAddress address header field.width
                field.offset 8 = .ok other := by
              unfold scalarFieldAddress
              simp [oldWidth, objectCount, usizeCount, oldFits, scalarCount,
                other]
              rfl
            have physicalDisjoint :
                offset + 7 < other ∨ other + 7 < offset := by
              rcases separated with before | after
              · right
                simp [other, offset, oldWidth, slotIndexEq, target]
                omega
              · left
                simp [other, offset, oldWidth, slotIndexEq, target]
                omega
            refine ⟨oldWidth, oldFits, ?_⟩
            calc
              readScalarUInt64Field result address field.width field.offset =
                  liftMemory (memory.readUInt64 other) := by
                    unfold readScalarUInt64Field
                    rw [constructorHeaderAfter]
                    simp only [Bind.bind, Except.bind]
                    rw [oldAddress]
              _ = liftMemory (state.memory.readUInt64 other) := by
                    rw [readUInt64Frame other physicalDisjoint]
              _ = readScalarUInt64Field state address field.width field.offset := by
                    unfold readScalarUInt64Field
                    rw [constructorHeaderBefore]
                    simp only [Bind.bind, Except.bind]
                    rw [oldAddress]
              _ = .ok oldValue := oldRead
    · intro index kind semanticValue kindAt valueAt
      change semantic.objectFields[index]? = some semanticValue at valueAt
      obtain ⟨word, readBefore, valueRelated⟩ :=
        related.objectFields index kind semanticValue kindAt valueAt
      exact ⟨word, by rw [objectFieldFrame]; exact readBefore, valueRelated⟩
    · intro index semanticValue valueAt
      change semantic.usizeFields[index]? = some semanticValue at valueAt
      rw [usizeFieldFrame]
      exact related.usizeFields index semanticValue valueAt
  exact ⟨result, operation, readBack, tagFrame, objectFieldFrame, usizeFieldFrame,
    relationAfter⟩

/-- The verified 32-bit lane replaces the corresponding semantic packed
coordinate and frames all earlier constructor regions. -/
theorem ConstructorObjectRel.writeScalarUInt32Field
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (slotIndex byteOffset : Nat) (value : UInt32)
    (replaced : semantic.scalarFields.filter (fun old =>
      old.width != slotIndex || old.offset != byteOffset) = [])
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 4 ≤ info.ssize) :
    ∃ result,
      Fir.Wasm.Concrete.writeScalarUInt32Field state address slotIndex byteOffset value =
        .ok result ∧
      readScalarUInt32Field result address slotIndex byteOffset = .ok value ∧
      readTag result address = readTag state address ∧
      (∀ index, readObjectField result address index =
        readObjectField state address index) ∧
      (∀ index, readUSizeField result address index =
        readUSizeField state address index) ∧
      ConstructorObjectRel result witness address info fieldKinds
        { semantic with
          scalarFields := {
            width := slotIndex
            offset := byteOffset
            value := .uint32 value } :: semantic.scalarFields.filter fun old =>
              old.width != slotIndex || old.offset != byteOffset } := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, decodedBefore, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * slotIndex + byteOffset
  have writeInBounds : offset + 3 < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    have layoutInMemory :
        address.value + (ConstructorLayout.ofInfo info).allocationBytes ≤
          state.memory.size :=
      Nat.le_trans (Nat.add_le_add_left allocationBytes address.value)
        extentInMemory
    simp [ConstructorLayout.ofInfo, target] at layoutInMemory
    simp [target] at layoutBound
    dsimp [offset]
    rw [slotIndexEq]
    simp [target]
    omega
  obtain ⟨memory, fieldWrite, memorySize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec state.memory offset value writeInBounds
  let result : MemoryState := { state with memory }
  have scalarAddress : scalarFieldAddress address header slotIndex byteOffset 4 =
      .ok offset := by
    unfold scalarFieldAddress
    simp [slotIndexEq, objectCount, usizeCount, fieldFits, scalarCount, offset]
    rfl
  have operation : Fir.Wasm.Concrete.writeScalarUInt32Field state address slotIndex
      byteOffset value = .ok result := by
    unfold Fir.Wasm.Concrete.writeScalarUInt32Field
    rw [constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    change (do
      let fieldAddress ← scalarFieldAddress address header slotIndex byteOffset 4
      let memory ← liftMemory (state.memory.writeUInt32 fieldAddress value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [scalarAddress]
    change (do
      let memory ← liftMemory (state.memory.writeUInt32 offset value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [fieldWrite]
    rfl
  have readUInt32Frame (other : Nat)
      (disjoint : offset + 3 < other ∨ other + 3 < offset) :
      memory.readUInt32 other = state.memory.readUInt32 other :=
    LinearMemory.readUInt32_of_writeUInt32_eq_ok_other state.memory memory offset other
      value writeInBounds fieldWrite disjoint
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
    simp [live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have constructorHeaderAfter : readConstructorHeader result address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerReadAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have readBack : readScalarUInt32Field result address slotIndex byteOffset =
      .ok value := by
    unfold readScalarUInt32Field
    rw [constructorHeaderAfter]
    simp only [Bind.bind, Except.bind]
    rw [scalarAddress]
    change liftMemory (memory.readUInt32 offset) = .ok value
    rw [LinearMemory.readUInt32_of_writeUInt32_eq_ok state.memory memory offset value
      writeInBounds fieldWrite]
    rfl
  have tagFrame : readTag result address = readTag state address := by
    unfold readTag
    simp [heap]
    rw [headerReadAfter, headerRead]
    simp only [liftMemory, Bind.bind, Except.bind]
    rw [headerKind]
    have constructorBranch :
        (ObjectKind.constructor == ObjectKind.constructor) = true := by decide
    simp only [if_pos constructorBranch]
  have readWord32Frame (other : Nat) (beforeField : other + 3 < offset) :
      memory.readWord32 other = state.memory.readWord32 other := by
    unfold LinearMemory.readWord32
    rw [readUInt32Frame other (.inr beforeField)]
  have objectFieldFrame (index : Nat) :
      readObjectField result address index = readObjectField state address index := by
    unfold readObjectField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    split <;> rename_i inBounds
    · rw [readWord32Frame
        (address.value + headerBytes + target.semanticSlotBytes * index) (by
          simp [offset, slotIndexEq, target]
          omega)]
      rw [readUInt32Frame
        (address.value + headerBytes + target.semanticSlotBytes * index + 4) (by
          right
          simp [offset, slotIndexEq, target]
          omega)]
    · rfl
  have readUInt64Frame (other : Nat) (beforeField : other + 7 < offset) :
      memory.readUInt64 other = state.memory.readUInt64 other := by
    unfold LinearMemory.readUInt64
    rw [readUInt32Frame other (by omega)]
    rw [readUInt32Frame (other + 4) (by omega)]
  have usizeFieldFrame (index : Nat) :
      readUSizeField result address index = readUSizeField state address index := by
    unfold readUSizeField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    split <;> rename_i inBounds
    · rw [readUInt64Frame
        (address.value + headerBytes +
          target.semanticSlotBytes * (header.aux1.toNat + index)) (by
            simp [offset, slotIndexEq, objectCount, target]
            omega)]
    · rfl
  have relationAfter : ConstructorObjectRel result witness address info fieldKinds
      { semantic with
        scalarFields := {
          width := slotIndex
          offset := byteOffset
          value := .uint32 value } :: semantic.scalarFields.filter fun old =>
            old.width != slotIndex || old.offset != byteOffset } := by
    refine {
      header := ⟨header, headerReadAfter, headerKind, allocationBytes,
        tag, objectCount, usizeCount, scalarCount⟩
      headerOwned := related.headerOwned
      extent := related.extent
      semanticObjectFields := related.semanticObjectFields
      semanticUSizeFields := related.semanticUSizeFields
      semanticScalarFields := ?_
      fieldKindsSize := related.fieldKindsSize
      fieldKindsValid := related.fieldKindsValid
      objectFields := ?_
      usizeFields := ?_ }
    · intro field member
      simp [replaced] at member
      subst field
      exact ⟨slotIndexEq, fieldFits, readBack⟩
    · intro index kind semanticValue kindAt valueAt
      change semantic.objectFields[index]? = some semanticValue at valueAt
      obtain ⟨word, readBefore, valueRelated⟩ :=
        related.objectFields index kind semanticValue kindAt valueAt
      exact ⟨word, by rw [objectFieldFrame]; exact readBefore, valueRelated⟩
    · intro index semanticValue valueAt
      change semantic.usizeFields[index]? = some semanticValue at valueAt
      rw [usizeFieldFrame]
      exact related.usizeFields index semanticValue valueAt
  exact ⟨result, operation, readBack, tagFrame, objectFieldFrame, usizeFieldFrame,
    relationAfter⟩

/-- A checked byte write replaces one semantic `UInt8` packed coordinate and
preserves every constructor region before the scalar suffix. -/
theorem ConstructorObjectRel.writeScalarUInt8Field
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (slotIndex byteOffset : Nat) (value : UInt8)
    (replaced : semantic.scalarFields.filter (fun old =>
      old.width != slotIndex || old.offset != byteOffset) = [])
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 1 ≤ info.ssize) :
    ∃ result,
      Fir.Wasm.Concrete.writeScalarUInt8Field state address slotIndex byteOffset value =
        .ok result ∧
      ConstructorObjectRel result witness address info fieldKinds
        { semantic with
          scalarFields := {
            width := slotIndex
            offset := byteOffset
            value := .uint8 value } :: semantic.scalarFields.filter fun old =>
              old.width != slotIndex || old.offset != byteOffset } := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, decodedBefore, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * slotIndex + byteOffset
  have writeInBounds : offset < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    have layoutInMemory :
        address.value + (ConstructorLayout.ofInfo info).allocationBytes ≤
          state.memory.size :=
      Nat.le_trans (Nat.add_le_add_left allocationBytes address.value)
        extentInMemory
    simp [ConstructorLayout.ofInfo, target] at layoutInMemory
    simp [target] at layoutBound
    dsimp [offset]
    rw [slotIndexEq]
    simp [target]
    omega
  let memory : LinearMemory := state.memory.set offset value writeInBounds
  have fieldWrite : state.memory.writeByte offset value = .ok memory := by
    simp [LinearMemory.writeByte, writeInBounds, memory]
  have memorySize : memory.size = state.memory.size := by simp [memory]
  let result : MemoryState := { state with memory }
  have scalarAddress : scalarFieldAddress address header slotIndex byteOffset 1 =
      .ok offset := by
    unfold scalarFieldAddress
    simp [slotIndexEq, objectCount, usizeCount, fieldFits, scalarCount, offset]
    rfl
  have operation : Fir.Wasm.Concrete.writeScalarUInt8Field state address slotIndex
      byteOffset value = .ok result := by
    unfold Fir.Wasm.Concrete.writeScalarUInt8Field
    rw [constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    change (do
      let fieldAddress ← scalarFieldAddress address header slotIndex byteOffset 1
      let memory ← liftMemory (state.memory.writeByte fieldAddress value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [scalarAddress]
    simp only [Bind.bind, Except.bind]
    rw [fieldWrite]
    rfl
  have readByteFrame (other : Nat) (different : offset ≠ other) :
      memory.readByte other = state.memory.readByte other := by
    exact LinearMemory.readByte_set_other state.memory offset other value writeInBounds
      different
  have readUInt32Frame (other : Nat) (beforeField : other + 3 < offset) :
      memory.readUInt32 other = state.memory.readUInt32 other := by
    unfold LinearMemory.readUInt32
    rw [readByteFrame other (by omega)]
    rw [readByteFrame (other + 1) (by omega)]
    rw [readByteFrame (other + 2) (by omega)]
    rw [readByteFrame (other + 3) (by omega)]
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
    simp [live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have constructorHeaderAfter : readConstructorHeader result address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerReadAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have readBack : readScalarUInt8Field result address slotIndex byteOffset =
      .ok value := by
    unfold readScalarUInt8Field
    rw [constructorHeaderAfter]
    simp only [Bind.bind, Except.bind]
    rw [scalarAddress]
    change liftMemory (memory.readByte offset) = .ok value
    simp [memory, LinearMemory.readByte]
    rfl
  have readWord32Frame (other : Nat) (beforeField : other + 3 < offset) :
      memory.readWord32 other = state.memory.readWord32 other := by
    unfold LinearMemory.readWord32
    rw [readUInt32Frame other beforeField]
  have readUInt64Frame (other : Nat) (beforeField : other + 7 < offset) :
      memory.readUInt64 other = state.memory.readUInt64 other := by
    unfold LinearMemory.readUInt64
    rw [readUInt32Frame other (by omega)]
    rw [readUInt32Frame (other + 4) (by omega)]
  have objectFieldFrame (index : Nat) :
      readObjectField result address index = readObjectField state address index := by
    unfold readObjectField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    split <;> rename_i inBounds
    · rw [readWord32Frame _ (by
          simp [offset, slotIndexEq, target]
          omega)]
      rw [readUInt32Frame _ (by
          simp [offset, slotIndexEq, target]
          omega)]
    · rfl
  have usizeFieldFrame (index : Nat) :
      readUSizeField result address index = readUSizeField state address index := by
    unfold readUSizeField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    split <;> rename_i inBounds
    · rw [readUInt64Frame _ (by
          simp [offset, slotIndexEq, objectCount, target]
          omega)]
    · rfl
  refine ⟨result, operation, ?_⟩
  refine {
    header := ⟨header, headerReadAfter, headerKind, allocationBytes,
      tag, objectCount, usizeCount, scalarCount⟩
    headerOwned := related.headerOwned
    extent := related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := ?_
    fieldKindsSize := related.fieldKindsSize
    fieldKindsValid := related.fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · intro field member
    simp [replaced] at member
    subst field
    exact ⟨slotIndexEq, fieldFits, readBack⟩
  · intro index kind semanticValue kindAt valueAt
    change semantic.objectFields[index]? = some semanticValue at valueAt
    obtain ⟨word, readBefore, valueRelated⟩ :=
      related.objectFields index kind semanticValue kindAt valueAt
    exact ⟨word, by rw [objectFieldFrame]; exact readBefore, valueRelated⟩
  · intro index semanticValue valueAt
    change semantic.usizeFields[index]? = some semanticValue at valueAt
    rw [usizeFieldFrame]
    exact related.usizeFields index semanticValue valueAt

/-- A checked little-endian halfword write replaces one semantic `UInt16`
packed coordinate and preserves all fixed constructor slots. -/
theorem ConstructorObjectRel.writeScalarUInt16Field
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (slotIndex byteOffset : Nat) (value : UInt16)
    (replaced : semantic.scalarFields.filter (fun old =>
      old.width != slotIndex || old.offset != byteOffset) = [])
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 2 ≤ info.ssize) :
    ∃ result,
      Fir.Wasm.Concrete.writeScalarUInt16Field state address slotIndex byteOffset value =
        .ok result ∧
      ConstructorObjectRel result witness address info fieldKinds
        { semantic with
          scalarFields := {
            width := slotIndex
            offset := byteOffset
            value := .uint16 value } :: semantic.scalarFields.filter fun old =>
              old.width != slotIndex || old.offset != byteOffset } := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, decodedBefore, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * slotIndex + byteOffset
  have writeInBounds : offset + 1 < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    have layoutInMemory :
        address.value + (ConstructorLayout.ofInfo info).allocationBytes ≤
          state.memory.size :=
      Nat.le_trans (Nat.add_le_add_left allocationBytes address.value)
        extentInMemory
    simp [ConstructorLayout.ofInfo, target] at layoutInMemory
    simp [target] at layoutBound
    dsimp [offset]
    rw [slotIndexEq]
    simp [target]
    omega
  obtain ⟨memory, fieldWrite, memorySize, _, _, _⟩ :=
    LinearMemory.writeUInt16_spec state.memory offset value writeInBounds
  let result : MemoryState := { state with memory }
  have scalarAddress : scalarFieldAddress address header slotIndex byteOffset 2 =
      .ok offset := by
    unfold scalarFieldAddress
    simp [slotIndexEq, objectCount, usizeCount, fieldFits, scalarCount, offset]
    rfl
  have operation : Fir.Wasm.Concrete.writeScalarUInt16Field state address slotIndex
      byteOffset value = .ok result := by
    unfold Fir.Wasm.Concrete.writeScalarUInt16Field
    rw [constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    change (do
      let fieldAddress ← scalarFieldAddress address header slotIndex byteOffset 2
      let memory ← liftMemory (state.memory.writeUInt16 fieldAddress value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [scalarAddress]
    simp only [Bind.bind, Except.bind]
    rw [fieldWrite]
    rfl
  have readByteFrame (other : Nat)
      (ne0 : offset ≠ other) (ne1 : offset + 1 ≠ other) :
      memory.readByte other = state.memory.readByte other :=
    LinearMemory.readByte_of_writeUInt16_eq_ok_other state.memory memory offset value
      writeInBounds fieldWrite other ne0 ne1
  have readUInt32Frame (other : Nat) (beforeField : other + 3 < offset) :
      memory.readUInt32 other = state.memory.readUInt32 other := by
    unfold LinearMemory.readUInt32
    rw [readByteFrame other (by omega) (by omega)]
    rw [readByteFrame (other + 1) (by omega) (by omega)]
    rw [readByteFrame (other + 2) (by omega) (by omega)]
    rw [readByteFrame (other + 3) (by omega) (by omega)]
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
    simp [live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have constructorHeaderAfter : readConstructorHeader result address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerReadAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have readBack : readScalarUInt16Field result address slotIndex byteOffset =
      .ok value := by
    unfold readScalarUInt16Field
    rw [constructorHeaderAfter]
    simp only [Bind.bind, Except.bind]
    rw [scalarAddress]
    change liftMemory (memory.readUInt16 offset) = .ok value
    rw [LinearMemory.readUInt16_of_writeUInt16_eq_ok state.memory memory offset value
      writeInBounds fieldWrite]
    rfl
  have readWord32Frame (other : Nat) (beforeField : other + 3 < offset) :
      memory.readWord32 other = state.memory.readWord32 other := by
    unfold LinearMemory.readWord32
    rw [readUInt32Frame other beforeField]
  have readUInt64Frame (other : Nat) (beforeField : other + 7 < offset) :
      memory.readUInt64 other = state.memory.readUInt64 other := by
    unfold LinearMemory.readUInt64
    rw [readUInt32Frame other (by omega)]
    rw [readUInt32Frame (other + 4) (by omega)]
  have objectFieldFrame (index : Nat) :
      readObjectField result address index = readObjectField state address index := by
    unfold readObjectField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    split <;> rename_i inBounds
    · rw [readWord32Frame _ (by
          simp [offset, slotIndexEq, target]
          omega)]
      rw [readUInt32Frame _ (by
          simp [offset, slotIndexEq, target]
          omega)]
    · rfl
  have usizeFieldFrame (index : Nat) :
      readUSizeField result address index = readUSizeField state address index := by
    unfold readUSizeField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    split <;> rename_i inBounds
    · rw [readUInt64Frame _ (by
          simp [offset, slotIndexEq, objectCount, target]
          omega)]
    · rfl
  refine ⟨result, operation, ?_⟩
  refine {
    header := ⟨header, headerReadAfter, headerKind, allocationBytes,
      tag, objectCount, usizeCount, scalarCount⟩
    headerOwned := related.headerOwned
    extent := related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := ?_
    fieldKindsSize := related.fieldKindsSize
    fieldKindsValid := related.fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · intro field member
    simp [replaced] at member
    subst field
    exact ⟨slotIndexEq, fieldFits, readBack⟩
  · intro index kind semanticValue kindAt valueAt
    change semantic.objectFields[index]? = some semanticValue at valueAt
    obtain ⟨word, readBefore, valueRelated⟩ :=
      related.objectFields index kind semanticValue kindAt valueAt
    exact ⟨word, by rw [objectFieldFrame]; exact readBefore, valueRelated⟩
  · intro index semanticValue valueAt
    change semantic.usizeFields[index]? = some semanticValue at valueAt
    rw [usizeFieldFrame]
    exact related.usizeFields index semanticValue valueAt

end Fir.Wasm.Concrete
