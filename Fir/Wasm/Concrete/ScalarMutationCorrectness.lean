import Fir.Wasm.Concrete.FieldMutationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- A compiler-shaped packed `UInt64` replacement reads back exactly and
frames every previously implemented constructor observation. -/
theorem ConstructorObjectRel.writeScalarUInt64Field
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (empty : semantic.scalarFields = [])
    (slotIndex byteOffset : Nat) (value : UInt64)
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
    target.semanticSlotBytes * slotIndex + byteOffset
  have writeInBounds : offset + 7 < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    rw [allocationBytes] at extentInMemory
    simp [ConstructorLayout.ofInfo, target] at extentInMemory
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
          value := .uint64 value } :: semantic.scalarFields.filter fun old =>
            old.width != slotIndex || old.offset != byteOffset } := by
    refine {
      header := ⟨header, headerReadAfter, headerKind, allocationBytes,
        persistent, tag, objectCount, usizeCount, scalarCount⟩
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
      simp [empty] at member
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

/-- The verified 32-bit lane installs the corresponding first semantic
packed field and frames all earlier constructor regions. -/
theorem ConstructorObjectRel.writeScalarUInt32Field
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (empty : semantic.scalarFields = [])
    (slotIndex byteOffset : Nat) (value : UInt32)
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
    target.semanticSlotBytes * slotIndex + byteOffset
  have writeInBounds : offset + 3 < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    rw [allocationBytes] at extentInMemory
    simp [ConstructorLayout.ofInfo, target] at extentInMemory
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
        persistent, tag, objectCount, usizeCount, scalarCount⟩
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
      simp [empty] at member
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

/-- A checked byte write implements the first semantic `UInt8` packed-field
insertion and preserves every constructor region before the scalar suffix. -/
theorem ConstructorObjectRel.writeScalarUInt8Field
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (empty : semantic.scalarFields = [])
    (slotIndex byteOffset : Nat) (value : UInt8)
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
    target.semanticSlotBytes * slotIndex + byteOffset
  have writeInBounds : offset < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    rw [allocationBytes] at extentInMemory
    simp [ConstructorLayout.ofInfo, target] at extentInMemory
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
      persistent, tag, objectCount, usizeCount, scalarCount⟩
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
    simp [empty] at member
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

/-- A checked little-endian halfword write implements the first semantic
`UInt16` packed-field insertion and preserves all fixed constructor slots. -/
theorem ConstructorObjectRel.writeScalarUInt16Field
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (empty : semantic.scalarFields = [])
    (slotIndex byteOffset : Nat) (value : UInt16)
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
    target.semanticSlotBytes * slotIndex + byteOffset
  have writeInBounds : offset + 1 < state.memory.size := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    rw [allocationBytes] at extentInMemory
    simp [ConstructorLayout.ofInfo, target] at extentInMemory
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
      persistent, tag, objectCount, usizeCount, scalarCount⟩
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
    simp [empty] at member
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
