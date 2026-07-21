import Fir.Wasm.Concrete.ProjectionCorrectness
import Fir.Wasm.Concrete.HeaderCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- A checked concrete tag replacement preserves the complete decoded
constructor relation, changing only the mutable semantic tag. -/
theorem ConstructorObjectRel.writeTag
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (tag : Nat) (tagFits : tag < UInt32.size) :
    ∃ result,
      Fir.Wasm.Concrete.writeTag state address tag = .ok result ∧
      ConstructorObjectRel result witness address info fieldKinds
        { semantic with tag := tag } := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, oldTag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at oldTag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size := by
    omega
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let updatedHeader : Header := { header with aux0 := UInt32.ofNat tag }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : Fir.Wasm.Concrete.writeTag state address tag = .ok result := by
    unfold Fir.Wasm.Concrete.writeTag
    rw [constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    rw [uint32Field_eq_ok "constructor tag" tag tagFits]
    change (do
      let memory ← liftMemory (updatedHeader.write state.memory address)
      return ({ state with memory } : MemoryState)) = .ok result
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
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have constructorHeaderAfter : readConstructorHeader result address = .ok updatedHeader := by
    unfold readConstructorHeader
    simp [heap, headerReadAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, updatedHeader, headerKind]
    rfl
  have readUInt32Frame (offset : Nat)
      (afterHeader : address.value + headerBytes ≤ offset) :
      memory.readUInt32 offset = state.memory.readUInt32 offset :=
    Header.readUInt32_of_write_eq_ok_other state.memory memory address updatedHeader
      offset headerInBounds headerWrite (by omega)
  have readByteFrame (offset : Nat)
      (afterHeader : address.value + headerBytes ≤ offset) :
      memory.readByte offset = state.memory.readByte offset :=
    Header.readByte_of_write_eq_ok_other state.memory memory address updatedHeader
      offset headerInBounds headerWrite (.inr afterHeader)
  have readUInt16Frame (offset : Nat)
      (afterHeader : address.value + headerBytes ≤ offset) :
      memory.readUInt16 offset = state.memory.readUInt16 offset := by
    unfold LinearMemory.readUInt16
    rw [readByteFrame offset afterHeader]
    rw [readByteFrame (offset + 1) (by omega)]
  have readWord32Frame (offset : Nat)
      (afterHeader : address.value + headerBytes ≤ offset) :
      memory.readWord32 offset = state.memory.readWord32 offset := by
    unfold LinearMemory.readWord32
    rw [readUInt32Frame offset afterHeader]
  have readUInt64Frame (offset : Nat)
      (afterHeader : address.value + headerBytes ≤ offset) :
      memory.readUInt64 offset = state.memory.readUInt64 offset := by
    unfold LinearMemory.readUInt64
    rw [readUInt32Frame offset afterHeader]
    rw [readUInt32Frame (offset + 4) (by omega)]
  have objectFieldFrame (index : Nat) :
      readObjectField result address index = readObjectField state address index := by
    unfold readObjectField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    simp only [updatedHeader]
    split <;> rename_i inBounds
    · rw [readWord32Frame
        (address.value + headerBytes + target.semanticSlotBytes * index) (by omega)]
      rw [readUInt32Frame
        (address.value + headerBytes + target.semanticSlotBytes * index + 4) (by omega)]
    · rfl
  have usizeFieldFrame (index : Nat) :
      readUSizeField result address index = readUSizeField state address index := by
    unfold readUSizeField
    rw [constructorHeaderAfter, constructorHeaderBefore]
    simp only [Bind.bind, Except.bind]
    simp only [updatedHeader]
    split <;> rename_i inBounds
    · rw [readUInt64Frame
        (address.value + headerBytes +
          target.semanticSlotBytes * (header.aux1.toNat + index)) (by omega)]
    · rfl
  have tagToNat : (UInt32.ofNat tag).toNat = tag :=
    UInt32.toNat_ofNat_of_lt' tagFits
  refine ⟨result, operation, ?_⟩
  refine {
    header := ⟨updatedHeader, headerReadAfter, by simp [updatedHeader, headerKind],
      by simpa [updatedHeader] using allocationBytes,
      by simpa [updatedHeader] using tagToNat,
      by simpa [updatedHeader] using objectCount,
      by simpa [updatedHeader] using usizeCount,
      by simpa [updatedHeader] using scalarCount⟩
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
    have beforeField := related.semanticScalarFields field member
    cases valueEq : field.value with
    | uint8 value =>
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
        change (do
          let fieldAddress ← scalarFieldAddress address header field.width
            field.offset 1
          liftMemory (memory.readByte fieldAddress)) = .ok value
        rw [scalarAddress]
        change liftMemory (memory.readByte _) = .ok value
        rw [readByteFrame _ (by omega)]
        exact readBefore
    | uint16 value =>
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
        change (do
          let fieldAddress ← scalarFieldAddress address header field.width
            field.offset 2
          liftMemory (memory.readUInt16 fieldAddress)) = .ok value
        rw [scalarAddress]
        change liftMemory (memory.readUInt16 _) = .ok value
        rw [readUInt16Frame _ (by omega)]
        exact readBefore
    | uint32 value =>
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
        change (do
          let fieldAddress ← scalarFieldAddress address header field.width
            field.offset 4
          liftMemory (memory.readUInt32 fieldAddress)) = .ok value
        rw [scalarAddress]
        change liftMemory (memory.readUInt32 _) = .ok value
        rw [readUInt32Frame _ (by omega)]
        exact readBefore
    | uint64 value =>
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
        change (do
          let fieldAddress ← scalarFieldAddress address header field.width
            field.offset 8
          liftMemory (memory.readUInt64 fieldAddress)) = .ok value
        rw [scalarAddress]
        change liftMemory (memory.readUInt64 _) = .ok value
        rw [readUInt64Frame _ (by omega)]
        exact readBefore
  · intro index kind value kindAt valueAt
    obtain ⟨word, readBefore, valueRelated⟩ :=
      related.objectFields index kind value kindAt valueAt
    exact ⟨word, by rw [objectFieldFrame]; exact readBefore, valueRelated⟩
  · intro index value valueAt
    rw [usizeFieldFrame]
    exact related.usizeFields index value valueAt

end Fir.Wasm.Concrete
