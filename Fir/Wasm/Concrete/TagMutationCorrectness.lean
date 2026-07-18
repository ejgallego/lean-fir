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
  obtain ⟨header, headerRead, headerKind, allocationBytes, refCount, persistent,
      oldTag, objectCount, usizeCount, scalarCount⟩ := related.header
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
      by simpa [updatedHeader] using refCount,
      by simpa [updatedHeader] using persistent,
      by simpa [updatedHeader] using tagToNat,
      by simpa [updatedHeader] using objectCount,
      by simpa [updatedHeader] using usizeCount,
      by simpa [updatedHeader] using scalarCount⟩
    headerOwned := related.headerOwned
    extent := related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := related.semanticScalarFields
    fieldKindsSize := related.fieldKindsSize
    objectFields := ?_
    usizeFields := ?_ }
  · intro index kind value kindAt valueAt
    obtain ⟨word, readBefore, valueRelated⟩ :=
      related.objectFields index kind value kindAt valueAt
    exact ⟨word, by rw [objectFieldFrame]; exact readBefore, valueRelated⟩
  · intro index value valueAt
    rw [usizeFieldFrame]
    exact related.usizeFields index value valueAt

end Fir.Wasm.Concrete
