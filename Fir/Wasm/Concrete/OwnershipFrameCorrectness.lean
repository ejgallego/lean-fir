import Fir.Wasm.Concrete.ReferenceCountCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Two concrete states agree on every byte of one complete allocation.
Ownership writes preserve the cursor and memory size, so all checked decoders
rooted in this region can be transported independently of the written header. -/
structure MemoryState.AllocationFrame (before after : MemoryState)
    (address : Word32) (bytes : Nat) : Prop where
  cursor : after.heapCursor = before.heapCursor
  memorySize : after.memory.size = before.memory.size
  readByte : ∀ offset, offset < bytes →
    after.memory.readByte (address.value + offset) =
      before.memory.readByte (address.value + offset)

/-- A header write produces an allocation frame for every allocation interval
disjoint from the complete target interval. -/
theorem MemoryState.AllocationFrame.ofHeaderWrite
    {before after : MemoryState} {target other : Word32}
    {targetBytes otherBytes : Nat} {updatedHeader : Header}
    {memory : LinearMemory}
    (resultEq : after = { before with memory })
    (headerInBounds : target.value + headerBytes ≤ before.memory.size)
    (written : updatedHeader.write before.memory target = .ok memory)
    (targetMinimum : headerBytes ≤ targetBytes)
    (disjoint : target.value + targetBytes ≤ other.value ∨
      other.value + otherBytes ≤ target.value) :
    before.AllocationFrame after other otherBytes := by
  subst after
  refine ⟨rfl,
    Header.write_preserves_size before.memory memory target updatedHeader
      headerInBounds written,
    ?_⟩
  intro offset offsetWithin
  apply Header.readByte_of_write_eq_ok_other before.memory memory target
    updatedHeader (other.value + offset) headerInBounds written
  rcases disjoint with targetBefore | otherBefore
  · right
    omega
  · left
    omega

private theorem MemoryState.AllocationFrame.readUInt32Raw
    {before after : MemoryState} {address : Word32} {bytes offset : Nat}
    (frame : before.AllocationFrame after address bytes)
    (owned : offset + 4 ≤ bytes) :
    after.memory.readUInt32 (address.value + offset) =
      before.memory.readUInt32 (address.value + offset) := by
  unfold LinearMemory.readUInt32
  rw [frame.readByte offset (by omega)]
  rw [show address.value + offset + 1 = address.value + (offset + 1) by omega]
  rw [frame.readByte (offset + 1) (by omega)]
  rw [show address.value + offset + 2 = address.value + (offset + 2) by omega]
  rw [frame.readByte (offset + 2) (by omega)]
  rw [show address.value + offset + 3 = address.value + (offset + 3) by omega]
  rw [frame.readByte (offset + 3) (by omega)]

private theorem MemoryState.AllocationFrame.readHeaderRaw
    {before after : MemoryState} {address : Word32} {bytes : Nat}
    (frame : before.AllocationFrame after address bytes)
    (minimum : headerBytes ≤ bytes) :
    Header.read after.memory address = Header.read before.memory address := by
  unfold Header.read
  dsimp only
  rw [frame.readUInt32Raw (offset := headerKindOffset) (by
    simp [headerKindOffset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32Raw (offset := headerFlagsOffset) (by
    simp [headerFlagsOffset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32Raw (offset := headerRefCountOffset) (by
    simp [headerRefCountOffset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32Raw (offset := headerAllocationBytesOffset) (by
    simp [headerAllocationBytesOffset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32Raw (offset := headerAux0Offset) (by
    simp [headerAux0Offset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32Raw (offset := headerAux1Offset) (by
    simp [headerAux1Offset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32Raw (offset := headerAux2Offset) (by
    simp [headerAux2Offset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32Raw (offset := headerAux3Offset) (by
    simp [headerAux3Offset, headerBytes] at minimum ⊢; omega)]

/-- The global descriptor invariant discharges the interval-disjointness
premise needed to frame one non-target descriptor allocation. -/
theorem LiveHeapRel.allocationFrame_of_headerWrite_other
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {target other : Word32}
    {targetDescriptor otherDescriptor : AllocationDescriptor}
    {targetHeader otherHeader updatedHeader : Header}
    {memory : LinearMemory}
    (related : LiveHeapRel before witness runtime)
    (targetFound : witness.descriptors.lookup? target = some targetDescriptor)
    (otherFound : witness.descriptors.lookup? other = some otherDescriptor)
    (different : target.value ≠ other.value)
    (targetRead : Header.read before.memory target = .ok targetHeader)
    (otherRead : Header.read before.memory other = .ok otherHeader)
    (resultEq : after = { before with memory })
    (headerInBounds : target.value + headerBytes ≤ before.memory.size)
    (written : updatedHeader.write before.memory target = .ok memory) :
    before.AllocationFrame after other otherHeader.allocationBytes.toNat := by
  obtain ⟨regionHeader, regionRead, targetMinimum, _, _⟩ :=
    related.descriptorRegion target targetDescriptor targetFound
  rw [targetRead] at regionRead
  have headerEq := Except.ok.inj regionRead
  subst regionHeader
  have disjoint := related.descriptorDisjoint target other targetDescriptor
    otherDescriptor targetFound otherFound different targetHeader otherHeader
      targetRead otherRead
  exact .ofHeaderWrite resultEq headerInBounds written targetMinimum disjoint

/-- Replacing one descriptor header without changing its allocation extent
preserves the global descriptor-region and disjointness invariants. -/
theorem LiveHeapRel.descriptorSpatial_of_headerWrite
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress : Word32}
    {targetDescriptor : AllocationDescriptor}
    {oldHeader updatedHeader : Header} {memory : LinearMemory}
    (related : LiveHeapRel before witness runtime)
    (targetFound : witness.descriptors.lookup? targetAddress = some targetDescriptor)
    (oldRead : Header.read before.memory targetAddress = .ok oldHeader)
    (resultEq : after = { before with memory })
    (headerInBounds : targetAddress.value + headerBytes ≤ before.memory.size)
    (written : updatedHeader.write before.memory targetAddress = .ok memory)
    (sameExtent : updatedHeader.allocationBytes = oldHeader.allocationBytes) :
    (∀ address descriptor,
      witness.descriptors.lookup? address = some descriptor →
      ∃ header,
        Header.read after.memory address = .ok header ∧
        headerBytes ≤ header.allocationBytes.toNat ∧
        header.allocationBytes.toNat % target.heapAlignment = 0 ∧
        address.value + header.allocationBytes.toNat ≤ after.heapCursor) ∧
    (∀ left right leftDescriptor rightDescriptor,
      witness.descriptors.lookup? left = some leftDescriptor →
      witness.descriptors.lookup? right = some rightDescriptor →
      left.value ≠ right.value →
      ∀ leftHeader rightHeader,
        Header.read after.memory left = .ok leftHeader →
        Header.read after.memory right = .ok rightHeader →
        left.value + leftHeader.allocationBytes.toNat ≤ right.value ∨
          right.value + rightHeader.allocationBytes.toNat ≤ left.value) := by
  have wordEq : ∀ left right : Word32, left.value = right.value → left = right := by
    intro left right equal
    cases left
    cases right
    simp_all
  obtain ⟨regionHeader, regionRead, targetMinimum, targetAligned, targetExtent⟩ :=
    related.descriptorRegion targetAddress targetDescriptor targetFound
  rw [oldRead] at regionRead
  have regionHeaderEq := Except.ok.inj regionRead
  subst regionHeader
  have updatedRead : Header.read after.memory targetAddress = .ok updatedHeader := by
    subst after
    exact Header.read_of_write_eq_ok before.memory memory targetAddress updatedHeader
      headerInBounds written
  refine ⟨?_, ?_⟩
  · intro address descriptor found
    by_cases isTarget : targetAddress.value = address.value
    · have addressEq : address = targetAddress := wordEq address targetAddress isTarget.symm
      subst address
      exact ⟨updatedHeader, updatedRead,
        by simpa [sameExtent] using targetMinimum,
        by simpa [sameExtent] using targetAligned,
        by subst after; simpa [sameExtent] using targetExtent⟩
    · obtain ⟨header, headerRead, minimum, aligned, extent⟩ :=
        related.descriptorRegion address descriptor found
      have frame := related.allocationFrame_of_headerWrite_other targetFound found
        isTarget oldRead headerRead resultEq headerInBounds written
      exact ⟨header, by rw [frame.readHeaderRaw minimum]; exact headerRead,
        minimum, aligned, by rw [frame.cursor]; exact extent⟩
  · intro left right leftDescriptor rightDescriptor leftFound rightFound different
      leftHeader rightHeader leftRead rightRead
    by_cases leftTarget : targetAddress.value = left.value
    · by_cases rightTarget : targetAddress.value = right.value
      · exact False.elim (different (leftTarget.symm.trans rightTarget))
      · have leftEq : left = targetAddress := wordEq left targetAddress leftTarget.symm
        subst left
        rw [updatedRead] at leftRead
        have leftHeaderEq := Except.ok.inj leftRead
        subst leftHeader
        obtain ⟨oldRightHeader, oldRightRead, rightMinimum, _, _⟩ :=
          related.descriptorRegion right rightDescriptor rightFound
        have frame := related.allocationFrame_of_headerWrite_other targetFound
          rightFound rightTarget oldRead oldRightRead resultEq headerInBounds written
        rw [frame.readHeaderRaw rightMinimum] at rightRead
        have oldDisjoint := related.descriptorDisjoint targetAddress right
          targetDescriptor rightDescriptor targetFound rightFound rightTarget
            oldHeader rightHeader oldRead rightRead
        simpa [sameExtent] using oldDisjoint
    · by_cases rightTarget : targetAddress.value = right.value
      · have rightEq : right = targetAddress := wordEq right targetAddress rightTarget.symm
        subst right
        rw [updatedRead] at rightRead
        have rightHeaderEq := Except.ok.inj rightRead
        subst rightHeader
        obtain ⟨oldLeftHeader, oldLeftRead, leftMinimum, _, _⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        have frame := related.allocationFrame_of_headerWrite_other targetFound
          leftFound leftTarget oldRead oldLeftRead resultEq headerInBounds written
        rw [frame.readHeaderRaw leftMinimum] at leftRead
        have oldDisjoint := related.descriptorDisjoint left targetAddress
          leftDescriptor targetDescriptor leftFound targetFound (Ne.symm leftTarget)
            leftHeader oldHeader leftRead oldRead
        simpa [sameExtent] using oldDisjoint
      · obtain ⟨oldLeftHeader, oldLeftRead, leftMinimum, _, _⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        obtain ⟨oldRightHeader, oldRightRead, rightMinimum, _, _⟩ :=
          related.descriptorRegion right rightDescriptor rightFound
        have leftFrame := related.allocationFrame_of_headerWrite_other targetFound
          leftFound leftTarget oldRead oldLeftRead resultEq headerInBounds written
        have rightFrame := related.allocationFrame_of_headerWrite_other targetFound
          rightFound rightTarget oldRead oldRightRead resultEq headerInBounds written
        rw [leftFrame.readHeaderRaw leftMinimum] at leftRead
        rw [rightFrame.readHeaderRaw rightMinimum] at rightRead
        exact related.descriptorDisjoint left right leftDescriptor rightDescriptor
          leftFound rightFound different leftHeader rightHeader leftRead rightRead

theorem MemoryState.AllocationFrame.readUInt16
    {before after : MemoryState} {address : Word32} {bytes offset : Nat}
    (frame : before.AllocationFrame after address bytes)
    (owned : offset + 2 ≤ bytes) :
    after.memory.readUInt16 (address.value + offset) =
      before.memory.readUInt16 (address.value + offset) := by
  unfold LinearMemory.readUInt16
  rw [frame.readByte offset (by omega)]
  rw [show address.value + offset + 1 = address.value + (offset + 1) by omega]
  rw [frame.readByte (offset + 1) (by omega)]

theorem MemoryState.AllocationFrame.readUInt32
    {before after : MemoryState} {address : Word32} {bytes offset : Nat}
    (frame : before.AllocationFrame after address bytes)
    (owned : offset + 4 ≤ bytes) :
    after.memory.readUInt32 (address.value + offset) =
      before.memory.readUInt32 (address.value + offset) := by
  unfold LinearMemory.readUInt32
  rw [frame.readByte offset (by omega)]
  rw [show address.value + offset + 1 = address.value + (offset + 1) by omega]
  rw [frame.readByte (offset + 1) (by omega)]
  rw [show address.value + offset + 2 = address.value + (offset + 2) by omega]
  rw [frame.readByte (offset + 2) (by omega)]
  rw [show address.value + offset + 3 = address.value + (offset + 3) by omega]
  rw [frame.readByte (offset + 3) (by omega)]

theorem MemoryState.AllocationFrame.readWord32
    {before after : MemoryState} {address : Word32} {bytes offset : Nat}
    (frame : before.AllocationFrame after address bytes)
    (owned : offset + 4 ≤ bytes) :
    after.memory.readWord32 (address.value + offset) =
      before.memory.readWord32 (address.value + offset) := by
  unfold LinearMemory.readWord32
  rw [frame.readUInt32 owned]

theorem MemoryState.AllocationFrame.readUInt64
    {before after : MemoryState} {address : Word32} {bytes offset : Nat}
    (frame : before.AllocationFrame after address bytes)
    (owned : offset + 8 ≤ bytes) :
    after.memory.readUInt64 (address.value + offset) =
      before.memory.readUInt64 (address.value + offset) := by
  unfold LinearMemory.readUInt64
  rw [frame.readUInt32 (offset := offset) (by omega)]
  rw [show address.value + offset + 4 = address.value + (offset + 4) by omega]
  rw [frame.readUInt32 (offset := offset + 4) (by omega)]

theorem MemoryState.AllocationFrame.readHeader
    {before after : MemoryState} {address : Word32} {bytes : Nat}
    (frame : before.AllocationFrame after address bytes)
    (minimum : headerBytes ≤ bytes) :
    Header.read after.memory address = Header.read before.memory address := by
  unfold Header.read
  dsimp only
  rw [frame.readUInt32 (offset := headerKindOffset) (by
    simp [headerKindOffset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32 (offset := headerFlagsOffset) (by
    simp [headerFlagsOffset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32 (offset := headerRefCountOffset) (by
    simp [headerRefCountOffset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32 (offset := headerAllocationBytesOffset) (by
    simp [headerAllocationBytesOffset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32 (offset := headerAux0Offset) (by
    simp [headerAux0Offset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32 (offset := headerAux1Offset) (by
    simp [headerAux1Offset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32 (offset := headerAux2Offset) (by
    simp [headerAux2Offset, headerBytes] at minimum ⊢; omega)]
  rw [frame.readUInt32 (offset := headerAux3Offset) (by
    simp [headerAux3Offset, headerBytes] at minimum ⊢; omega)]

theorem MemoryState.AllocationFrame.readLiveHeader
    {before after : MemoryState} {address : Word32} {bytes : Nat}
    (frame : before.AllocationFrame after address bytes)
    (minimum : headerBytes ≤ bytes) :
    after.readLiveHeader address = before.readLiveHeader address := by
  unfold MemoryState.readLiveHeader
  rw [frame.readHeader minimum, frame.memorySize]

theorem MemoryState.AllocationFrame.readNaturalLimbs
    {before after : MemoryState} {address : Word32} {bytes : Nat}
    (frame : before.AllocationFrame after address bytes)
    (index count : Nat)
    (owned : headerBytes + target.semanticSlotBytes * (index + count) ≤ bytes) :
    Fir.Wasm.Concrete.readNaturalLimbs after.memory address.value index count =
      Fir.Wasm.Concrete.readNaturalLimbs before.memory address.value index count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      unfold Fir.Wasm.Concrete.readNaturalLimbs
      rw [show address.value + headerBytes + target.semanticSlotBytes * index =
        address.value + (headerBytes + target.semanticSlotBytes * index) by omega]
      rw [frame.readUInt64
        (offset := headerBytes + target.semanticSlotBytes * index) (by
          simp [target] at owned ⊢
          omega)]
      rw [ih (index + 1) (by
        simp [target] at owned ⊢
        omega)]

theorem MemoryState.AllocationFrame.readNatural_eq
    {before after : MemoryState} {address : Word32} {header : Header}
    (frame : before.AllocationFrame after address header.allocationBytes.toNat)
    (headerRead : before.readLiveHeader address = .ok header)
    (limbsFit : headerBytes +
      target.semanticSlotBytes * header.aux1.toNat ≤
        header.allocationBytes.toNat) :
    Fir.Wasm.Concrete.readNatural after address =
      Fir.Wasm.Concrete.readNatural before address := by
  obtain ⟨heap, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header headerRead
  have headerAfter : after.readLiveHeader address = .ok header := by
    rw [frame.readLiveHeader minimum]
    exact headerRead
  unfold Fir.Wasm.Concrete.readNatural
  simp [heap]
  rw [headerAfter, headerRead]
  simp only [liftMemory, Bind.bind, Except.bind]
  rw [frame.readNaturalLimbs 0 header.aux1.toNat (by simpa using limbsFit)]

/-- Every constructor observation stays inside its declared mixed-layout
allocation, so a complete allocation frame preserves the decoded object. -/
theorem ConstructorObjectRel.allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel before witness address info fieldKinds semantic)
    (frame : before.AllocationFrame after address
      (ConstructorLayout.ofInfo info).allocationBytes) :
    ConstructorObjectRel after witness address info fieldKinds semantic := by
  obtain ⟨header, headerRead, headerKind, allocationBytes, persistent,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header
  obtain ⟨heap, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header headerRead
  have layoutMinimum : headerBytes ≤
      (ConstructorLayout.ofInfo info).allocationBytes := by
    rw [← allocationBytes]
    exact minimum
  have headerAfter : after.readLiveHeader address = .ok header := by
    rw [frame.readLiveHeader layoutMinimum]
    exact headerRead
  have constructorHeaderBefore : readConstructorHeader before address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have constructorHeaderAfter : readConstructorHeader after address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have scalarFieldsAfter : ∀ field, field ∈ semantic.scalarFields →
      match field.value with
      | .uint8 value =>
          field.width = info.size + info.usize ∧
          field.offset + 1 ≤ info.ssize ∧
          readScalarUInt8Field after address field.width field.offset = .ok value
      | .uint16 value =>
          field.width = info.size + info.usize ∧
          field.offset + 2 ≤ info.ssize ∧
          readScalarUInt16Field after address field.width field.offset = .ok value
      | .uint32 value =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field after address field.width field.offset = .ok value
      | .uint64 value =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field after address field.width field.offset = .ok value := by
    intro field member
    have beforeField := related.semanticScalarFields field member
    cases valueEq : field.value with
    | uint8 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            headerBytes + target.semanticSlotBytes * field.width + field.offset <
              (ConstructorLayout.ofInfo info).allocationBytes := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          simp [ConstructorLayout.ofInfo, target] at layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt8Field after address field.width field.offset =
              readScalarUInt8Field before address field.width field.offset := by
          unfold readScalarUInt8Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 1 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          have memoryEq : after.memory.readByte
                (address.value + headerBytes +
                  target.semanticSlotBytes * field.width + field.offset) =
              before.memory.readByte
                (address.value + headerBytes +
                  target.semanticSlotBytes * field.width + field.offset) := by
            rw [show address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset =
              address.value + (headerBytes +
                target.semanticSlotBytes * field.width + field.offset) by omega]
            exact frame.readByte _ fieldOwned
          simp [memoryEq]
        rw [operationEq]
        exact readBefore
    | uint16 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            headerBytes + target.semanticSlotBytes * field.width + field.offset + 2 ≤
              (ConstructorLayout.ofInfo info).allocationBytes := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          simp [ConstructorLayout.ofInfo, target] at layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt16Field after address field.width field.offset =
              readScalarUInt16Field before address field.width field.offset := by
          unfold readScalarUInt16Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 2 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          have memoryEq : after.memory.readUInt16
                (address.value + headerBytes +
                  target.semanticSlotBytes * field.width + field.offset) =
              before.memory.readUInt16
                (address.value + headerBytes +
                  target.semanticSlotBytes * field.width + field.offset) := by
            rw [show address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset =
              address.value + (headerBytes +
                target.semanticSlotBytes * field.width + field.offset) by omega]
            exact frame.readUInt16 fieldOwned
          simp [memoryEq]
        rw [operationEq]
        exact readBefore
    | uint32 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            headerBytes + target.semanticSlotBytes * field.width + field.offset + 4 ≤
              (ConstructorLayout.ofInfo info).allocationBytes := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          simp [ConstructorLayout.ofInfo, target] at layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt32Field after address field.width field.offset =
              readScalarUInt32Field before address field.width field.offset := by
          unfold readScalarUInt32Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 4 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          have memoryEq : after.memory.readUInt32
                (address.value + headerBytes +
                  target.semanticSlotBytes * field.width + field.offset) =
              before.memory.readUInt32
                (address.value + headerBytes +
                  target.semanticSlotBytes * field.width + field.offset) := by
            rw [show address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset =
              address.value + (headerBytes +
                target.semanticSlotBytes * field.width + field.offset) by omega]
            exact frame.readUInt32 fieldOwned
          simp [memoryEq]
        rw [operationEq]
        exact readBefore
    | uint64 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            headerBytes + target.semanticSlotBytes * field.width + field.offset + 8 ≤
              (ConstructorLayout.ofInfo info).allocationBytes := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          simp [ConstructorLayout.ofInfo, target] at layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt64Field after address field.width field.offset =
              readScalarUInt64Field before address field.width field.offset := by
          unfold readScalarUInt64Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 8 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          have memoryEq : after.memory.readUInt64
                (address.value + headerBytes +
                  target.semanticSlotBytes * field.width + field.offset) =
              before.memory.readUInt64
                (address.value + headerBytes +
                  target.semanticSlotBytes * field.width + field.offset) := by
            rw [show address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset =
              address.value + (headerBytes +
                target.semanticSlotBytes * field.width + field.offset) by omega]
            exact frame.readUInt64 fieldOwned
          simp [memoryEq]
        rw [operationEq]
        exact readBefore
  refine {
    header := ⟨header, headerAfter, headerKind, allocationBytes, persistent,
      tag, objectCount, usizeCount, scalarCount⟩
    headerOwned := by rw [frame.cursor]; exact related.headerOwned
    extent := by rw [frame.cursor]; exact related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := scalarFieldsAfter
    fieldKindsSize := related.fieldKindsSize
    fieldKindsValid := related.fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · intro index kind value kindAt valueAt
    obtain ⟨word, fieldBefore, valueRelated⟩ :=
      related.objectFields index kind value kindAt valueAt
    have indexLt : index < info.size := by
      obtain ⟨semanticIndex, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
      have semanticSize := related.semanticObjectFields
      omega
    have fieldOwned :
        headerBytes + target.semanticSlotBytes * index + 8 ≤
          (ConstructorLayout.ofInfo info).allocationBytes := by
      have layoutBound := align8_ge
        (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
      simp [ConstructorLayout.ofInfo, target] at layoutBound ⊢
      omega
    have operationEq : readObjectField after address index =
        readObjectField before address index := by
      unfold readObjectField
      rw [constructorHeaderAfter, constructorHeaderBefore]
      simp only [Bind.bind, Except.bind]
      rw [objectCount, if_pos indexLt]
      have wordFrame :
          after.memory.readWord32
              (address.value + headerBytes + target.semanticSlotBytes * index) =
            before.memory.readWord32
              (address.value + headerBytes + target.semanticSlotBytes * index) := by
        rw [show address.value + headerBytes + target.semanticSlotBytes * index =
          address.value + (headerBytes + target.semanticSlotBytes * index) by omega]
        exact frame.readWord32 (by omega)
      have paddingFrame :
          after.memory.readUInt32
              (address.value + headerBytes + target.semanticSlotBytes * index + 4) =
            before.memory.readUInt32
              (address.value + headerBytes + target.semanticSlotBytes * index + 4) := by
        rw [show address.value + headerBytes + target.semanticSlotBytes * index + 4 =
          address.value + (headerBytes + target.semanticSlotBytes * index + 4) by omega]
        exact frame.readUInt32 (by omega)
      rw [wordFrame, paddingFrame]
      simp only [if_pos indexLt]
    exact ⟨word, by rw [operationEq]; exact fieldBefore, valueRelated⟩
  · intro index value valueAt
    have indexLt : index < info.usize := by
      obtain ⟨semanticIndex, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
      have semanticSize := related.semanticUSizeFields
      omega
    have fieldOwned :
        headerBytes + target.semanticSlotBytes * (info.size + index) + 8 ≤
          (ConstructorLayout.ofInfo info).allocationBytes := by
      have layoutBound := align8_ge
        (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
      simp [ConstructorLayout.ofInfo, target] at layoutBound ⊢
      omega
    have operationEq : readUSizeField after address index =
        readUSizeField before address index := by
      unfold readUSizeField
      rw [constructorHeaderAfter, constructorHeaderBefore]
      simp only [Bind.bind, Except.bind]
      rw [objectCount]
      rw [show address.value + headerBytes +
          target.semanticSlotBytes * (info.size + index) =
        address.value + (headerBytes +
          target.semanticSlotBytes * (info.size + index)) by omega]
      rw [frame.readUInt64
        (offset := headerBytes + target.semanticSlotBytes * (info.size + index))
        fieldOwned]
    rw [operationEq]
    exact related.usizeFields index value valueAt

/-- Canonical released cells depend only on their raw header and therefore
transport across an allocation frame. -/
theorem DeadCellRel.allocationFrame
    {before after : MemoryState} {address : Word32} {header : Header}
    (related : DeadCellRel before address)
    (headerRead : Header.read before.memory address = .ok header)
    (frame : before.AllocationFrame after address header.allocationBytes.toNat) :
    DeadCellRel after address := by
  obtain ⟨actual, actualRead, addressHeap, headerKind, ordinary, dead, refCount,
      aux0, aux1, aux2, aux3, minimum, aligned, extentInMemory⟩ := related.header
  rw [headerRead] at actualRead
  have headerEq := Except.ok.inj actualRead
  subst actual
  have headerAfter : Header.read after.memory address = .ok header := by
    rw [frame.readHeader minimum]
    exact headerRead
  exact {
    header := ⟨header, headerAfter, addressHeap, headerKind, ordinary, dead, refCount,
      aux0, aux1, aux2, aux3, minimum, aligned, by
        rw [frame.memorySize]
        exact extentInMemory⟩
    headerOwned := by rw [frame.cursor]; exact related.headerOwned }

/-- A complete boxed-scalar allocation decoder is stable when every byte in
its region is framed. -/
theorem BoxedObjectRel.allocationFrame
    {before after : MemoryState} {address : Word32} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {header : Header}
    (related : BoxedObjectRel before address kind scalar header)
    (frame : before.AllocationFrame after address header.allocationBytes.toNat) :
    BoxedObjectRel after address kind scalar header := by
  obtain ⟨heap, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header
      related.headerRead
  have headerAfter : after.readLiveHeader address = .ok header := by
    rw [frame.readLiveHeader minimum]
    exact related.headerRead
  have payloadFits : headerBytes + target.semanticSlotBytes ≤
      header.allocationBytes.toNat := by
    rw [related.allocationBytes]
    exact align8_ge _
  have payloadEq :
      after.memory.readUInt64 (address.value + headerBytes) =
        before.memory.readUInt64 (address.value + headerBytes) := by
    simpa using frame.readUInt64 (offset := headerBytes) (by
      simpa [target] using payloadFits)
  have decoderEq : readBoxedScalar after kind address =
      readBoxedScalar before kind address := by
    unfold readBoxedScalar
    rw [heap]
    simp only
    rw [headerAfter, related.headerRead]
    simp only [liftMemory, Bind.bind, Except.bind]
    have boxed : (header.kind == ObjectKind.boxed) = true := by
      rw [related.headerKind]
      decide
    rw [boxed]
    simp only [if_true]
    unfold readHeapBoxedScalar
    rw [payloadEq]
  exact {
    scalarKind := related.scalarKind
    headerRead := headerAfter
    headerKind := related.headerKind
    ordinary := related.ordinary
    allocationBytes := related.allocationBytes
    kindCode := related.kindCode
    payloadBytes := related.payloadBytes
    reserved2 := related.reserved2
    reserved3 := related.reserved3
    headerOwned := by rw [frame.cursor]; exact related.headerOwned
    extent := by rw [frame.cursor]; exact related.extent
    decoded := by rw [decoderEq]; exact related.decoded }

/-- Boxed scalars and heap naturals are the nonrecursive live ownership
representations. A complete allocation frame preserves their `LiveCellRel`. -/
theorem LiveCellRel.leaf_allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell} {regionHeader : Header}
    (related : LiveCellRel before witness address cell)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (headerRead : Header.read before.memory address = .ok regionHeader)
    (frame : before.AllocationFrame after address
      regionHeader.allocationBytes.toNat) :
    LiveCellRel after witness address cell := by
  cases related with
  | constructor descriptor objectEq objectRelated liveHeaderRead headerKind refCount
        persistent live =>
      rcases leafCell with boxedCell | naturalCell
      · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
      · obtain ⟨value, naturalEq⟩ := naturalCell
        rw [objectEq] at naturalEq
        contradiction
  | @boxed kind scalar actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          objectRelated.headerRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      exact .boxed descriptor objectEq (objectRelated.allocationFrame frame)
        refCount persistent live
  | @natural value actualHeader _ descriptor objectEq liveHeaderRead headerKind ordinary
        marker extent limbsFit decoded refCount persistent live =>
      obtain ⟨_, rawRead, _, minimum, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          liveHeaderRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      have headerAfter : after.readLiveHeader address = .ok actualHeader := by
        rw [frame.readLiveHeader minimum]
        exact liveHeaderRead
      exact .natural descriptor objectEq headerAfter headerKind ordinary marker
        (by rw [frame.cursor]; exact extent) limbsFit
        (by rw [frame.readNatural_eq liveHeaderRead limbsFit]; exact decoded)
        refCount persistent live

/-- Whole cells whose live branch is nonrecursive transport across a complete
allocation frame; dead branches require only their canonical raw header. -/
theorem CellRel.leaf_allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell} {header : Header}
    (related : CellRel before witness address cell)
    (leafCell : cell.live = true →
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (headerRead : Header.read before.memory address = .ok header)
    (frame : before.AllocationFrame after address header.allocationBytes.toNat) :
    CellRel after witness address cell := by
  cases related with
  | live liveRelated =>
      exact .live (liveRelated.leaf_allocationFrame
        (leafCell liveRelated.live_eq_true) headerRead frame)
  | dead count dead descriptor deadRelated =>
      exact .dead count dead descriptor
        (deadRelated.allocationFrame headerRead frame)

/-- Every currently modeled live or dead heap-cell representation transports
across a frame of its complete descriptor allocation. -/
theorem LiveCellRel.allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell} {regionHeader : Header}
    (related : LiveCellRel before witness address cell)
    (headerRead : Header.read before.memory address = .ok regionHeader)
    (frame : before.AllocationFrame after address
      regionHeader.allocationBytes.toNat) :
    LiveCellRel after witness address cell := by
  cases related with
  | @constructor info fieldKinds semantic actualHeader _ descriptor objectEq
        objectRelated liveHeaderRead headerKind refCount persistent live =>
      obtain ⟨_, rawRead, _, minimum, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          liveHeaderRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      obtain ⟨objectHeader, objectHeaderRead, _, allocationBytes, _, _, _, _, _⟩ :=
        objectRelated.header
      rw [liveHeaderRead] at objectHeaderRead
      have objectHeaderEq := Except.ok.inj objectHeaderRead
      subst objectHeader
      have objectFrame : before.AllocationFrame after address
          (ConstructorLayout.ofInfo info).allocationBytes := by
        rw [← allocationBytes]
        exact frame
      have headerAfter : after.readLiveHeader address = .ok actualHeader := by
        rw [frame.readLiveHeader minimum]
        exact liveHeaderRead
      exact .constructor descriptor objectEq
        (objectRelated.allocationFrame objectFrame) headerAfter headerKind refCount
          persistent live
  | @boxed kind scalar actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          objectRelated.headerRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      exact .boxed descriptor objectEq (objectRelated.allocationFrame frame)
        refCount persistent live
  | @natural value actualHeader _ descriptor objectEq liveHeaderRead headerKind ordinary
        marker extent limbsFit decoded refCount persistent live =>
      obtain ⟨_, rawRead, _, minimum, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          liveHeaderRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      have headerAfter : after.readLiveHeader address = .ok actualHeader := by
        rw [frame.readLiveHeader minimum]
        exact liveHeaderRead
      exact .natural descriptor objectEq headerAfter headerKind ordinary marker
        (by rw [frame.cursor]; exact extent) limbsFit
        (by rw [frame.readNatural_eq liveHeaderRead limbsFit]; exact decoded)
        refCount persistent live

theorem CellRel.allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell} {header : Header}
    (related : CellRel before witness address cell)
    (headerRead : Header.read before.memory address = .ok header)
    (frame : before.AllocationFrame after address header.allocationBytes.toNat) :
    CellRel after witness address cell := by
  cases related with
  | live liveRelated => exact .live (liveRelated.allocationFrame headerRead frame)
  | dead count dead descriptor deadRelated =>
      exact .dead count dead descriptor
        (deadRelated.allocationFrame headerRead frame)

/-- A promoted immediate's persistent heap representation is stable across a
complete frame of its allocation. -/
theorem PromotedTagRel.allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {payload : UInt64} {address : Word32} {header : Header}
    (related : PromotedTagRel before witness payload address)
    (headerRead : before.readLiveHeader address = .ok header)
    (frame : before.AllocationFrame after address header.allocationBytes.toNat) :
    PromotedTagRel after witness payload address := by
  obtain ⟨actual, actualRead, headerKind, persistent, refCount, marker, extent,
      payloadFits⟩ := related.header
  rw [headerRead] at actualRead
  have headerEq := Except.ok.inj actualRead
  subst actual
  obtain ⟨heap, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header headerRead
  have headerAfter : after.readLiveHeader address = .ok header := by
    rw [frame.readLiveHeader minimum]
    exact headerRead
  have payloadEq :
      after.memory.readUInt64 (address.value + headerBytes) =
        before.memory.readUInt64 (address.value + headerBytes) := by
    simpa using frame.readUInt64 (offset := headerBytes) (by
      simpa [target] using payloadFits)
  have decoderEq : readTag after address = readTag before address := by
    unfold readTag
    rw [heap]
    simp only
    rw [headerAfter, headerRead]
    simp only [liftMemory, Bind.bind, Except.bind]
    have notConstructor : (header.kind == ObjectKind.constructor) = false := by
      rw [headerKind]
      decide
    have natural : (header.kind == ObjectKind.natural) = true := by
      rw [headerKind]
      decide
    rw [notConstructor]
    rw [natural, persistent]
    simp only [Bool.true_and, Bool.false_eq_true]
    have markerEq : (header.aux0 == promotedTagMarker) = true := by simp [marker]
    rw [markerEq]
    simp only [if_true]
    rw [payloadEq]
  exact {
    mapped := related.mapped
    descriptor := related.descriptor
    header := ⟨header, headerAfter, headerKind, persistent, refCount, marker,
      by rw [frame.cursor]; exact extent, payloadFits⟩
    decoded := by rw [decoderEq]; exact related.decoded }

/-- One extent-preserving header write plus a new target-cell relation is
enough to perform the matching semantic replacement and rebuild the complete
whole-heap refinement. This is the common spatial boundary for count rewrites
and canonical release. -/
theorem LiveHeapRel.setCell_of_headerWrite
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell replacement : HeapCell} {targetDescriptor : AllocationDescriptor}
    {oldHeader updatedHeader : Header} {memory : LinearMemory}
    (related : LiveHeapRel before witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (targetFound : witness.descriptors.lookup? address = some targetDescriptor)
    (oldRead : Header.read before.memory address = .ok oldHeader)
    (resultEq : after = { before with memory })
    (headerInBounds : address.value + headerBytes ≤ before.memory.size)
    (written : updatedHeader.write before.memory address = .ok memory)
    (sameExtent : updatedHeader.allocationBytes = oldHeader.allocationBytes)
    (finalValid : after.FrontierInvariant)
    (targetRelated : CellRel after witness address replacement) :
    ∃ nextRuntime,
      setCell runtime location replacement = .ok nextRuntime ∧
      LiveHeapRel after witness nextRuntime := by
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.descriptorSpatial_of_headerWrite targetFound oldRead resultEq
      headerInBounds written sameExtent
  have wordEq : ∀ left right : Word32, left.value = right.value → left = right := by
    intro left right equal
    cases left
    cases right
    simp_all
  have cellFrame : ∀ other otherAddress otherCell,
      other ≠ location →
      findCell? runtime.heap other = some otherCell →
      witness.locations.lookup? other = some otherAddress →
      CellRel before witness otherAddress otherCell →
      CellRel after witness otherAddress otherCell := by
    intro other otherAddress otherCell otherNe foundOther mappedOther otherRelated
    obtain ⟨otherDescriptor, otherDescriptorFound⟩ := otherRelated.descriptor
    have different : address.value ≠ otherAddress.value := by
      intro equal
      have addressEq : address = otherAddress := wordEq address otherAddress equal
      subst otherAddress
      have locationEq := related.witnessWellFormed.locationInjective location other
        address mapped mappedOther
      exact otherNe locationEq.symm
    obtain ⟨otherHeader, otherHeaderRead, _, _, _⟩ :=
      related.descriptorRegion otherAddress otherDescriptor otherDescriptorFound
    have frame := related.allocationFrame_of_headerWrite_other targetFound
      otherDescriptorFound different oldRead otherHeaderRead resultEq headerInBounds
        written
    exact otherRelated.allocationFrame otherHeaderRead frame
  have promotedFrame : ∀ payload other,
      witness.promotedTags.Contains payload other →
      PromotedTagRel after witness payload other := by
    intro payload other promotedMapped
    have promoted := related.promoted payload other promotedMapped
    obtain ⟨promotedHeader, promotedHeaderRead, _, _, _, _, _, _⟩ :=
      promoted.header
    obtain ⟨_, promotedRawRead, _, _, _, _⟩ :=
      MemoryState.PrefixExtension.readLiveHeader_facts before other promotedHeader
        promotedHeaderRead
    have differentWord : address ≠ other :=
      related.witnessWellFormed.locationPromotionDisjoint location payload address
        other mapped promotedMapped
    have different : address.value ≠ other.value := by
      intro equal
      exact differentWord (wordEq address other equal)
    have frame := related.allocationFrame_of_headerWrite_other targetFound
      promoted.descriptor different oldRead promotedRawRead resultEq headerInBounds
        written
    exact promoted.allocationFrame promotedHeaderRead frame
  exact related.setCell_of_frames mapped found (by rw [resultEq]) finalValid targetRelated
    descriptorRegion descriptorDisjoint cellFrame promotedFrame

/-- Uniform ordinary-header facts needed to expose the exact common-header
write behind a live-cell ownership transition. -/
theorem LiveCellRel.ordinaryHeader
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) :
    ∃ header,
      state.readLiveHeader address = .ok header ∧
      Header.read state.memory address = .ok header ∧
      header.isPromotedTag = false ∧
      header.persistent = false ∧
      header.refCount.toNat = cell.rc := by
  cases related with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
        persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead
      have ordinary : cell.persistent = false :=
        (LiveCellRel.constructor descriptor objectEq objectRelated headerRead headerKind
          refCount persistent live).persistent_eq_false
      have headerOrdinary := persistent.trans ordinary
      have different : (ObjectKind.constructor == ObjectKind.natural) = false := by decide
      exact ⟨_, headerRead, rawRead, by
        simp [Header.isPromotedTag, headerKind, different], headerOrdinary, refCount⟩
  | boxed descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _
          objectRelated.headerRead
      have different : (ObjectKind.boxed == ObjectKind.natural) = false := by decide
      exact ⟨_, objectRelated.headerRead, rawRead, by
        simp [Header.isPromotedTag, objectRelated.headerKind, different],
        objectRelated.ordinary, refCount⟩
  | natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
        decoded refCount persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead
      exact ⟨_, headerRead, rawRead, by
        simp [Header.isPromotedTag, headerKind, ordinary], ordinary, refCount⟩

/-- Whole-heap source/concrete refinement for the nonrecursive decrement
branch. The target count changes, every other allocation is framed by the
descriptor disjointness invariant, and the semantic `setCell` update is
reassembled into `LiveHeapRel`. -/
theorem LiveHeapRel.decrementReferenceOnce_refines_above_one
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnce state address check = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, rawRead, notPromoted, ordinary, refCount⟩ :=
    targetRelated.ordinaryHeader
  obtain ⟨targetDescriptor, targetDescriptorFound⟩ := targetRelated.descriptor
  obtain ⟨result, updatedHeader, memory, writeOperation, updatedEq, resultEq,
      headerWrite, finalValid, headerAfter⟩ :=
    writeReferenceCount_header related.frontier headerRead targetRelated.headerOwned
      (UInt32.ofNat (cell.rc - 1))
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead).1
  have refCountNe : header.refCount ≠ 0 := by
    intro zero
    rw [zero] at refCount
    simp at refCount
    omega
  have operation : decrementReferenceOnce state address check = .ok result := by
    simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [ordinary])]
    rw [if_neg (by simpa using refCountNe)]
    rw [refCount, if_pos oneLt]
    simpa [updatedEq] using writeOperation
  obtain ⟨localResult, localOperation, _, targetAfter⟩ :=
    targetRelated.decrementReferenceOnce_above_one related.frontier oneLt check
  have localEq := Except.ok.inj (localOperation.symm.trans operation)
  subst localResult
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
  have sameExtent : updatedHeader.allocationBytes = header.allocationBytes := by
    simp [updatedEq]
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.descriptorSpatial_of_headerWrite targetDescriptorFound rawRead resultEq
      headerInBounds headerWrite sameExtent
  have wordEq : ∀ left right : Word32, left.value = right.value → left = right := by
    intro left right equal
    cases left
    cases right
    simp_all
  have cellFrame : ∀ other otherAddress otherCell,
      other ≠ location →
      findCell? runtime.heap other = some otherCell →
      witness.locations.lookup? other = some otherAddress →
      CellRel state witness otherAddress otherCell →
      CellRel result witness otherAddress otherCell := by
    intro other otherAddress otherCell otherNe foundOther mappedOther otherRelated
    obtain ⟨otherDescriptor, otherDescriptorFound⟩ := otherRelated.descriptor
    have different : address.value ≠ otherAddress.value := by
      intro equal
      have addressEq : address = otherAddress := wordEq address otherAddress equal
      subst otherAddress
      have locationEq := related.witnessWellFormed.locationInjective location other
        address mapped mappedOther
      exact otherNe locationEq.symm
    obtain ⟨otherHeader, otherHeaderRead, _, _, _⟩ :=
      related.descriptorRegion otherAddress otherDescriptor otherDescriptorFound
    have frame := related.allocationFrame_of_headerWrite_other targetDescriptorFound
      otherDescriptorFound different rawRead otherHeaderRead resultEq headerInBounds
        headerWrite
    exact otherRelated.allocationFrame otherHeaderRead frame
  have promotedFrame : ∀ payload other,
      witness.promotedTags.Contains payload other →
      PromotedTagRel result witness payload other := by
    intro payload other promotedMapped
    have promoted := related.promoted payload other promotedMapped
    obtain ⟨promotedHeader, promotedHeaderRead, _, _, _, _, _, _⟩ :=
      promoted.header
    obtain ⟨_, promotedRawRead, _, _, _, _⟩ :=
      MemoryState.PrefixExtension.readLiveHeader_facts state other promotedHeader
        promotedHeaderRead
    have differentWord : address ≠ other :=
      related.witnessWellFormed.locationPromotionDisjoint location payload address
        other mapped promotedMapped
    have different : address.value ≠ other.value := by
      intro equal
      exact differentWord (wordEq address other equal)
    have frame := related.allocationFrame_of_headerWrite_other targetDescriptorFound
      promoted.descriptor different rawRead promotedRawRead resultEq headerInBounds
        headerWrite
    exact promoted.allocationFrame promotedHeaderRead frame
  obtain ⟨nextRuntime, semanticUpdate, finalRelated⟩ :=
    related.setCell_of_frames mapped found (by rw [resultEq]) finalValid
      (.live targetAfter)
      descriptorRegion descriptorDisjoint cellFrame promotedFrame
  have semanticEq := targetRelated.decValueOnce_above_one_eq runtime location found
    oneLt check
  exact ⟨result, nextRuntime, operation, by rw [semanticEq, semanticUpdate],
    finalRelated⟩

/-- Whole-heap source/concrete refinement for count-one boxes and heap
naturals. The concrete allocation becomes a canonical dead cell, every
disjoint allocation is framed, and the semantic heap records the matching
zero-count/dead replacement. -/
theorem LiveHeapRel.decrementReferenceOnce_refines_leaf_one
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (one : cell.rc = 1) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnce state address check = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨targetDescriptor, targetDescriptorFound⟩ := targetRelated.descriptor
  obtain ⟨result, header, memory, operation, headerRead, resultEq, headerWrite,
      finalValid, deadRelated⟩ :=
    targetRelated.decrementReferenceOnce_leaf_one leafCell related.frontier one check
  obtain ⟨_, rawRead, _, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
  have sameExtent : header.forRelease.allocationBytes = header.allocationBytes := by
    rfl
  let replacement : HeapCell := { cell with rc := 0, live := false }
  have targetAfter : CellRel result witness address replacement :=
    .dead (by simp [replacement]) (by simp [replacement])
      ⟨targetDescriptor, targetDescriptorFound⟩ deadRelated
  obtain ⟨nextRuntime, semanticUpdate, finalRelated⟩ :=
    related.setCell_of_headerWrite mapped found targetDescriptorFound rawRead
      resultEq headerInBounds headerWrite sameExtent finalValid targetAfter
  have semanticEq := targetRelated.decValueOnce_leaf_one_eq leafCell runtime location
    found one check
  exact ⟨result, nextRuntime, operation,
    by rw [semanticEq, show { cell with rc := 0, live := false } = replacement by rfl,
      semanticUpdate], finalRelated⟩

/-- The established whole-heap above-one refinement is valid at every
positive explicit fuel budget, not only the two public derived budgets. -/
theorem LiveHeapRel.decrementReferenceOnceFuel_refines_above_one
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (oneLt : 1 < cell.rc) (fuel : Nat) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnceFuel (fuel + 1) state address check = .ok result ∧
      Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, ordinary, refCount⟩ :=
    targetRelated.ordinaryHeader
  obtain ⟨result, nextRuntime, concretePublic, semanticPublic, finalRelated⟩ :=
    related.decrementReferenceOnce_refines_above_one mapped found live oneLt check
  have concreteEq :=
    Fir.Wasm.Concrete.decrementReferenceOnceFuel_above_one_eq_public headerRead
      notPromoted ordinary cell.rc refCount oneLt fuel check
  have semanticFuelEq :=
    targetRelated.decLocationFuel_above_one_eq runtime location found oneLt fuel
  have semanticPublicEq :=
    targetRelated.decValueOnce_above_one_eq runtime location found oneLt check
  exact ⟨result, nextRuntime, by rw [concreteEq]; exact concretePublic, by
    rw [semanticFuelEq, ← semanticPublicEq]
    exact semanticPublic, finalRelated⟩

/-- The whole-heap box/natural leaf refinement is likewise valid for every
positive explicit fuel budget. -/
theorem LiveHeapRel.decrementReferenceOnceFuel_refines_leaf_one
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (one : cell.rc = 1) (fuel : Nat) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnceFuel (fuel + 1) state address check = .ok result ∧
      Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨result, nextRuntime, concretePublic, semanticPublic, finalRelated⟩ :=
    related.decrementReferenceOnce_refines_leaf_one mapped found live leafCell one check
  have concreteEq :=
    targetRelated.decrementReferenceOnceFuel_leaf_one_eq_public leafCell one fuel check
  have semanticFuelEq :=
    targetRelated.decLocationFuel_leaf_one_eq leafCell runtime location found one fuel
  have semanticPublicEq :=
    targetRelated.decValueOnce_leaf_one_eq leafCell runtime location found one check
  exact ⟨result, nextRuntime, by rw [concreteEq]; exact concretePublic, by
    rw [semanticFuelEq, ← semanticPublicEq]
    exact semanticPublic, finalRelated⟩

end Fir.Wasm.Concrete
