import Fir.Wasm.Concrete.ReferenceCountCorrectness
import Fir.Wasm.Concrete.ClosureOwnershipCorrectness

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

/-- A complete physical-allocation frame also frames every smaller logical
prefix rooted at the same address. -/
theorem MemoryState.AllocationFrame.shrink
    {before after : MemoryState} {address : Word32} {large small : Nat}
    (frame : before.AllocationFrame after address large)
    (fits : small ≤ large) :
    before.AllocationFrame after address small := by
  exact ⟨frame.cursor, frame.memorySize,
    fun offset within => frame.readByte offset (Nat.lt_of_lt_of_le within fits)⟩

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

/-- A checked constructor object-field writer produces a complete allocation
frame for every allocation disjoint from the target's retained physical
extent. -/
theorem MemoryState.AllocationFrame.ofWriteObjectFields
    {before after : MemoryState} {target other : Word32}
    {targetBytes otherBytes : Nat} {fields : List Word32}
    {memory : LinearMemory}
    (resultEq : after = { before with memory })
    (targetInBounds : target.value + targetBytes ≤ before.memory.size)
    (fieldsInTarget : objectFieldAddress target.value fields.length ≤
      target.value + targetBytes)
    (written : writeObjectFields before.memory target.value 0 fields =
      .ok memory)
    (disjoint : target.value + targetBytes ≤ other.value ∨
      other.value + otherBytes ≤ target.value) :
    before.AllocationFrame after other otherBytes := by
  have fieldsInBounds :
      objectFieldAddress target.value (0 + fields.length) ≤
        before.memory.size := by
    simp only [Nat.zero_add]
    exact Nat.le_trans fieldsInTarget targetInBounds
  have post := writeObjectFields_post before.memory memory target.value 0 fields
    fieldsInBounds written
  subst after
  refine ⟨rfl, post.size, ?_⟩
  intro offset offsetWithin
  change memory.readByte (other.value + offset) =
    before.memory.readByte (other.value + offset)
  apply post.byteFrame
  rcases disjoint with targetBefore | otherBefore
  · right
    simp only [Nat.zero_add]
    exact Nat.le_trans fieldsInTarget (by omega)
  · left
    simp [objectFieldAddress, Fir.Wasm.Concrete.target]
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

/-- The global descriptor invariant discharges the retained-extent premises
needed to frame any non-target allocation through a bulk object-field write. -/
theorem LiveHeapRel.allocationFrame_of_writeObjectFields_other
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress otherAddress : Word32}
    {targetDescriptor otherDescriptor : AllocationDescriptor}
    {targetHeader otherHeader : Header} {fields : List Word32}
    {memory : LinearMemory}
    (related : LiveHeapRel before witness runtime)
    (targetFound : witness.descriptors.lookup? targetAddress =
      some targetDescriptor)
    (otherFound : witness.descriptors.lookup? otherAddress =
      some otherDescriptor)
    (different : targetAddress.value ≠ otherAddress.value)
    (targetRead : Header.read before.memory targetAddress = .ok targetHeader)
    (otherRead : Header.read before.memory otherAddress = .ok otherHeader)
    (resultEq : after = { before with memory })
    (fieldsInTarget : objectFieldAddress targetAddress.value fields.length ≤
      targetAddress.value + targetHeader.allocationBytes.toNat)
    (written : writeObjectFields before.memory targetAddress.value 0 fields =
      .ok memory) :
    before.AllocationFrame after otherAddress
      otherHeader.allocationBytes.toNat := by
  obtain ⟨regionHeader, regionRead, _, _, targetExtent⟩ :=
    related.descriptorRegion targetAddress targetDescriptor targetFound
  rw [targetRead] at regionRead
  have headerEq := Except.ok.inj regionRead
  subst regionHeader
  have targetInBounds :
      targetAddress.value + targetHeader.allocationBytes.toNat ≤
        before.memory.size :=
    Nat.le_trans targetExtent related.frontier.cursorInBounds
  have disjoint := related.descriptorDisjoint targetAddress otherAddress
    targetDescriptor otherDescriptor targetFound otherFound different
      targetHeader otherHeader targetRead otherRead
  exact .ofWriteObjectFields resultEq targetInBounds fieldsInTarget written disjoint

/-- A same-extent header update preserves the retained allocation word of
every mapped semantic location. The target uses the updated header directly;
descriptor disjointness frames every other mapped allocation. -/
theorem LiveHeapRel.mappedHeaderCapacity_of_headerWrite
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress : Word32}
    {targetDescriptor : AllocationDescriptor}
    {oldHeader updatedHeader : Header} {memory : LinearMemory}
    (related : LiveHeapRel before witness runtime)
    (targetFound :
      witness.descriptors.lookup? targetAddress = some targetDescriptor)
    (oldRead : Header.read before.memory targetAddress = .ok oldHeader)
    (resultEq : after = { before with memory })
    (headerInBounds :
      targetAddress.value + headerBytes ≤ before.memory.size)
    (written : updatedHeader.write before.memory targetAddress = .ok memory)
    (sameExtent :
      updatedHeader.allocationBytes = oldHeader.allocationBytes) :
    MappedHeaderCapacityTransport before after witness := by
  intro address location header mapped headerRead owned
  obtain ⟨cell, _, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
  obtain ⟨descriptor, descriptorFound⟩ := cellRelated.descriptor
  by_cases different : targetAddress.value ≠ address.value
  · obtain ⟨regionHeader, regionRead, minimum, _, _⟩ :=
      related.descriptorRegion address descriptor descriptorFound
    rw [headerRead] at regionRead
    have regionHeaderEq := Except.ok.inj regionRead
    subst regionHeader
    have frame := related.allocationFrame_of_headerWrite_other targetFound
      descriptorFound different oldRead headerRead resultEq headerInBounds
      written
    refine ⟨header, ?_, rfl, ?_⟩
    · rw [frame.readHeaderRaw minimum]
      exact headerRead
    · rw [frame.cursor]
      exact owned
  · have sameValue : targetAddress.value = address.value := by omega
    have sameAddress : targetAddress = address := by
      cases targetAddress
      cases address
      simp_all
    subst address
    rw [oldRead] at headerRead
    have headerEq := Except.ok.inj headerRead
    subst header
    refine ⟨updatedHeader, ?_, sameExtent, ?_⟩
    · rw [resultEq]
      exact Header.read_of_write_eq_ok before.memory memory targetAddress
        updatedHeader headerInBounds written
    · simpa [resultEq] using owned

/-- A bounded constructor-field write leaves every mapped allocation header
unchanged. The target header lies before its payload; all other headers are
framed by descriptor disjointness. -/
theorem LiveHeapRel.mappedHeaderCapacity_of_writeObjectFields
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress : Word32}
    {targetDescriptor : AllocationDescriptor} {targetHeader : Header}
    {fields : List Word32} {memory : LinearMemory}
    (related : LiveHeapRel before witness runtime)
    (targetFound :
      witness.descriptors.lookup? targetAddress = some targetDescriptor)
    (targetRead :
      Header.read before.memory targetAddress = .ok targetHeader)
    (resultEq : after = { before with memory })
    (fieldsInTarget :
      objectFieldAddress targetAddress.value fields.length ≤
        targetAddress.value + targetHeader.allocationBytes.toNat)
    (written :
      writeObjectFields before.memory targetAddress.value 0 fields =
        .ok memory) :
    MappedHeaderCapacityTransport before after witness := by
  obtain ⟨regionHeader, regionRead, _, _, targetExtent⟩ :=
    related.descriptorRegion targetAddress targetDescriptor targetFound
  rw [targetRead] at regionRead
  have regionHeaderEq := Except.ok.inj regionRead
  subst regionHeader
  have targetInBounds :
      targetAddress.value + targetHeader.allocationBytes.toNat ≤
        before.memory.size :=
    Nat.le_trans targetExtent related.frontier.cursorInBounds
  have fieldsInBounds :
      objectFieldAddress targetAddress.value (0 + fields.length) ≤
        before.memory.size := by
    simp only [Nat.zero_add]
    exact Nat.le_trans fieldsInTarget targetInBounds
  have post := writeObjectFields_post before.memory memory targetAddress.value 0
    fields fieldsInBounds written
  intro address location header mapped headerRead owned
  obtain ⟨cell, _, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
  obtain ⟨descriptor, descriptorFound⟩ := cellRelated.descriptor
  by_cases different : targetAddress.value ≠ address.value
  · obtain ⟨mappedHeader, mappedRead, minimum, _, _⟩ :=
      related.descriptorRegion address descriptor descriptorFound
    rw [headerRead] at mappedRead
    have mappedHeaderEq := Except.ok.inj mappedRead
    subst mappedHeader
    have frame := related.allocationFrame_of_writeObjectFields_other targetFound
      descriptorFound different targetRead headerRead resultEq fieldsInTarget
      written
    refine ⟨header, ?_, rfl, ?_⟩
    · rw [frame.readHeaderRaw minimum]
      exact headerRead
    · rw [frame.cursor]
      exact owned
  · have sameValue : targetAddress.value = address.value := by omega
    have sameAddress : targetAddress = address := by
      cases targetAddress
      cases address
      simp_all
    subst address
    rw [targetRead] at headerRead
    have headerEq := Except.ok.inj headerRead
    subst header
    refine ⟨targetHeader, ?_, rfl, ?_⟩
    · rw [resultEq]
      rw [Header.read_of_writeObjectFields before.memory memory targetAddress
        0 fields post]
      exact targetRead
    · simpa [resultEq] using owned

/-- A bounded bulk object-field write preserves every descriptor's complete
physical region and the pairwise allocation-disjointness invariant. -/
theorem LiveHeapRel.descriptorSpatial_of_writeObjectFields
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress : Word32}
    {targetDescriptor : AllocationDescriptor} {targetHeader : Header}
    {fields : List Word32} {memory : LinearMemory}
    (related : LiveHeapRel before witness runtime)
    (targetFound : witness.descriptors.lookup? targetAddress =
      some targetDescriptor)
    (targetRead : Header.read before.memory targetAddress = .ok targetHeader)
    (resultEq : after = { before with memory })
    (fieldsInTarget : objectFieldAddress targetAddress.value fields.length ≤
      targetAddress.value + targetHeader.allocationBytes.toNat)
    (written : writeObjectFields before.memory targetAddress.value 0 fields =
      .ok memory) :
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
  rw [targetRead] at regionRead
  have regionHeaderEq := Except.ok.inj regionRead
  subst regionHeader
  have targetInBounds :
      targetAddress.value + targetHeader.allocationBytes.toNat ≤
        before.memory.size :=
    Nat.le_trans targetExtent related.frontier.cursorInBounds
  have fieldsInBounds : objectFieldAddress targetAddress.value
      (0 + fields.length) ≤ before.memory.size := by
    simp only [Nat.zero_add]
    exact Nat.le_trans fieldsInTarget targetInBounds
  have post := writeObjectFields_post before.memory memory targetAddress.value 0
    fields fieldsInBounds written
  have targetReadAfter :
      Header.read after.memory targetAddress = .ok targetHeader := by
    rw [resultEq]
    dsimp only
    rw [Header.read_of_writeObjectFields before.memory memory targetAddress 0
      fields post]
    exact targetRead
  refine ⟨?_, ?_⟩
  · intro address descriptor found
    by_cases isTarget : targetAddress.value = address.value
    · have addressEq : address = targetAddress :=
        wordEq address targetAddress isTarget.symm
      subst address
      exact ⟨targetHeader, targetReadAfter, targetMinimum, targetAligned, by
        rw [resultEq]
        exact targetExtent⟩
    · obtain ⟨header, headerRead, minimum, aligned, extent⟩ :=
        related.descriptorRegion address descriptor found
      have frame := related.allocationFrame_of_writeObjectFields_other targetFound
        found isTarget targetRead headerRead resultEq fieldsInTarget written
      exact ⟨header, by rw [frame.readHeaderRaw minimum]; exact headerRead,
        minimum, aligned, by rw [frame.cursor]; exact extent⟩
  · intro left right leftDescriptor rightDescriptor leftFound rightFound different
      leftHeader rightHeader leftRead rightRead
    by_cases leftTarget : targetAddress.value = left.value
    · by_cases rightTarget : targetAddress.value = right.value
      · exact False.elim (different (leftTarget.symm.trans rightTarget))
      · have leftEq : left = targetAddress :=
          wordEq left targetAddress leftTarget.symm
        subst left
        rw [targetReadAfter] at leftRead
        have leftHeaderEq := Except.ok.inj leftRead
        subst leftHeader
        obtain ⟨oldRightHeader, oldRightRead, rightMinimum, _, _⟩ :=
          related.descriptorRegion right rightDescriptor rightFound
        have frame := related.allocationFrame_of_writeObjectFields_other
          targetFound rightFound rightTarget targetRead oldRightRead resultEq
            fieldsInTarget written
        rw [frame.readHeaderRaw rightMinimum] at rightRead
        exact related.descriptorDisjoint targetAddress right targetDescriptor
          rightDescriptor targetFound rightFound rightTarget targetHeader rightHeader
            targetRead rightRead
    · by_cases rightTarget : targetAddress.value = right.value
      · have rightEq : right = targetAddress :=
          wordEq right targetAddress rightTarget.symm
        subst right
        rw [targetReadAfter] at rightRead
        have rightHeaderEq := Except.ok.inj rightRead
        subst rightHeader
        obtain ⟨oldLeftHeader, oldLeftRead, leftMinimum, _, _⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        have frame := related.allocationFrame_of_writeObjectFields_other
          targetFound leftFound leftTarget targetRead oldLeftRead resultEq
            fieldsInTarget written
        rw [frame.readHeaderRaw leftMinimum] at leftRead
        exact related.descriptorDisjoint left targetAddress leftDescriptor
          targetDescriptor leftFound targetFound (Ne.symm leftTarget) leftHeader
            targetHeader leftRead targetRead
      · obtain ⟨oldLeftHeader, oldLeftRead, leftMinimum, _, _⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        obtain ⟨oldRightHeader, oldRightRead, rightMinimum, _, _⟩ :=
          related.descriptorRegion right rightDescriptor rightFound
        have leftFrame := related.allocationFrame_of_writeObjectFields_other
          targetFound leftFound leftTarget targetRead oldLeftRead resultEq
            fieldsInTarget written
        have rightFrame := related.allocationFrame_of_writeObjectFields_other
          targetFound rightFound rightTarget targetRead oldRightRead resultEq
            fieldsInTarget written
        rw [leftFrame.readHeaderRaw leftMinimum] at leftRead
        rw [rightFrame.readHeaderRaw rightMinimum] at rightRead
        exact related.descriptorDisjoint left right leftDescriptor rightDescriptor
          leftFound rightFound different leftHeader rightHeader leftRead rightRead

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

/-- A complete allocation frame preserves the checked closure-header decoder.
The decoder has no payload observations beyond the common header. -/
theorem MemoryState.AllocationFrame.readClosureHeader
    {before after : MemoryState} {address : Word32} {bytes : Nat}
    (frame : before.AllocationFrame after address bytes)
    (minimum : headerBytes ≤ bytes) :
    Fir.Wasm.Concrete.readClosureHeader after address =
      Fir.Wasm.Concrete.readClosureHeader before address := by
  unfold Fir.Wasm.Concrete.readClosureHeader
  rw [frame.readLiveHeader minimum]

/-- Closure metadata adds only immutable module-table lookups to the framed
checked header, so it transports through the same complete allocation frame. -/
theorem MemoryState.AllocationFrame.readClosureMetadata
    {before after : MemoryState} {address : Word32} {bytes : Nat}
    (frame : before.AllocationFrame after address bytes)
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (minimum : headerBytes ≤ bytes) :
    Fir.Wasm.Concrete.readClosureMetadata after dispatch descriptors address =
      Fir.Wasm.Concrete.readClosureMetadata before dispatch descriptors address := by
  unfold Fir.Wasm.Concrete.readClosureMetadata
  rw [frame.readClosureHeader minimum]

/-- Every observation made by a locally related closure stays inside its
declared complete allocation, so a complete frame preserves the decoder. -/
theorem ClosureObjectRel.allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32} {bytes : Nat}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {semantic : Array Value}
    (related : ClosureObjectRel before witness dispatch descriptors address
      function arity captureKinds semantic)
    (frame : before.AllocationFrame after address bytes)
    (minimum : headerBytes ≤ bytes)
    (capturesFit : headerBytes + target.semanticSlotBytes * semantic.size ≤ bytes) :
    ClosureObjectRel after witness dispatch descriptors address function arity
      captureKinds semantic := by
  refine {
    descriptor := related.descriptor
    metadata := ?_
    captureKindsSize := related.captureKindsSize
    captures := ?_ }
  · obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
        metadataFixed, metadataKinds⟩ := related.metadata
    exact ⟨metadata, by
      rw [frame.readClosureMetadata dispatch descriptors minimum]
      exact metadataRead,
      metadataFunction, metadataArity, metadataFixed, metadataKinds⟩
  · intro index kind value kindAt valueAt
    obtain ⟨lane, readBefore, laneRelated⟩ :=
      related.captures index kind value kindAt valueAt
    obtain ⟨indexLt, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
    have slotFits : headerBytes + target.semanticSlotBytes * index + 8 ≤ bytes := by
      simp [target] at capturesFit ⊢
      omega
    refine ⟨lane, ?_, laneRelated⟩
    rw [LinearMemory.readClosureCapture_of_byteFrame
      before.memory after.memory (closureCaptureAddress address.value index) kind]
    · exact readBefore
    · intro offset offsetLt
      change after.memory.readByte
          (address.value + headerBytes + target.semanticSlotBytes * index + offset) =
        before.memory.readByte
          (address.value + headerBytes + target.semanticSlotBytes * index + offset)
      rw [show address.value + headerBytes + target.semanticSlotBytes * index + offset =
          address.value +
            (headerBytes + target.semanticSlotBytes * index + offset) by omega]
      exact frame.readByte _ (by omega)

/-- A complete descriptor-allocation frame preserves the packaged semantic
closure cell, including its module metadata and every typed capture. -/
theorem ClosureCellRel.allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell} {regionHeader : Header}
    (related : ClosureCellRel before witness address cell)
    (headerRead : Header.read before.memory address = .ok regionHeader)
    (frame : before.AllocationFrame after address
      regionHeader.allocationBytes.toNat) :
    ClosureCellRel after witness address cell := by
  cases related with
  | @closure function arity captureKinds captures actualHeader _ objectEq
      objectRelated liveHeaderRead headerKind descriptorLookup fixedCount
      extent refCount persistent live =>
      obtain ⟨heap, rawRead, _, minimum, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          liveHeaderRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      have requiredFits :
          align8 (headerBytes +
            target.semanticSlotBytes * actualHeader.aux2.toNat) ≤
              actualHeader.allocationBytes.toNat := by
        obtain ⟨metadata, metadataRead, _, _, _, _⟩ := objectRelated.metadata
        have closureHeaderSuccess : ∃ decoded,
            Fir.Wasm.Concrete.readClosureHeader before address = .ok decoded := by
          cases result : Fir.Wasm.Concrete.readClosureHeader before address with
          | error failure =>
              unfold Fir.Wasm.Concrete.readClosureMetadata at metadataRead
              simp only [result, Bind.bind, Except.bind] at metadataRead
              contradiction
          | ok decoded => exact ⟨decoded, rfl⟩
        obtain ⟨decoded, decodedRead⟩ := closureHeaderSuccess
        have check := decodedRead
        unfold Fir.Wasm.Concrete.readClosureHeader at check
        simp only [heap, if_true] at check
        rw [liveHeaderRead] at check
        simp only [liftMemory, Bind.bind, Except.bind] at check
        have kindCheck : (actualHeader.kind == ObjectKind.closure) = true := by
          rw [headerKind]
          decide
        rw [kindCheck] at check
        simp only [if_true] at check
        split at check
        · rename_i valid
          have validProp : actualHeader.aux2.toNat < actualHeader.aux1.toNat ∧
              align8 (headerBytes +
                target.semanticSlotBytes * actualHeader.aux2.toNat) ≤
                  actualHeader.allocationBytes.toNat := by
            simpa using valid
          exact validProp.2
        · contradiction
      have capturesFit :
          headerBytes + target.semanticSlotBytes * captures.size ≤
            actualHeader.allocationBytes.toNat := by
        rw [← fixedCount]
        exact Nat.le_trans (align8_ge _) requiredFits
      have headerAfter : after.readLiveHeader address = .ok actualHeader := by
        rw [frame.readLiveHeader minimum]
        exact liveHeaderRead
      exact .closure objectEq
        (objectRelated.allocationFrame frame minimum capturesFit)
        headerAfter headerKind descriptorLookup fixedCount
        (by rw [frame.cursor]; exact extent) refCount persistent live

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

theorem MemoryState.AllocationFrame.readInteger_eq
    {before after : MemoryState} {address : Word32} {header : Header}
    (frame : before.AllocationFrame after address header.allocationBytes.toNat)
    (headerRead : before.readLiveHeader address = .ok header)
    (limbsFit : headerBytes +
      target.semanticSlotBytes * header.aux1.toNat ≤
        header.allocationBytes.toNat) :
    Fir.Wasm.Concrete.readInteger after address =
      Fir.Wasm.Concrete.readInteger before address := by
  obtain ⟨heap, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header headerRead
  have headerAfter : after.readLiveHeader address = .ok header := by
    rw [frame.readLiveHeader minimum]
    exact headerRead
  unfold Fir.Wasm.Concrete.readInteger
  rw [heap]
  simp only
  rw [headerAfter, headerRead]
  simp only [liftMemory, Bind.bind, Except.bind]
  rw [frame.readNaturalLimbs 0 header.aux1.toNat (by simpa using limbsFit)]

/-- A raw UTF-8 byte decoder is stable when its complete payload lies inside
the framed allocation. -/
theorem MemoryState.AllocationFrame.readStringBytes
    {before after : MemoryState} {address : Word32} {bytes : Nat}
    (frame : before.AllocationFrame after address bytes)
    (index count : Nat) (owned : headerBytes + index + count ≤ bytes) :
    Fir.Wasm.Concrete.readStringBytes after.memory address.value index count =
      Fir.Wasm.Concrete.readStringBytes before.memory address.value index count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      unfold Fir.Wasm.Concrete.readStringBytes
      rw [show address.value + headerBytes + index =
        address.value + (headerBytes + index) by omega]
      rw [frame.readByte (headerBytes + index) (by omega)]
      rw [ih (index + 1) (by omega)]

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
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header.choose_spec
  change before.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header headerRead
  have layoutMinimum : headerBytes ≤
      (ConstructorLayout.ofInfo info).allocationBytes := by
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
        info.ssize)
    simpa [ConstructorLayout.ofInfo, target] using
      Nat.le_trans (by omega : headerBytes ≤
        headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
          info.ssize) aligned
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
          readScalarUInt64Field after address field.width field.offset = .ok value
      | .float32Bits bits =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field after address field.width field.offset = .ok bits
      | .float64Bits bits =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field after address field.width field.offset = .ok bits := by
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
    | float32Bits bits =>
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
    | float64Bits bits =>
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
    header := ⟨header, headerAfter, headerKind, allocationBytes,
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
    allocationBytes := related.allocationBytes
    kindCode := related.kindCode
    payloadBytes := related.payloadBytes
    reserved2 := related.reserved2
    reserved3 := related.reserved3
    headerOwned := by rw [frame.cursor]; exact related.headerOwned
    extent := by rw [frame.cursor]; exact related.extent
    decoded := by rw [decoderEq]; exact related.decoded }

/-- A complete heap-integer allocation frame preserves its header metadata,
sign-magnitude limbs, and exact checked decoder. -/
theorem IntegerObjectRel.allocationFrame
    {before after : MemoryState} {address : Word32} {value : Int}
    {header : Header} (related : IntegerObjectRel before address value header)
    (frame : before.AllocationFrame after address header.allocationBytes.toNat) :
    IntegerObjectRel after address value header := by
  obtain ⟨_, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header
      related.headerRead
  have headerAfter : after.readLiveHeader address = .ok header := by
    rw [frame.readLiveHeader minimum]
    exact related.headerRead
  have limbsFit : headerBytes +
      target.semanticSlotBytes * header.aux1.toNat ≤
        header.allocationBytes.toNat := by
    rw [related.limbCount, related.allocationBytes]
    exact align8_ge _
  have decoderEq := frame.readInteger_eq related.headerRead limbsFit
  exact {
    headerRead := headerAfter
    headerKind := related.headerKind
    marker := related.marker
    limbCount := related.limbCount
    sign := related.sign
    reserved := related.reserved
    allocationBytes := related.allocationBytes
    extent := by rw [frame.cursor]; exact related.extent
    decoded := by rw [decoderEq]; exact related.decoded }

/-- A complete string allocation decoder is stable when every byte in its
region is framed. -/
theorem StringObjectRel.allocationFrame
    {before after : MemoryState} {address : Word32} {value : String}
    {header : Header} (related : StringObjectRel before address value header)
    (frame : before.AllocationFrame after address header.allocationBytes.toNat) :
    StringObjectRel after address value header := by
  obtain ⟨_, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header
      related.headerRead
  have headerAfter : after.readLiveHeader address = .ok header := by
    rw [frame.readLiveHeader minimum]
    exact related.headerRead
  have decoderEq := frame.readStringBytes 0 header.aux1.toNat
    (by simpa using related.bytesFit)
  exact {
    headerRead := headerAfter
    headerKind := related.headerKind
    marker := related.marker
    byteCount := related.byteCount
    reserved2 := related.reserved2
    reserved3 := related.reserved3
    allocationBytes := related.allocationBytes
    headerOwned := by rw [frame.cursor]; exact related.headerOwned
    extent := by rw [frame.cursor]; exact related.extent
    bytesFit := related.bytesFit
    rawDecoded := by rw [decoderEq]; exact related.rawDecoded }

/-- Boxes, heap naturals, heap integers, and strings are the nonrecursive live ownership
representations. A complete allocation frame preserves their `LiveCellRel`. -/
theorem LiveCellRel.leaf_allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell} {regionHeader : Header}
    (related : LiveCellRel before witness address cell)
    (leafCell : NonrecursiveCell cell)
    (headerRead : Header.read before.memory address = .ok regionHeader)
    (frame : before.AllocationFrame after address
      regionHeader.allocationBytes.toNat) :
    LiveCellRel after witness address cell := by
  cases related with
  | constructor descriptor objectEq objectRelated liveHeaderRead headerKind refCount
        persistent live =>
      rcases leafCell with ((boxedCell | naturalCell) | stringCell) | integerCell
      · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
      · obtain ⟨value, naturalEq⟩ := naturalCell
        rw [objectEq] at naturalEq
        contradiction
      · obtain ⟨value, stringEq⟩ := stringCell
        rw [objectEq] at stringEq
        contradiction
      · obtain ⟨value, integerEq⟩ := integerCell
        rw [objectEq] at integerEq
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
  | @natural value actualHeader _ descriptor objectEq liveHeaderRead headerKind
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
      exact .natural descriptor objectEq headerAfter headerKind marker
        (by rw [frame.cursor]; exact extent) limbsFit
        (by rw [frame.readNatural_eq liveHeaderRead limbsFit]; exact decoded)
        refCount persistent live
  | @integer value actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          objectRelated.headerRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      exact .integer descriptor objectEq (objectRelated.allocationFrame frame)
        refCount persistent live
  | @string value actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          objectRelated.headerRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      exact .string descriptor objectEq (objectRelated.allocationFrame frame)
        refCount persistent live
  | closure closureRelated =>
      obtain ⟨function, arity, captures, closureEq⟩ := closureRelated.objectEq
      rcases leafCell with ((boxedCell | naturalCell) | stringCell) | integerCell
      · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [closureEq] at boxedEq
        contradiction
      · obtain ⟨value, naturalEq⟩ := naturalCell
        rw [closureEq] at naturalEq
        contradiction
      · obtain ⟨value, stringEq⟩ := stringCell
        rw [closureEq] at stringEq
        contradiction
      · obtain ⟨value, integerEq⟩ := integerCell
        rw [closureEq] at integerEq
        contradiction

/-- Whole cells whose live branch is nonrecursive transport across a complete
allocation frame; dead branches require only their canonical raw header. -/
theorem CellRel.leaf_allocationFrame
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell} {header : Header}
    (related : CellRel before witness address cell)
    (leafCell : cell.live = true → NonrecursiveCell cell)
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
      obtain ⟨objectHeader, objectHeaderRead, _, allocationBytes, _, _, _, _⟩ :=
        objectRelated.header
      rw [liveHeaderRead] at objectHeaderRead
      have objectHeaderEq := Except.ok.inj objectHeaderRead
      subst objectHeader
      have objectFrame : before.AllocationFrame after address
          (ConstructorLayout.ofInfo info).allocationBytes := by
        exact frame.shrink allocationBytes
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
  | @natural value actualHeader _ descriptor objectEq liveHeaderRead headerKind
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
      exact .natural descriptor objectEq headerAfter headerKind marker
        (by rw [frame.cursor]; exact extent) limbsFit
        (by rw [frame.readNatural_eq liveHeaderRead limbsFit]; exact decoded)
        refCount persistent live
  | @integer value actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          objectRelated.headerRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      exact .integer descriptor objectEq (objectRelated.allocationFrame frame)
        refCount persistent live
  | @string value actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address actualHeader
          objectRelated.headerRead
      rw [headerRead] at rawRead
      have headerEq := Except.ok.inj rawRead
      subst regionHeader
      exact .string descriptor objectEq (objectRelated.allocationFrame frame)
        refCount persistent live
  | closure closureRelated =>
      exact .closure (closureRelated.allocationFrame headerRead frame)

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

/-- Uniform live-header facts needed to select the concrete ownership branch.
The persistent bit remains related to the semantic cell instead of being
silently restricted to ordinary objects. -/
theorem LiveCellRel.ownershipHeader
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) :
    ∃ header,
      state.readLiveHeader address = .ok header ∧
      Header.read state.memory address = .ok header ∧
      header.isPromotedTag = false ∧
      header.persistent = cell.persistent ∧
      header.refCount.toNat = cell.rc := by
  cases related with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
        persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead
      have different : (ObjectKind.constructor == ObjectKind.natural) = false := by decide
      exact ⟨_, headerRead, rawRead, by
        simp [Header.isPromotedTag, headerKind, different], persistent, refCount⟩
  | boxed descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _
          objectRelated.headerRead
      have different : (ObjectKind.boxed == ObjectKind.natural) = false := by decide
      exact ⟨_, objectRelated.headerRead, rawRead, by
        simp [Header.isPromotedTag, objectRelated.headerKind, different],
        persistent, refCount⟩
  | natural descriptor objectEq headerRead headerKind marker extent limbsFit
        decoded refCount persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead
      exact ⟨_, headerRead, rawRead, by
        simp [Header.isPromotedTag, headerKind, marker, bigNaturalMarker,
          promotedTagMarker], persistent, refCount⟩
  | integer descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _
          objectRelated.headerRead
      have different : (ObjectKind.integer == ObjectKind.natural) = false := by decide
      exact ⟨_, objectRelated.headerRead, rawRead, by
        simp [Header.isPromotedTag, objectRelated.headerKind, different],
        persistent, refCount⟩
  | string descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨_, rawRead, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address _
          objectRelated.headerRead
      have different : (ObjectKind.string == ObjectKind.natural) = false := by decide
      exact ⟨_, objectRelated.headerRead, rawRead, by
        simp [Header.isPromotedTag, objectRelated.headerKind, different],
        persistent, refCount⟩
  | closure closureRelated =>
      cases closureRelated with
      | closure objectEq objectRelated headerRead headerKind descriptorLookup
          fixedCount extent refCount persistent live =>
          obtain ⟨_, rawRead, _, _, _, _⟩ :=
            MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead
          have different : (ObjectKind.closure == ObjectKind.natural) = false := by
            decide
          exact ⟨_, headerRead, rawRead, by
            simp [Header.isPromotedTag, headerKind, different], persistent, refCount⟩

/-- A stale mapped allocation rejects increment before reference-count
arithmetic or a header write. -/
theorem DeadCellRel.incrementReference_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (amount : Nat) (check : Bool) :
    Fir.Wasm.Concrete.incrementReference state address amount check =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨_, _, addressHeap, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    related.header
  unfold Fir.Wasm.Concrete.incrementReference
  rw [addressHeap]
  simp only
  rw [related.readLiveHeader_eq]
  rfl

/-- Every fuel branch of one stale decrement rejects at the released-header
read, before fuel, reference-count, descriptor, or child processing. -/
theorem DeadCellRel.decrementReferenceOnceFuel_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (fuel : Nat) (check : Bool)
    (descriptors : ClosureDescriptorTable := #[]) :
    decrementReferenceOnceFuel fuel state address check descriptors =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨_, _, addressHeap, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    related.header
  cases fuel <;> simp only [decrementReferenceOnceFuel] <;>
    rw [addressHeap, related.readLiveHeader_eq] <;> rfl

/-- The public one-step stale decrement inherits the fuel-indexed boundary. -/
theorem DeadCellRel.decrementReferenceOnce_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (check : Bool)
    (descriptors : ClosureDescriptorTable := #[]) :
    decrementReferenceOnce state address check descriptors =
      .error (.sourceAddress (.deadObject address)) := by
  unfold decrementReferenceOnce
  exact related.decrementReferenceOnceFuel_eq _ check descriptors

/-- A positive repeated decrement stops at its first stale one-step
transition. Amount zero remains the operation's intentional empty fold. -/
theorem DeadCellRel.decrementReference_succ_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (amount : Nat) (check : Bool)
    (descriptors : ClosureDescriptorTable := #[]) :
    decrementReference state address (amount + 1) check descriptors =
      .error (.sourceAddress (.deadObject address)) := by
  simp only [decrementReference, List.replicate_succ, List.foldlM_cons,
    Bind.bind, Except.bind]
  rw [related.decrementReferenceOnce_eq check descriptors]

/-- A stale mapped increment has the same exact concrete/source fault and no
post-state at either level. -/
theorem LiveHeapRel.incrementReference_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) (amount : Nat) (check : Bool) :
    incrementReference state address amount check =
        .error (.sourceAddress (.deadObject address)) ∧
      Fir.LeanIR.Impure.incValue runtime (.object (.heap location)) amount check =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  exact ⟨deadRelated.incrementReference_eq amount check, by
    simp [Fir.LeanIR.Impure.incValue, Fir.LeanIR.Impure.incLocation,
      getLiveCell, found, dead]
    rfl⟩

/-- Every positive stale decrement has the same exact boundary; the first
failed step prevents any concrete or semantic update. -/
theorem LiveHeapRel.decrementReference_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) (amount : Nat) (check : Bool)
    (descriptors : ClosureDescriptorTable := #[]) :
    decrementReference state address (amount + 1) check
        descriptors =
        .error (.sourceAddress (.deadObject address)) ∧
      Fir.LeanIR.Impure.decValue runtime (.object (.heap location))
          (amount + 1) check = .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  refine ⟨deadRelated.decrementReference_succ_eq amount check
    descriptors, ?_⟩
  have semanticOnce :
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .error (.deadObject location) := by
    simp [Fir.LeanIR.Impure.decValueOnce, Fir.LeanIR.Impure.decLocation,
      Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found, dead]
    rfl
  simp only [Fir.LeanIR.Impure.decValue, List.replicate_succ,
    List.foldlM_cons, Bind.bind, Except.bind]
  rw [semanticOnce]

/-- A positive-fuel decrement of a represented live, ordinary, zero-count
cell reaches the exact physical underflow boundary before reading ownership
metadata or traversing children. -/
theorem LiveCellRel.decrementReferenceOnceFuel_underflow_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (ordinary : cell.persistent = false) (zero : cell.rc = 0)
    (fuel : Nat) (check : Bool)
    (descriptors : ClosureDescriptorTable := #[]) :
    decrementReferenceOnceFuel (fuel + 1) state address check descriptors =
      .error (.sourceAddress (.referenceCountUnderflow address)) := by
  obtain ⟨header, headerRead, _, notPromoted, headerPersistentRel,
      headerRefCountRel⟩ := related.ownershipHeader
  have headerOrdinary : header.persistent = false :=
    headerPersistentRel.trans ordinary
  have headerZero : header.refCount = 0 := by
    apply UInt32.toNat.inj
    simpa [zero] using headerRefCountRel
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  simp only [decrementReferenceOnceFuel]
  rw [heap, headerRead]
  simp only [Bind.bind, Except.bind, liftMemory]
  rw [if_neg (by simp [notPromoted])]
  rw [if_neg (by simp [headerOrdinary])]
  rw [if_pos (by simp [headerZero])]
  rfl

/-- The public one-step decrement inherits the exact represented-cell
underflow boundary from its positive cursor-derived fuel budget. -/
theorem LiveCellRel.decrementReferenceOnce_underflow_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (ordinary : cell.persistent = false) (zero : cell.rc = 0)
    (check : Bool) (descriptors : ClosureDescriptorTable := #[]) :
    decrementReferenceOnce state address check descriptors =
      .error (.sourceAddress (.referenceCountUnderflow address)) := by
  unfold decrementReferenceOnce
  exact related.decrementReferenceOnceFuel_underflow_eq ordinary zero _ check
    descriptors

/-- A positive semantic release budget selects the matching source underflow
before any owned child can be visited. -/
theorem LiveCellRel.decLocationFuel_underflow_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (ordinary : cell.persistent = false) (zero : cell.rc = 0)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell) (fuel : Nat) :
    Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location =
      .error (.referenceCountUnderflow location) := by
  simp only [Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found,
    related.live_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [if_neg (by simp [ordinary])]
  rw [if_pos zero]
  rfl

/-- Every positive repeated decrement of a mapped live, ordinary, zero-count
cell has the same exact concrete/source underflow; the first failing step
prevents header writes and recursive ownership release. -/
theorem LiveHeapRel.decrementReference_underflow
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (zero : cell.rc = 0) (amount : Nat) (check : Bool)
    (descriptors : ClosureDescriptorTable := #[]) :
    decrementReference state address (amount + 1) check descriptors =
        .error (.sourceAddress (.referenceCountUnderflow address)) ∧
      Fir.LeanIR.Impure.decValue runtime (.object (.heap location))
          (amount + 1) check =
        .error (.referenceCountUnderflow location) := by
  have mappedLookup :
      witness.locations.lookup? location = some address := by
    cases mapped with
    | mapped found => exact found
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mappedLookup
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  have concreteOnce :=
    targetRelated.decrementReferenceOnce_underflow_eq ordinary zero check
      descriptors
  have semanticOnce :=
    targetRelated.decLocationFuel_underflow_eq ordinary zero runtime location
      found runtime.heap.length
  constructor
  · simp only [decrementReference, List.replicate_succ, List.foldlM_cons,
      Bind.bind, Except.bind]
    rw [concreteOnce]
  · simp only [Fir.LeanIR.Impure.decValue, List.replicate_succ,
      List.foldlM_cons, Bind.bind, Except.bind,
      Fir.LeanIR.Impure.decValueOnce, Fir.LeanIR.Impure.decLocation]
    rw [semanticOnce]

/-- A represented persistent cell makes the concrete increment operation an
exact no-op, independently of the requested count. -/
theorem LiveCellRel.incrementReference_persistent_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (persistent : cell.persistent = true) (amount : Nat) (check : Bool) :
    Fir.Wasm.Concrete.incrementReference state address amount check = .ok state := by
  obtain ⟨header, headerRead, _, notPromoted, headerPersistentRel, _⟩ :=
    related.ownershipHeader
  have headerPersistent : header.persistent = true :=
    headerPersistentRel.trans persistent
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  unfold Fir.Wasm.Concrete.incrementReference
  rw [heap]
  simp only
  rw [headerRead]
  simp only [Bind.bind, Except.bind, liftMemory]
  rw [if_neg (by simp [notPromoted])]
  rw [if_pos (by simp [headerPersistent])]
  rfl

/-- Every positive concrete ownership-decrement fuel budget also returns a
represented persistent cell unchanged. -/
theorem LiveCellRel.decrementReferenceOnceFuel_persistent_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (persistent : cell.persistent = true) (fuel : Nat) (check : Bool)
    (descriptors : ClosureDescriptorTable := #[]) :
    decrementReferenceOnceFuel (fuel + 1) state address check descriptors =
      .ok state := by
  obtain ⟨header, headerRead, _, notPromoted, headerPersistentRel, _⟩ :=
    related.ownershipHeader
  have headerPersistent : header.persistent = true :=
    headerPersistentRel.trans persistent
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  simp only [decrementReferenceOnceFuel]
  rw [heap, headerRead]
  simp only [Bind.bind, Except.bind, liftMemory]
  rw [if_neg (by simp [notPromoted])]
  rw [if_pos (by simp [headerPersistent])]
  rfl

/-- Every positive semantic ownership-decrement fuel budget returns a
persistent mapped cell unchanged. -/
theorem LiveCellRel.decLocationFuel_persistent_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (persistent : cell.persistent = true)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell) (fuel : Nat) :
    Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location = .ok runtime := by
  simp only [Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found,
    related.live_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [if_pos persistent]
  rfl

/-- Semantic increment likewise returns a persistent mapped cell unchanged. -/
theorem LiveCellRel.incValue_persistent_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (persistent : cell.persistent = true)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (amount : Nat) (check : Bool) :
    Fir.LeanIR.Impure.incValue runtime (.object (.heap location)) amount check =
      .ok runtime := by
  simp only [Fir.LeanIR.Impure.incValue, Fir.LeanIR.Impure.incLocation, getLiveCell,
    found, related.live_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [if_pos persistent]
  rfl

/-- Whole-heap source/concrete increment refinement. Persistent cells are
exact no-ops in both runtimes; ordinary cells rewrite only the target common
header and use the generic frame assembler for every other allocation. Both
branches preserve the heap frontier and physical capacity of every mapped
allocation. -/
theorem LiveHeapRel.incrementReference_refines_with_capacity
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result nextRuntime,
      incrementReference state address amount check = .ok result ∧
      Fir.LeanIR.Impure.incValue runtime (.object (.heap location)) amount check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      result.heapCursor = state.heapCursor ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  by_cases persistentCase : cell.persistent = true
  · exact ⟨state, runtime,
      targetRelated.incrementReference_persistent_eq persistentCase amount check,
      targetRelated.incValue_persistent_eq persistentCase runtime location found amount
        check,
      related, rfl, .refl state witness⟩
  · have ordinary : cell.persistent = false := by
      cases value : cell.persistent
      · rfl
      · simp [value] at persistentCase
    obtain ⟨header, headerRead, rawRead, notPromoted, persistent, refCount⟩ :=
      targetRelated.ownershipHeader
    have headerOrdinary : header.persistent = false := persistent.trans ordinary
    obtain ⟨targetDescriptor, targetDescriptorFound⟩ := targetRelated.descriptor
    obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
        headerWrite, finalValid, headerAfter⟩ :=
      incrementReference_header related.frontier headerRead targetRelated.headerOwned
        notPromoted headerOrdinary cell.rc amount refCount fits check
    obtain ⟨localResult, localOperation, _, targetAfter⟩ :=
      targetRelated.incrementReference related.frontier ordinary amount fits check
    rw [operation] at localOperation
    have localEq := Except.ok.inj localOperation
    subst localResult
    have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
      Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
    have sameExtent : updatedHeader.allocationBytes = header.allocationBytes := by
      simp [updatedEq]
    obtain ⟨nextRuntime, semanticUpdate, finalRelated⟩ :=
      related.setCell_of_headerWrite mapped found targetDescriptorFound rawRead
        resultEq headerInBounds headerWrite sameExtent finalValid (.live targetAfter)
    have semanticEq := targetRelated.incValue_eq ordinary runtime location found amount check
    have capacity :=
      related.mappedHeaderCapacity_of_headerWrite targetDescriptorFound rawRead
        resultEq headerInBounds headerWrite sameExtent
    exact ⟨result, nextRuntime, operation, by rw [semanticEq, semanticUpdate],
      finalRelated, by simp [resultEq], capacity⟩

theorem LiveHeapRel.incrementReference_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result nextRuntime,
      incrementReference state address amount check = .ok result ∧
      Fir.LeanIR.Impure.incValue runtime (.object (.heap location)) amount check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, nextRuntime, concrete, semantic, finalRelated, _, _⟩ :=
    related.incrementReference_refines_with_capacity mapped found live amount fits
      check
  exact ⟨result, nextRuntime, concrete, semantic, finalRelated⟩

/-- Folding state transitions that individually preserve the heap frontier
also preserves it for the complete successful fold. -/
private theorem List.foldlM_memoryState_preserves_heapCursor
    {α ε : Type} {step : MemoryState → α → Except ε MemoryState}
    (preserves : ∀ before value after,
      step before value = .ok after →
      after.heapCursor = before.heapCursor)
    {values : List α} {before after : MemoryState}
    (operation : values.foldlM (init := before) step = .ok after) :
    after.heapCursor = before.heapCursor := by
  induction values generalizing before with
  | nil =>
      simpa only [List.foldlM_nil, Except.ok.injEq] using
        (congrArg MemoryState.heapCursor (Except.ok.inj operation)).symm
  | cons value rest ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at operation
      cases firstOperation : step before value with
      | error failure =>
          rw [firstOperation] at operation
          contradiction
      | ok middle =>
          rw [firstOperation] at operation
          exact (ih operation).trans (preserves before value middle firstOperation)

/-- Rewriting a validated header changes only linear memory. -/
theorem writeLiveHeader_preserves_heapCursor
    {state result : MemoryState} {address : Word32} {header : Header}
    (operation : writeLiveHeader state address header = .ok result) :
    result.heapCursor = state.heapCursor := by
  unfold writeLiveHeader at operation
  change (do
    let memory ← liftMemory (header.write state.memory address)
    return ({ state with memory } : MemoryState)) = .ok result at operation
  cases written : header.write state.memory address with
  | error failure =>
      rw [written] at operation
      simp [liftMemory, Functor.map, Except.map] at operation
  | ok memory =>
      rw [written] at operation
      simp [liftMemory, Functor.map, Except.map] at operation
      subst result
      rfl

/--
Every successful fuel-indexed recursive release preserves the exact heap
frontier. This is a property of the executable ownership algorithm itself:
it performs only header rewrites and recursive folds of the same operation.
-/
theorem decrementReferenceOnceFuel_preserves_heapCursor
    {fuel : Nat} {state result : MemoryState} {object : Word32} {check : Bool}
    {descriptors : ClosureDescriptorTable}
    (operation :
      decrementReferenceOnceFuel fuel state object check descriptors =
        .ok result) :
    result.heapCursor = state.heapCursor := by
  induction fuel generalizing state result object check with
  | zero =>
      simp only [decrementReferenceOnceFuel] at operation
      cases classified : object.classify <;> rw [classified] at operation
      · by_cases checked : check = true <;>
          simp [checked, pure, Except.pure] at operation
        subst result
        rfl
      · by_cases checked : check = true <;>
          simp [checked, pure, Except.pure] at operation
        subst result
        rfl
      · cases read : state.readLiveHeader object with
        | error failure =>
            simp [liftMemory, read, Bind.bind, Except.bind] at operation
        | ok header =>
            simp [liftMemory, read, Bind.bind, Except.bind] at operation
            by_cases promoted : header.isPromotedTag = true
            · by_cases checked : check = true <;>
                simp [promoted, checked, pure, Except.pure] at operation
              subst result
              rfl
            · simp [promoted] at operation
      · simp at operation
  | succ fuel ih =>
      simp only [decrementReferenceOnceFuel] at operation
      cases classified : object.classify <;> rw [classified] at operation
      · by_cases checked : check = true <;>
          simp [checked, pure, Except.pure] at operation
        subst result
        rfl
      · by_cases checked : check = true <;>
          simp [checked, pure, Except.pure] at operation
        subst result
        rfl
      · cases read : state.readLiveHeader object with
        | error failure =>
            simp [liftMemory, read, Bind.bind, Except.bind] at operation
        | ok header =>
            simp only [liftMemory, read, Bind.bind, Except.bind] at operation
            by_cases promoted : header.isPromotedTag = true
            · by_cases checked : check = true <;>
                simp [promoted, checked, pure, Except.pure] at operation
              subst result
              rfl
            · simp only [promoted] at operation
              by_cases persistent : header.persistent = true
              · simp [persistent, pure, Except.pure] at operation
                subst result
                rfl
              · simp only [persistent] at operation
                by_cases zero : header.refCount == 0
                · simp [zero] at operation
                · simp only [zero] at operation
                  by_cases shared : 1 < header.refCount.toNat
                  · simp only [shared, if_true] at operation
                    exact writeLiveHeader_preserves_heapCursor operation
                  · simp only [shared, if_false] at operation
                    cases ownedOperation :
                        readOwnedReferences state object header descriptors with
                    | error failure =>
                        rw [ownedOperation] at operation
                        contradiction
                    | ok owned =>
                        rw [ownedOperation] at operation
                        cases writeOperation :
                            writeLiveHeader state object header.forRelease with
                        | error failure =>
                            rw [writeOperation] at operation
                            contradiction
                        | ok middle =>
                            rw [writeOperation] at operation
                            exact
                              (List.foldlM_memoryState_preserves_heapCursor
                                (fun before child after childOperation =>
                                  ih childOperation)
                                operation).trans
                                (writeLiveHeader_preserves_heapCursor
                                  writeOperation)
      · simp at operation

/-- The public one-step release wrapper inherits exact frontier preservation
from its fuel-indexed implementation. -/
theorem decrementReferenceOnce_preserves_heapCursor
    {state result : MemoryState} {object : Word32} {check : Bool}
    {descriptors : ClosureDescriptorTable}
    (operation :
      decrementReferenceOnce state object check descriptors = .ok result) :
    result.heapCursor = state.heapCursor := by
  unfold decrementReferenceOnce at operation
  exact decrementReferenceOnceFuel_preserves_heapCursor operation

/-- Repeating successful release steps never advances or retracts the heap
frontier. -/
theorem decrementReference_preserves_heapCursor
    {state result : MemoryState} {object : Word32} {amount : Nat} {check : Bool}
    {descriptors : ClosureDescriptorTable}
    (operation :
      decrementReference state object amount check descriptors = .ok result) :
    result.heapCursor = state.heapCursor := by
  unfold decrementReference at operation
  exact List.foldlM_memoryState_preserves_heapCursor
    (fun before _ after step =>
      decrementReferenceOnce_preserves_heapCursor step)
    operation

/-- Whole-heap source/concrete refinement for the nonrecursive decrement
branch. The target count changes, every other allocation is framed by the
descriptor disjointness invariant, and the semantic `setCell` update is
reassembled into `LiveHeapRel`. -/
theorem LiveHeapRel.decrementReferenceOnce_refines_above_one_with_capacity
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnce state address check descriptors = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, rawRead, notPromoted, persistent, refCount⟩ :=
    targetRelated.ownershipHeader
  have headerOrdinary : header.persistent = false := persistent.trans ordinary
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
  have operationFor (descriptorTable : ClosureDescriptorTable) :
      decrementReferenceOnce state address check descriptorTable = .ok result := by
    simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [headerOrdinary])]
    rw [if_neg (by simpa using refCountNe)]
    rw [refCount, if_pos oneLt]
    simpa [updatedEq] using writeOperation
  have operation := operationFor descriptors
  obtain ⟨localResult, localOperation, _, targetAfter⟩ :=
    targetRelated.decrementReferenceOnce_above_one related.frontier ordinary oneLt check
  have localEq := Except.ok.inj (localOperation.symm.trans (operationFor #[]))
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
  have semanticEq := targetRelated.decValueOnce_above_one_eq ordinary runtime location
    found oneLt check
  have capacity :=
    related.mappedHeaderCapacity_of_headerWrite targetDescriptorFound rawRead
      resultEq headerInBounds headerWrite sameExtent
  exact ⟨result, nextRuntime, operation, by rw [semanticEq, semanticUpdate],
    finalRelated, capacity⟩

theorem LiveHeapRel.decrementReferenceOnce_refines_above_one
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnce state address check descriptors = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, nextRuntime, concrete, semantic, finalRelated, _⟩ :=
    related.decrementReferenceOnce_refines_above_one_with_capacity
      (descriptors := descriptors) mapped found live ordinary oneLt check
  exact ⟨result, nextRuntime, concrete, semantic, finalRelated⟩

/-- Whole-heap source/concrete refinement for count-one boxes and heap
naturals. The concrete allocation becomes a canonical dead cell, every
disjoint allocation is framed, and the semantic heap records the matching
zero-count/dead replacement. -/
theorem LiveHeapRel.decrementReferenceOnce_refines_leaf_one_with_capacity
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (leafCell : NonrecursiveCell cell)
    (ordinary : cell.persistent = false)
    (one : cell.rc = 1) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnce state address check descriptors = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨targetDescriptor, targetDescriptorFound⟩ := targetRelated.descriptor
  obtain ⟨result, header, memory, operation, headerRead, resultEq, headerWrite,
      finalValid, deadRelated⟩ :=
    targetRelated.decrementReferenceOnce_leaf_one (descriptors := descriptors) leafCell
      related.frontier ordinary one check
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
  have semanticEq := targetRelated.decValueOnce_leaf_one_eq leafCell ordinary runtime
    location found one check
  have capacity :=
    related.mappedHeaderCapacity_of_headerWrite targetDescriptorFound rawRead
      resultEq headerInBounds headerWrite sameExtent
  exact ⟨result, nextRuntime, operation,
    by rw [semanticEq, show { cell with rc := 0, live := false } = replacement by rfl,
      semanticUpdate], finalRelated, capacity⟩

theorem LiveHeapRel.decrementReferenceOnce_refines_leaf_one
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (leafCell : NonrecursiveCell cell)
    (ordinary : cell.persistent = false)
    (one : cell.rc = 1) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnce state address check descriptors = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, nextRuntime, concrete, semantic, finalRelated, _⟩ :=
    related.decrementReferenceOnce_refines_leaf_one_with_capacity
      (descriptors := descriptors) mapped found live leafCell ordinary one check
  exact ⟨result, nextRuntime, concrete, semantic, finalRelated⟩

/-- The established whole-heap above-one refinement is valid at every
positive explicit fuel budget, not only the two public derived budgets. -/
theorem LiveHeapRel.decrementReferenceOnceFuel_refines_above_one_with_capacity
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (oneLt : 1 < cell.rc) (fuel : Nat) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnceFuel (fuel + 1) state address check descriptors = .ok result ∧
      Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, persistent, refCount⟩ :=
    targetRelated.ownershipHeader
  have headerOrdinary : header.persistent = false := persistent.trans ordinary
  obtain ⟨result, nextRuntime, concretePublic, semanticPublic, finalRelated,
      capacity⟩ :=
    related.decrementReferenceOnce_refines_above_one_with_capacity
      (descriptors := descriptors) mapped found live ordinary oneLt check
  have concreteEq :=
    Fir.Wasm.Concrete.decrementReferenceOnceFuel_above_one_eq_public headerRead
      notPromoted headerOrdinary cell.rc refCount oneLt fuel check descriptors
  have semanticFuelEq :=
    targetRelated.decLocationFuel_above_one_eq ordinary runtime location found oneLt fuel
  have semanticPublicEq :=
    targetRelated.decValueOnce_above_one_eq ordinary runtime location found oneLt check
  exact ⟨result, nextRuntime, by rw [concreteEq]; exact concretePublic, by
    rw [semanticFuelEq, ← semanticPublicEq]
    exact semanticPublic, finalRelated, capacity⟩

theorem LiveHeapRel.decrementReferenceOnceFuel_refines_above_one
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (oneLt : 1 < cell.rc) (fuel : Nat) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnceFuel (fuel + 1) state address check descriptors =
        .ok result ∧
      Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, nextRuntime, concrete, semantic, finalRelated, _⟩ :=
    related.decrementReferenceOnceFuel_refines_above_one_with_capacity
      (descriptors := descriptors) mapped found live ordinary oneLt fuel check
  exact ⟨result, nextRuntime, concrete, semantic, finalRelated⟩

/-- The whole-heap box/natural leaf refinement is likewise valid for every
positive explicit fuel budget. -/
theorem LiveHeapRel.decrementReferenceOnceFuel_refines_leaf_one_with_capacity
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (leafCell : NonrecursiveCell cell)
    (ordinary : cell.persistent = false)
    (one : cell.rc = 1) (fuel : Nat) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnceFuel (fuel + 1) state address check descriptors = .ok result ∧
      Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨result, nextRuntime, concretePublic, semanticPublic, finalRelated,
      capacity⟩ :=
    related.decrementReferenceOnce_refines_leaf_one_with_capacity
      (descriptors := descriptors) mapped found live leafCell ordinary one check
  have concreteEq :=
    targetRelated.decrementReferenceOnceFuel_leaf_one_eq_public
      (descriptors := descriptors) leafCell ordinary one fuel check
  have semanticFuelEq :=
    targetRelated.decLocationFuel_leaf_one_eq leafCell ordinary runtime location found one fuel
  have semanticPublicEq :=
    targetRelated.decValueOnce_leaf_one_eq leafCell ordinary runtime location found one check
  exact ⟨result, nextRuntime, by rw [concreteEq]; exact concretePublic, by
    rw [semanticFuelEq, ← semanticPublicEq]
    exact semanticPublic, finalRelated, capacity⟩

theorem LiveHeapRel.decrementReferenceOnceFuel_refines_leaf_one
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (leafCell : NonrecursiveCell cell)
    (ordinary : cell.persistent = false)
    (one : cell.rc = 1) (fuel : Nat) (check : Bool) :
    ∃ result nextRuntime,
      decrementReferenceOnceFuel (fuel + 1) state address check descriptors =
        .ok result ∧
      Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, nextRuntime, concrete, semantic, finalRelated, _⟩ :=
    related.decrementReferenceOnceFuel_refines_leaf_one_with_capacity
      (descriptors := descriptors) mapped found live leafCell ordinary one fuel
      check
  exact ⟨result, nextRuntime, concrete, semantic, finalRelated⟩

/-- Complete same-fuel recursive ownership simulation for one mapped semantic
heap location. Successful semantic execution determines every branch; the
count-one constructor branch releases the parent first and then applies the
paired ownership-fold theorem with the fuel induction hypothesis. -/
theorem LiveHeapRel.decrementReferenceOnceFuel_refines_with_capacity
    {fuel : Nat} {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (semanticOperation :
      Fir.LeanIR.Impure.decLocationFuel fuel runtime location = .ok nextRuntime) :
    ∃ result,
      decrementReferenceOnceFuel fuel state address check witness.closureDescriptors =
        .ok result ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness := by
  induction fuel generalizing state runtime location address nextRuntime check with
  | zero =>
      simp [Fir.LeanIR.Impure.decLocationFuel] at semanticOperation
  | succ fuel ih =>
      obtain ⟨cell, found, cellRelation⟩ :=
        related.concreteToSemantic location address mapped
      have live : cell.live = true := by
        cases liveEq : cell.live with
        | false =>
            simp [Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found, liveEq,
              Bind.bind, Except.bind] at semanticOperation
        | true => rfl
      have targetRelated := cellRelation.live_of_eq_true live
      by_cases persistentCase : cell.persistent = true
      · have semanticEq := targetRelated.decLocationFuel_persistent_eq persistentCase
          runtime location found fuel
        have runtimeEq := Except.ok.inj (semanticEq.symm.trans semanticOperation)
        subst nextRuntime
        exact ⟨state,
          targetRelated.decrementReferenceOnceFuel_persistent_eq persistentCase fuel check
            witness.closureDescriptors,
          related, .refl state witness⟩
      · have ordinary : cell.persistent = false := by
          cases value : cell.persistent
          · rfl
          · simp [value] at persistentCase
        have nonzero : cell.rc ≠ 0 := by
          intro zero
          simp [Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found, live, ordinary,
            zero, Bind.bind, Except.bind] at semanticOperation
        by_cases oneLt : 1 < cell.rc
        · obtain ⟨result, branchRuntime, concreteBranch, semanticBranch,
              finalRelated, capacity⟩ :=
          related.decrementReferenceOnceFuel_refines_above_one_with_capacity
            (descriptors := witness.closureDescriptors) mapped found live ordinary
              oneLt fuel check
          have runtimeEq := Except.ok.inj (semanticBranch.symm.trans semanticOperation)
          subst branchRuntime
          exact ⟨result, concreteBranch, finalRelated, capacity⟩
        · have one : cell.rc = 1 := by omega
          cases targetRelated with
          | @boxed kind scalar header _ descriptor objectEq objectRelated refCount
                persistent cellLive =>
              let leafCell : NonrecursiveCell cell :=
                .inl (.inl (.inl ⟨kind, scalar, objectEq⟩))
              obtain ⟨result, branchRuntime, concreteBranch, semanticBranch,
                  finalRelated, capacity⟩ :=
                related.decrementReferenceOnceFuel_refines_leaf_one_with_capacity
                  (descriptors := witness.closureDescriptors) mapped found live leafCell
                    ordinary one fuel check
              have runtimeEq := Except.ok.inj (semanticBranch.symm.trans semanticOperation)
              subst branchRuntime
              exact ⟨result, concreteBranch, finalRelated, capacity⟩
          | @natural value header _ descriptor objectEq headerRead headerKind
                marker extent limbsFit decoded refCount persistent cellLive =>
              let leafCell : NonrecursiveCell cell :=
                .inl (.inl (.inr ⟨value, objectEq⟩))
              obtain ⟨result, branchRuntime, concreteBranch, semanticBranch,
                  finalRelated, capacity⟩ :=
                related.decrementReferenceOnceFuel_refines_leaf_one_with_capacity
                  (descriptors := witness.closureDescriptors) mapped found live leafCell
                    ordinary one fuel check
              have runtimeEq := Except.ok.inj (semanticBranch.symm.trans semanticOperation)
              subst branchRuntime
              exact ⟨result, concreteBranch, finalRelated, capacity⟩
          | @integer value header _ descriptor objectEq objectRelated refCount
                persistent cellLive =>
              let leafCell : NonrecursiveCell cell := .inr ⟨value, objectEq⟩
              obtain ⟨result, branchRuntime, concreteBranch, semanticBranch,
                  finalRelated, capacity⟩ :=
                related.decrementReferenceOnceFuel_refines_leaf_one_with_capacity
                  (descriptors := witness.closureDescriptors) mapped found live leafCell
                    ordinary one fuel check
              have runtimeEq := Except.ok.inj (semanticBranch.symm.trans semanticOperation)
              subst branchRuntime
              exact ⟨result, concreteBranch, finalRelated, capacity⟩
          | @string value header _ descriptor objectEq objectRelated refCount
                persistent cellLive =>
              let leafCell : NonrecursiveCell cell :=
                .inl (.inr ⟨value, objectEq⟩)
              obtain ⟨result, branchRuntime, concreteBranch, semanticBranch,
                  finalRelated, capacity⟩ :=
                related.decrementReferenceOnceFuel_refines_leaf_one_with_capacity
                  (descriptors := witness.closureDescriptors) mapped found live leafCell
                    ordinary one fuel check
              have runtimeEq := Except.ok.inj (semanticBranch.symm.trans semanticOperation)
              subst branchRuntime
              exact ⟨result, concreteBranch, finalRelated, capacity⟩
          | @constructor info fieldKinds semantic header _ descriptor objectEq objectRelated
                headerRead headerKind refCount persistent cellLive =>
              obtain ⟨words, ownedRead, ownershipRelated⟩ :=
                objectRelated.readOwnedReferences headerRead
              obtain ⟨released, memory, releasedOperation, releasedEq, headerWrite,
                  finalValid, deadRelated⟩ :=
                releaseHeader related.frontier headerRead objectRelated.headerOwned
              obtain ⟨_, rawRead, _, _, _, _⟩ :=
                MemoryState.PrefixExtension.readLiveHeader_facts state address header
                  headerRead
              have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
                Nat.le_trans objectRelated.headerOwned related.frontier.cursorInBounds
              let replacement : HeapCell := { cell with rc := 0, live := false }
              have targetAfter : CellRel released witness address replacement :=
                .dead (by simp [replacement]) (by simp [replacement])
                  ⟨.constructor info fieldKinds, descriptor⟩ deadRelated
              obtain ⟨parentRuntime, parentSemantic, parentRelated⟩ :=
                related.setCell_of_headerWrite mapped found descriptor rawRead releasedEq
                  headerInBounds headerWrite rfl finalValid targetAfter
              have parentCapacity :=
                related.mappedHeaderCapacity_of_headerWrite descriptor rawRead
                  releasedEq headerInBounds headerWrite rfl
              let releaseChild : RuntimeState → Fir.LeanIR.Impure.Value →
                  Except Fir.LeanIR.Impure.RuntimeFault RuntimeState := fun next value =>
                match value with
                | .object (.heap child) =>
                    Fir.LeanIR.Impure.decLocationFuel fuel next child
                | _ => .ok next
              have semanticFoldArray :
                  Array.foldlM releaseChild parentRuntime semantic.objectFields =
                    .ok nextRuntime := by
                simp only [Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found, live,
                  ↓reduceIte, Bind.bind, Except.bind] at semanticOperation
                rw [if_neg (by simp [ordinary])] at semanticOperation
                rw [if_neg nonzero, if_neg oneLt] at semanticOperation
                rw [parentSemantic] at semanticOperation
                rw [objectEq] at semanticOperation
                change Array.foldlM releaseChild parentRuntime semantic.objectFields =
                  .ok nextRuntime at semanticOperation
                exact semanticOperation
              have semanticFoldList :
                  semantic.objectFields.toList.foldlM (init := parentRuntime)
                    releaseChild = .ok nextRuntime := by
                simpa only [Array.foldlM_toList] using semanticFoldArray
              have recurse : ∀ {before : MemoryState}
                  {semanticState nextSemantic : RuntimeState}
                  {childLocation : Location} {childAddress : Word32},
                  LiveHeapRel before witness semanticState →
                  witness.locations.lookup? childLocation = some childAddress →
                  Fir.LeanIR.Impure.decLocationFuel fuel semanticState childLocation =
                    .ok nextSemantic →
                  ∃ after,
                    decrementReferenceOnceFuel fuel before childAddress true
                      witness.closureDescriptors = .ok after ∧
                    LiveHeapRel after witness nextSemantic ∧
                    MappedHeaderCapacityTransport before after witness := by
                intro before semanticState nextSemantic childLocation childAddress
                  childRelated childMapped childOperation
                exact ih childRelated childMapped true childOperation
              obtain ⟨result, concreteFold, finalRelated, foldCapacity⟩ :=
                ownershipRelated.foldlM_refines_with_capacity parentRelated recurse
                  semanticFoldList
              have addressHeap :=
                (MemoryState.PrefixExtension.readLiveHeader_facts state address header
                  headerRead).1
              have notPromoted : header.isPromotedTag = false := by
                have different : (ObjectKind.constructor == ObjectKind.natural) = false :=
                  by decide
                have headerOrdinary : header.persistent = false := persistent.trans ordinary
                simp [Header.isPromotedTag, headerKind, headerOrdinary, different]
              have headerOrdinary : header.persistent = false := persistent.trans ordinary
              have concreteOperation :
                  decrementReferenceOnceFuel (fuel + 1) state address check
                    witness.closureDescriptors = .ok result := by
                simp only [decrementReferenceOnceFuel]
                rw [addressHeap, headerRead]
                simp only [Bind.bind, Except.bind, liftMemory]
                rw [if_neg (by simp [notPromoted])]
                rw [if_neg (by simp [headerOrdinary])]
                have headerNonzero : header.refCount ≠ 0 := by
                  intro zero
                  rw [zero] at refCount
                  simp at refCount
                  omega
                rw [if_neg (by simpa using headerNonzero)]
                rw [refCount, if_neg oneLt]
                have ownedReadWithDescriptors :
                    readOwnedReferences state address header witness.closureDescriptors =
                      .ok words := by
                  simpa [readOwnedReferences, headerKind] using ownedRead
                rw [ownedReadWithDescriptors, releasedOperation]
                exact concreteFold
              exact ⟨result, concreteOperation, finalRelated,
                parentCapacity.trans foldCapacity⟩
          | closure closureRelated =>
              cases closureRelated with
              | @closure function arity captureKinds captures header _ objectEq objectRelated
                    headerRead headerKind descriptorLookup fixedCount extent
                    refCount persistent cellLive =>
                let localClosure : ClosureCellRel state witness address cell :=
                  .closure objectEq objectRelated headerRead headerKind descriptorLookup
                    fixedCount extent refCount persistent cellLive
                obtain ⟨words, closureWordsRead, ownershipRelated⟩ :=
                  objectRelated.readClosureOwnedReferences
                have ownedRead :
                    readOwnedReferences state address header witness.closureDescriptors =
                      .ok words := by
                  simpa [readOwnedReferences, headerKind, descriptorLookup,
                    objectRelated.captureKindsSize, fixedCount] using closureWordsRead
                obtain ⟨released, memory, releasedOperation, releasedEq, headerWrite,
                    finalValid, deadRelated⟩ :=
                  releaseHeader related.frontier headerRead localClosure.headerOwned
                obtain ⟨_, rawRead, _, _, _, _⟩ :=
                  MemoryState.PrefixExtension.readLiveHeader_facts state address header
                    headerRead
                have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
                  Nat.le_trans localClosure.headerOwned related.frontier.cursorInBounds
                let replacement : HeapCell := { cell with rc := 0, live := false }
                have targetAfter : CellRel released witness address replacement :=
                  .dead (by simp [replacement]) (by simp [replacement])
                    ⟨.closure function arity captureKinds, objectRelated.descriptor⟩
                    deadRelated
                obtain ⟨parentRuntime, parentSemantic, parentRelated⟩ :=
                  related.setCell_of_headerWrite mapped found objectRelated.descriptor rawRead
                    releasedEq headerInBounds headerWrite rfl finalValid targetAfter
                have parentCapacity :=
                  related.mappedHeaderCapacity_of_headerWrite
                    objectRelated.descriptor rawRead releasedEq headerInBounds
                    headerWrite rfl
                let releaseChild : RuntimeState → Fir.LeanIR.Impure.Value →
                    Except Fir.LeanIR.Impure.RuntimeFault RuntimeState := fun next value =>
                  match value with
                  | .object (.heap child) =>
                      Fir.LeanIR.Impure.decLocationFuel fuel next child
                  | _ => .ok next
                have semanticFoldArray :
                    Array.foldlM releaseChild parentRuntime captures = .ok nextRuntime := by
                  simp only [Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found, live,
                    ↓reduceIte, Bind.bind, Except.bind] at semanticOperation
                  rw [if_neg (by simp [ordinary])] at semanticOperation
                  rw [if_neg nonzero, if_neg oneLt] at semanticOperation
                  rw [parentSemantic] at semanticOperation
                  rw [objectEq] at semanticOperation
                  change Array.foldlM releaseChild parentRuntime captures =
                    .ok nextRuntime at semanticOperation
                  exact semanticOperation
                have semanticFoldList :
                    captures.toList.foldlM (init := parentRuntime) releaseChild =
                      .ok nextRuntime := by
                  simpa only [Array.foldlM_toList] using semanticFoldArray
                have semanticOwnedFoldList :
                    (closureOwnedValues captureKinds.toList captures.toList).foldlM
                      (init := parentRuntime) releaseChild = .ok nextRuntime := by
                  have foldEq :=
                    objectRelated.foldlM_closureOwnedValues fuel parentRuntime
                  have semanticFoldExplicit := semanticFoldList
                  unfold releaseChild at semanticFoldExplicit ⊢
                  exact foldEq.symm.trans semanticFoldExplicit
                have recurse : ∀ {before : MemoryState}
                    {semanticState nextSemantic : RuntimeState}
                    {childLocation : Location} {childAddress : Word32},
                    LiveHeapRel before witness semanticState →
                    witness.locations.lookup? childLocation = some childAddress →
                    Fir.LeanIR.Impure.decLocationFuel fuel semanticState childLocation =
                      .ok nextSemantic →
                    ∃ after,
                      decrementReferenceOnceFuel fuel before childAddress true
                        witness.closureDescriptors = .ok after ∧
                      LiveHeapRel after witness nextSemantic ∧
                      MappedHeaderCapacityTransport before after witness := by
                  intro before semanticState nextSemantic childLocation childAddress
                    childRelated childMapped childOperation
                  exact ih childRelated childMapped true childOperation
                obtain ⟨result, concreteFold, finalRelated, foldCapacity⟩ :=
                  ownershipRelated.foldlM_refines_with_capacity parentRelated
                    recurse semanticOwnedFoldList
                have addressHeap :=
                  (MemoryState.PrefixExtension.readLiveHeader_facts state address header
                    headerRead).1
                have concreteOrdinary : header.persistent = false :=
                  persistent.trans ordinary
                have notPromoted : header.isPromotedTag = false := by
                  have different : (ObjectKind.closure == ObjectKind.natural) = false :=
                    by decide
                  simp [Header.isPromotedTag, headerKind, concreteOrdinary, different]
                have concreteOperation :
                    decrementReferenceOnceFuel (fuel + 1) state address check
                      witness.closureDescriptors = .ok result := by
                  simp only [decrementReferenceOnceFuel]
                  rw [addressHeap, headerRead]
                  simp only [Bind.bind, Except.bind, liftMemory]
                  rw [if_neg (by simp [notPromoted])]
                  rw [if_neg (by simp [concreteOrdinary])]
                  have headerNonzero : header.refCount ≠ 0 := by
                    intro zero
                    rw [zero] at refCount
                    simp at refCount
                    omega
                  rw [if_neg (by simpa using headerNonzero)]
                  rw [refCount, if_neg oneLt]
                  rw [ownedRead, releasedOperation]
                  exact concreteFold
                exact ⟨result, concreteOperation, finalRelated,
                  parentCapacity.trans foldCapacity⟩

theorem LiveHeapRel.decrementReferenceOnceFuel_refines
    {fuel : Nat} {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (semanticOperation :
      Fir.LeanIR.Impure.decLocationFuel fuel runtime location =
        .ok nextRuntime) :
    ∃ result,
      decrementReferenceOnceFuel fuel state address check
          witness.closureDescriptors =
        .ok result ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, concrete, finalRelated, _⟩ :=
    related.decrementReferenceOnceFuel_refines_with_capacity mapped check
      semanticOperation
  exact ⟨result, concrete, finalRelated⟩

/-- The public concrete recursive decrement refines FIR's public semantic
decrement. Related heaps guarantee that the semantic heap-length fuel fits
inside the concrete cursor-derived budget, and concrete success is monotone
when that budget is enlarged. -/
theorem LiveHeapRel.decrementReferenceOnce_refines_with_capacity
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (semanticOperation :
      Fir.LeanIR.Impure.decLocation runtime location = .ok nextRuntime) :
    ∃ result,
      decrementReferenceOnce state address check witness.closureDescriptors =
        .ok result ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness := by
  unfold Fir.LeanIR.Impure.decLocation at semanticOperation
  obtain ⟨result, concreteSemanticFuel, finalRelated, capacity⟩ :=
    related.decrementReferenceOnceFuel_refines_with_capacity mapped check
      semanticOperation
  have concretePublic := decrementReferenceOnceFuel_ok_mono
    related.semanticFuel_le_concreteFuel concreteSemanticFuel
  exact ⟨result, by
    unfold decrementReferenceOnce
    exact concretePublic, finalRelated, capacity⟩

theorem LiveHeapRel.decrementReferenceOnce_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (semanticOperation :
      Fir.LeanIR.Impure.decLocation runtime location = .ok nextRuntime) :
    ∃ result,
      decrementReferenceOnce state address check witness.closureDescriptors =
        .ok result ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, concrete, finalRelated, _⟩ :=
    related.decrementReferenceOnce_refines_with_capacity mapped check
      semanticOperation
  exact ⟨result, concrete, finalRelated⟩

/-- Repeating a public decrement preserves the heap relation after every
successful semantic step. The outer checked/unchecked bit is immaterial for a
mapped heap address; recursive child releases remain checked in both models.
The witness mapping is stable across dead-cell transitions, so the one-step
theorem composes directly through both folds. -/
theorem LiveHeapRel.decrementReference_refines_with_capacity
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    {amount : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (semanticOperation :
      Fir.LeanIR.Impure.decValue runtime (.object (.heap location)) amount check =
        .ok nextRuntime) :
    ∃ result,
      decrementReference state address amount check witness.closureDescriptors = .ok result ∧
      LiveHeapRel result witness nextRuntime ∧
      result.heapCursor = state.heapCursor ∧
      MappedHeaderCapacityTransport state result witness := by
  induction amount generalizing state runtime nextRuntime with
  | zero =>
      simp [Fir.LeanIR.Impure.decValue] at semanticOperation
      have runtimeEq := Except.ok.inj semanticOperation
      subst nextRuntime
      exact ⟨state, rfl, related, rfl, .refl state witness⟩
  | succ amount ih =>
      simp only [Fir.LeanIR.Impure.decValue, List.replicate_succ,
        List.foldlM_cons, Bind.bind, Except.bind,
        Fir.LeanIR.Impure.decValueOnce] at semanticOperation
      cases firstSemantic : Fir.LeanIR.Impure.decLocation runtime location with
      | error fault =>
          rw [firstSemantic] at semanticOperation
          contradiction
      | ok middleRuntime =>
          rw [firstSemantic] at semanticOperation
          obtain ⟨middleState, firstConcrete, middleRelated, firstCapacity⟩ :=
            related.decrementReferenceOnce_refines_with_capacity mapped check
              firstSemantic
          obtain ⟨result, restConcrete, finalRelated, _restCursor,
              restCapacity⟩ :=
            ih middleRelated semanticOperation
          have concreteOperation :
              decrementReference state address (amount + 1) check
                  witness.closureDescriptors = .ok result := by
            simp only [decrementReference, List.replicate_succ, List.foldlM_cons,
              Bind.bind, Except.bind]
            rw [firstConcrete]
            exact restConcrete
          exact ⟨result, concreteOperation, finalRelated,
            decrementReference_preserves_heapCursor concreteOperation,
            firstCapacity.trans restCapacity⟩

theorem LiveHeapRel.decrementReference_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    {amount : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (semanticOperation :
      Fir.LeanIR.Impure.decValue runtime (.object (.heap location)) amount check =
        .ok nextRuntime) :
    ∃ result,
      decrementReference state address amount check witness.closureDescriptors = .ok result ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, concrete, finalRelated, _, _⟩ :=
    related.decrementReference_refines_with_capacity mapped check
      semanticOperation
  exact ⟨result, concrete, finalRelated⟩

/-- Explicitly deleting an already released ordinary allocation fails at the
live-header read; the physical-zero sentinel exception is unreachable because
every `DeadCellRel` address classifies as a heap word. -/
theorem DeadCellRel.deleteObject_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) :
    deleteObject state address =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨_, _, addressHeap, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    related.header
  have addressNeZero : address ≠ Word32.zero := by
    intro equal
    subst address
    change ObjectWordClass.sentinel = ObjectWordClass.heap at addressHeap
    contradiction
  have addressValueNeZero : address.value ≠ 0 := by
    intro equal
    have sentinel : address.classify = .sentinel := by
      simp [Word32.classify, equal]
    rw [sentinel] at addressHeap
    contradiction
  have addressZeroCheck : (address == Word32.zero) = false := by
    change (address.value == 0) = false
    simp [addressValueNeZero]
  unfold deleteObject
  rw [if_neg (by simp [addressZeroCheck])]
  rw [addressHeap]
  simp only [↓reduceIte, Bind.bind, Except.bind]
  rw [related.readLiveHeader_eq]
  rfl

/-- Stale explicit deletion preserves the exact concrete-address/source-location
fault and produces no post-state. -/
theorem LiveHeapRel.deleteObject_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    deleteObject state address =
        .error (.sourceAddress (.deadObject address)) ∧
      Fir.LeanIR.Impure.deleteValue runtime (.object (.heap location)) =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  exact ⟨deadRelated.deleteObject_eq, by
    simp [Fir.LeanIR.Impure.deleteValue, getLiveCell, found, dead]
    rfl⟩

/-- The erased failed-reset sentinel is a delete-specific no-op in both the
source and concrete runtimes. This does not introduce an ordinary object
relation for physical zero. -/
theorem LiveHeapRel.deleteObject_erased_refines_with_capacity
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    (related : LiveHeapRel state witness runtime) :
    ∃ result,
      deleteObject state Word32.zero = .ok result ∧
      Fir.LeanIR.Impure.deleteValue runtime .erased = .ok runtime ∧
      LiveHeapRel result witness runtime ∧
      MappedHeaderCapacityTransport state result witness ∧
      result.heapCursor = state.heapCursor := by
  exact ⟨state, deleteObject_zero state,
    Fir.LeanIR.Impure.deleteValue_erased runtime, related, .refl state witness,
    rfl⟩

theorem LiveHeapRel.deleteObject_erased_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    (related : LiveHeapRel state witness runtime) :
    ∃ result,
      deleteObject state Word32.zero = .ok result ∧
      Fir.LeanIR.Impure.deleteValue runtime .erased = .ok runtime ∧
      LiveHeapRel result witness runtime := by
  obtain ⟨result, concrete, semantic, finalRelated, _, _⟩ :=
    related.deleteObject_erased_refines_with_capacity
  exact ⟨result, concrete, semantic, finalRelated⟩

/-- Explicit deletion installs the canonical concrete freed header and the
matching semantic zero-count/dead cell without releasing owned children. -/
theorem LiveHeapRel.deleteObject_refines_with_capacity
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (semanticOperation :
      Fir.LeanIR.Impure.deleteValue runtime (.object (.heap location)) =
        .ok nextRuntime) :
    ∃ result,
      deleteObject state address = .ok result ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness ∧
      result.heapCursor = state.heapCursor := by
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  have live : cell.live = true := by
    cases liveEq : cell.live with
    | false =>
        simp [Fir.LeanIR.Impure.deleteValue, getLiveCell, found, liveEq,
          Bind.bind, Except.bind] at semanticOperation
    | true => rfl
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, rawRead, notPromoted, _, _⟩ :=
    targetRelated.ownershipHeader
  obtain ⟨descriptor, descriptorFound⟩ := targetRelated.descriptor
  obtain ⟨released, memory, releasedOperation, releasedEq, headerWrite,
      finalValid, deadRelated⟩ :=
    releaseHeader related.frontier headerRead targetRelated.headerOwned
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
  let replacement : HeapCell := { cell with rc := 0, live := false }
  have targetAfter : CellRel released witness address replacement :=
    .dead (by simp [replacement]) (by simp [replacement])
      ⟨descriptor, descriptorFound⟩ deadRelated
  obtain ⟨deletedRuntime, semanticDelete, finalRelated⟩ :=
    related.setCell_of_headerWrite mapped found descriptorFound rawRead releasedEq
      headerInBounds headerWrite rfl finalValid targetAfter
  have semanticSet : setCell runtime location replacement = .ok nextRuntime := by
    simp only [Fir.LeanIR.Impure.deleteValue, getLiveCell, found, live,
      ↓reduceIte, Bind.bind, Except.bind] at semanticOperation
    exact semanticOperation
  have runtimeEq := Except.ok.inj (semanticDelete.symm.trans semanticSet)
  subst deletedRuntime
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  have addressNeZero : address ≠ Word32.zero := by
    intro equal
    subst address
    change ObjectWordClass.sentinel = ObjectWordClass.heap at addressHeap
    contradiction
  have addressValueNeZero : address.value ≠ 0 := by
    intro equal
    have sentinel : address.classify = .sentinel := by
      simp [Word32.classify, equal]
    rw [sentinel] at addressHeap
    contradiction
  have addressZeroCheck : (address == Word32.zero) = false := by
    change (address.value == 0) = false
    simp [addressValueNeZero]
  have concreteDelete : deleteObject state address = .ok released := by
    unfold deleteObject
    rw [if_neg (by simp [addressZeroCheck])]
    rw [addressHeap]
    simp only [↓reduceIte, Bind.bind, Except.bind]
    rw [headerRead]
    simp only [liftMemory]
    rw [if_neg (by simp [notPromoted])]
    exact releasedOperation
  have capacity :=
    related.mappedHeaderCapacity_of_headerWrite descriptorFound rawRead releasedEq
      headerInBounds headerWrite rfl
  exact ⟨released, concreteDelete, finalRelated, capacity, by
    simp [releasedEq]⟩

theorem LiveHeapRel.deleteObject_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (semanticOperation :
      Fir.LeanIR.Impure.deleteValue runtime (.object (.heap location)) =
        .ok nextRuntime) :
    ∃ result,
      deleteObject state address = .ok result ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨result, concrete, finalRelated, _, _⟩ :=
    related.deleteObject_refines_with_capacity mapped semanticOperation
  exact ⟨result, concrete, finalRelated⟩

end Fir.Wasm.Concrete
