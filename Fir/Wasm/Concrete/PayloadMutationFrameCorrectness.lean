import Fir.Wasm.Concrete.OwnershipFrameCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Spatial postcondition for a mutation contained in one allocation. The
target header is unchanged and every physically disjoint allocation retains
all of its bytes. -/
structure MemoryState.TargetMutationFrame (before after : MemoryState)
    (targetAddress : Word32) (targetBytes : Nat) : Prop where
  cursor : after.heapCursor = before.heapCursor
  memorySize : after.memory.size = before.memory.size
  targetHeader :
    Header.read after.memory targetAddress = Header.read before.memory targetAddress
  other : ∀ otherAddress otherBytes,
    targetAddress.value + targetBytes ≤ otherAddress.value ∨
      otherAddress.value + otherBytes ≤ targetAddress.value →
    before.AllocationFrame after otherAddress otherBytes

theorem MemoryState.TargetMutationFrame.targetLiveHeader
    {before after : MemoryState} {targetAddress : Word32} {targetBytes : Nat}
    (frame : before.TargetMutationFrame after targetAddress targetBytes) :
    after.readLiveHeader targetAddress = before.readLiveHeader targetAddress := by
  unfold MemoryState.readLiveHeader
  rw [frame.targetHeader, frame.memorySize]

/-- A checked 64-bit payload write wholly inside the target allocation
provides the generic target-mutation frame. -/
theorem MemoryState.TargetMutationFrame.ofWriteUInt64
    {before after : MemoryState} {targetAddress : Word32} {targetBytes : Nat}
    {offset : Nat} {value : UInt64} {memory : LinearMemory}
    (resultEq : after = { before with memory })
    (writeInBounds : offset + 7 < before.memory.size)
    (written : before.memory.writeUInt64 offset value = .ok memory)
    (afterHeader : targetAddress.value + headerBytes ≤ offset)
    (insideTarget : offset + 8 ≤ targetAddress.value + targetBytes) :
    before.TargetMutationFrame after targetAddress targetBytes := by
  subst after
  have memorySize : memory.size = before.memory.size :=
    LinearMemory.size_of_writeUInt64_eq_ok before.memory memory offset value
      writeInBounds written
  have headerFrame : before.AllocationFrame ({ before with memory } : MemoryState)
      targetAddress headerBytes := by
    refine ⟨rfl, memorySize, ?_⟩
    intro byte byteWithin
    apply LinearMemory.readByte_of_writeUInt64_eq_ok_other before.memory memory
      offset value writeInBounds written
    left
    omega
  refine ⟨rfl, memorySize, headerFrame.readHeader (by omega), ?_⟩
  intro otherAddress otherBytes disjoint
  refine ⟨rfl, memorySize, ?_⟩
  intro byte byteWithin
  apply LinearMemory.readByte_of_writeUInt64_eq_ok_other before.memory memory
    offset value writeInBounds written
  rcases disjoint with targetBefore | otherBefore
  · right
    omega
  · left
    omega

/-- A successful 64-bit payload write below the allocation frontier preserves
the zero suffix and therefore the complete frontier invariant. -/
theorem MemoryState.FrontierInvariant.writeUInt64
    {state : MemoryState} {memory : LinearMemory} {offset : Nat} {value : UInt64}
    (valid : state.FrontierInvariant)
    (beforeFrontier : offset + 8 ≤ state.heapCursor)
    (written : state.memory.writeUInt64 offset value = .ok memory) :
    ({ state with memory } : MemoryState).FrontierInvariant := by
  have writeInBounds : offset + 7 < state.memory.size :=
    Nat.lt_of_lt_of_le (by omega) valid.cursorInBounds
  have memorySize := LinearMemory.size_of_writeUInt64_eq_ok state.memory memory
    offset value writeInBounds written
  refine {
    cursorAligned := valid.cursorAligned
    cursorInBounds := by simpa [memorySize] using valid.cursorInBounds
    unusedZero := ?_ }
  intro byte afterCursor finalInBounds
  change state.heapCursor ≤ byte at afterCursor
  change byte < memory.size at finalInBounds
  have oldInBounds : byte < state.memory.size := by
    rw [← memorySize]
    exact finalInBounds
  have oldZero := valid.unusedZero byte afterCursor oldInBounds
  have framed := LinearMemory.readByte_of_writeUInt64_eq_ok_other state.memory
    memory offset value writeInBounds written byte (.inr (by omega))
  cases memoryByte : memory[byte]? with
  | none => simp [LinearMemory.readByte, memoryByte, oldZero] at framed
  | some actual =>
      simp [LinearMemory.readByte, memoryByte, oldZero] at framed
      subst actual
      rfl

/-- A target-mutation frame preserves the descriptor-region and pairwise
disjointness invariants for the complete concrete heap. -/
theorem LiveHeapRel.descriptorSpatial_of_targetMutation
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress : Word32}
    {targetDescriptor : AllocationDescriptor} {targetHeader : Header}
    (related : LiveHeapRel before witness runtime)
    (targetFound : witness.descriptors.lookup? targetAddress = some targetDescriptor)
    (targetRead : Header.read before.memory targetAddress = .ok targetHeader)
    (frame : before.TargetMutationFrame after targetAddress
      targetHeader.allocationBytes.toNat) :
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
  have targetReadAfter : Header.read after.memory targetAddress = .ok targetHeader := by
    rw [frame.targetHeader]
    exact targetRead
  have otherFrame : ∀ other otherDescriptor,
      witness.descriptors.lookup? other = some otherDescriptor →
      targetAddress.value ≠ other.value →
      ∀ otherHeader,
        Header.read before.memory other = .ok otherHeader →
        before.AllocationFrame after other otherHeader.allocationBytes.toNat := by
    intro other otherDescriptor otherFound different otherHeader otherRead
    have disjoint := related.descriptorDisjoint targetAddress other
      targetDescriptor otherDescriptor targetFound otherFound different
        targetHeader otherHeader targetRead otherRead
    exact frame.other other otherHeader.allocationBytes.toNat disjoint
  refine ⟨?_, ?_⟩
  · intro address descriptor found
    by_cases isTarget : targetAddress.value = address.value
    · have addressEq : address = targetAddress :=
        wordEq address targetAddress isTarget.symm
      subst address
      exact ⟨targetHeader, targetReadAfter, targetMinimum, targetAligned, by
        rw [frame.cursor]
        exact targetExtent⟩
    · obtain ⟨header, headerRead, minimum, aligned, extent⟩ :=
        related.descriptorRegion address descriptor found
      have allocationFrame := otherFrame address descriptor found isTarget header
        headerRead
      exact ⟨header, by rw [allocationFrame.readHeader minimum]; exact headerRead,
        minimum, aligned, by rw [allocationFrame.cursor]; exact extent⟩
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
        have rightFrame := otherFrame right rightDescriptor rightFound rightTarget
          oldRightHeader oldRightRead
        rw [rightFrame.readHeader rightMinimum] at rightRead
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
        have leftFrame := otherFrame left leftDescriptor leftFound leftTarget
          oldLeftHeader oldLeftRead
        rw [leftFrame.readHeader leftMinimum] at leftRead
        exact related.descriptorDisjoint left targetAddress leftDescriptor
          targetDescriptor leftFound targetFound (Ne.symm leftTarget) leftHeader
            targetHeader leftRead targetRead
      · obtain ⟨oldLeftHeader, oldLeftRead, leftMinimum, _, _⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        obtain ⟨oldRightHeader, oldRightRead, rightMinimum, _, _⟩ :=
          related.descriptorRegion right rightDescriptor rightFound
        have leftFrame := otherFrame left leftDescriptor leftFound leftTarget
          oldLeftHeader oldLeftRead
        have rightFrame := otherFrame right rightDescriptor rightFound rightTarget
          oldRightHeader oldRightRead
        rw [leftFrame.readHeader leftMinimum] at leftRead
        rw [rightFrame.readHeader rightMinimum] at rightRead
        exact related.descriptorDisjoint left right leftDescriptor rightDescriptor
          leftFound rightFound different leftHeader rightHeader leftRead rightRead

/-- One target-allocation mutation frame plus a new target-cell relation is
enough to perform the matching semantic replacement and rebuild the complete
whole-heap refinement. -/
theorem LiveHeapRel.setCell_of_targetMutation
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell replacement : HeapCell} {targetDescriptor : AllocationDescriptor}
    {targetHeader : Header}
    (related : LiveHeapRel before witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (targetFound : witness.descriptors.lookup? address = some targetDescriptor)
    (targetRead : Header.read before.memory address = .ok targetHeader)
    (frame : before.TargetMutationFrame after address
      targetHeader.allocationBytes.toNat)
    (finalValid : after.FrontierInvariant)
    (targetRelated : CellRel after witness address replacement) :
    ∃ nextRuntime,
      setCell runtime location replacement = .ok nextRuntime ∧
      LiveHeapRel after witness nextRuntime := by
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.descriptorSpatial_of_targetMutation targetFound targetRead frame
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
    obtain ⟨otherHeader, otherHeaderRead, otherMinimum, _, _⟩ :=
      related.descriptorRegion otherAddress otherDescriptor otherDescriptorFound
    have disjoint := related.descriptorDisjoint address otherAddress
      targetDescriptor otherDescriptor targetFound otherDescriptorFound different
        targetHeader otherHeader targetRead otherHeaderRead
    have allocationFrame := frame.other otherAddress
      otherHeader.allocationBytes.toNat disjoint
    exact otherRelated.allocationFrame otherHeaderRead allocationFrame
  have promotedFrame : ∀ payload other,
      witness.promotedTags.Contains payload other →
      PromotedTagRel after witness payload other := by
    intro payload other promotedMapped
    have promoted := related.promoted payload other promotedMapped
    obtain ⟨promotedHeader, promotedHeaderRead, _, _, _, _, _, _⟩ :=
      promoted.header
    obtain ⟨_, promotedRawRead, _, promotedMinimum, _, _⟩ :=
      MemoryState.PrefixExtension.readLiveHeader_facts before other promotedHeader
        promotedHeaderRead
    have differentWord : address ≠ other :=
      related.witnessWellFormed.locationPromotionDisjoint location payload address
        other mapped promotedMapped
    have different : address.value ≠ other.value := by
      intro equal
      exact differentWord (wordEq address other equal)
    have disjoint := related.descriptorDisjoint address other targetDescriptor
      (.promotedTag payload) targetFound promoted.descriptor different targetHeader
        promotedHeader targetRead promotedRawRead
    have allocationFrame := frame.other other
      promotedHeader.allocationBytes.toNat disjoint
    exact promoted.allocationFrame promotedHeaderRead allocationFrame
  exact related.setCell_of_frames mapped found frame.cursor finalValid targetRelated
    descriptorRegion descriptorDisjoint cellFrame promotedFrame

end Fir.Wasm.Concrete
