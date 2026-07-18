import Fir.Wasm.Concrete.ReferenceCountCorrectness

namespace Fir.Wasm.Concrete

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

end Fir.Wasm.Concrete
