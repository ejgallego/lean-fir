import Fir.Wasm.Concrete.ObjectFieldsCorrectness

namespace Fir.Wasm.Concrete

/-- A concrete runtime state extends another monotonically while preserving
every byte owned below the old allocation frontier.  Fresh allocation proofs
use this relation as the frame boundary for already-related heap objects. -/
structure MemoryState.PrefixExtension (before after : MemoryState) : Prop where
  cursor : before.heapCursor ≤ after.heapCursor
  memorySize : before.memory.size ≤ after.memory.size
  readByte : ∀ address, address < before.heapCursor →
    after.memory.readByte address = before.memory.readByte address

namespace MemoryState.PrefixExtension

theorem refl (state : MemoryState) : state.PrefixExtension state := by
  exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩

theorem trans {first second third : MemoryState}
    (left : first.PrefixExtension second)
    (right : second.PrefixExtension third) :
    first.PrefixExtension third := by
  refine ⟨Nat.le_trans left.cursor right.cursor,
    Nat.le_trans left.memorySize right.memorySize, ?_⟩
  intro address beforeCursor
  rw [right.readByte address (Nat.lt_of_lt_of_le beforeCursor left.cursor)]
  exact left.readByte address beforeCursor

end MemoryState.PrefixExtension

/-- Page growth appends zero bytes and never changes an existing byte. -/
theorem LinearMemory.readByte_growToFit_before_size (memory : LinearMemory)
    (requiredBytes address : Nat) (inBounds : address < memory.size) :
    (memory.growToFit requiredBytes).readByte address = memory.readByte address := by
  unfold LinearMemory.growToFit
  split
  next enough => rfl
  next notEnough =>
    simp [LinearMemory.readByte, Array.getElem?_append, inBounds]

/-- The raw monotone allocator is a prefix extension whenever its input
frontier is aligned and in bounds. -/
theorem MemoryState.FrontierInvariant.allocate_prefixExtension
    {state result : MemoryState} {requestedBytes : Nat} {address : Word32}
    (valid : state.FrontierInvariant)
    (allocated : state.allocate requestedBytes = .ok (result, address)) :
    state.PrefixExtension result := by
  have post := MemoryState.allocate_spec state result requestedBytes address allocated
  have cursorAligned : align8 state.heapCursor = state.heapCursor := by
    exact align8_eq_of_mod_eq_zero state.heapCursor (by
      simpa [target] using valid.cursorAligned)
  refine {
    cursor := ?_
    memorySize := ?_
    readByte := ?_ }
  · rw [post.cursor, cursorAligned]
    omega
  · rw [post.memory]
    unfold LinearMemory.growToFit
    split
    next enough => exact Nat.le_refl _
    next notEnough => simp
  · intro byte beforeCursor
    rw [post.memory]
    exact LinearMemory.readByte_growToFit_before_size state.memory _ byte
      (Nat.lt_of_lt_of_le beforeCursor valid.cursorInBounds)

/-- A fresh object begins exactly at the old aligned frontier. -/
theorem MemoryState.FrontierInvariant.allocateObject_address
    {state result : MemoryState} {kind : ObjectKind} {payloadBytes : Nat}
    {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (valid : state.FrontierInvariant)
    (allocated : state.allocateObject kind payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (result, address)) :
    address.value = state.heapCursor := by
  obtain ⟨middle, allocateResult, _, _, _⟩ :=
    MemoryState.allocateObject_header state result kind payloadBytes persistent
      aux0 aux1 aux2 aux3 address allocated
  have post := MemoryState.allocate_spec state middle
    (align8 (headerBytes + payloadBytes)) address allocateResult
  rw [post.addressValue]
  exact align8_eq_of_mod_eq_zero state.heapCursor (by
    simpa [target] using valid.cursorAligned)

/-- A fresh object's cursor is exactly the end of its aligned extent. -/
theorem MemoryState.allocateObject_extent
    {state result : MemoryState} {kind : ObjectKind} {payloadBytes : Nat}
    {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (allocated : state.allocateObject kind payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (result, address)) :
    result.heapCursor = address.value + align8 (headerBytes + payloadBytes) := by
  obtain ⟨middle, allocateResult, _, cursorEq, _⟩ :=
    MemoryState.allocateObject_header state result kind payloadBytes persistent
      aux0 aux1 aux2 aux3 address allocated
  have post := MemoryState.allocate_spec state middle
    (align8 (headerBytes + payloadBytes)) address allocateResult
  rw [cursorEq, post.cursor, post.addressValue, align8_align8]

/-- Installing a fresh common header preserves the entire old owned prefix. -/
theorem MemoryState.FrontierInvariant.allocateObject_prefixExtension
    {state result : MemoryState} {kind : ObjectKind} {payloadBytes : Nat}
    {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (valid : state.FrontierInvariant)
    (allocated : state.allocateObject kind payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (result, address)) :
    state.PrefixExtension result := by
  obtain ⟨middle, allocateResult, headerWrite, cursorEq, _⟩ :=
    MemoryState.allocateObject_header state result kind payloadBytes persistent
      aux0 aux1 aux2 aux3 address allocated
  have extension := valid.allocate_prefixExtension allocateResult
  have allocationPost := MemoryState.allocate_spec state middle
    (align8 (headerBytes + payloadBytes)) address allocateResult
  have headerInBounds : address.value + headerBytes ≤ middle.memory.size := by
    have endInBounds := allocationPost.endInBounds
    rw [align8_align8] at endInBounds
    have minimum := align8_ge (headerBytes + payloadBytes)
    omega
  have finalSize := Header.write_preserves_size middle.memory result.memory address
    (Header.forAllocation kind (align8 (headerBytes + payloadBytes)) persistent
      aux0 aux1 aux2 aux3) headerInBounds headerWrite
  have freshAddress := valid.allocateObject_address allocated
  refine {
    cursor := by simpa [cursorEq] using extension.cursor
    memorySize := Nat.le_trans extension.memorySize (by omega)
    readByte := ?_ }
  intro byte beforeCursor
  calc
    result.memory.readByte byte = middle.memory.readByte byte :=
      Header.readByte_of_write_eq_ok_other middle.memory result.memory address
        (Header.forAllocation kind (align8 (headerBytes + payloadBytes)) persistent
          aux0 aux1 aux2 aux3) byte headerInBounds headerWrite
        (.inl (by omega))
    _ = state.memory.readByte byte := extension.readByte byte beforeCursor

namespace MemoryState.PrefixExtension

/-- Any owned 16-bit lane reads identically through a prefix extension. -/
theorem readUInt16 {before after : MemoryState}
    (extension : before.PrefixExtension after) (address : Nat)
    (owned : address + 2 ≤ before.heapCursor) :
    after.memory.readUInt16 address = before.memory.readUInt16 address := by
  unfold LinearMemory.readUInt16
  rw [extension.readByte address (by omega)]
  rw [extension.readByte (address + 1) (by omega)]

/-- Any owned 32-bit lane reads identically through a prefix extension. -/
theorem readUInt32 {before after : MemoryState}
    (extension : before.PrefixExtension after) (address : Nat)
    (owned : address + 4 ≤ before.heapCursor) :
    after.memory.readUInt32 address = before.memory.readUInt32 address := by
  unfold LinearMemory.readUInt32
  rw [extension.readByte address (by omega)]
  rw [extension.readByte (address + 1) (by omega)]
  rw [extension.readByte (address + 2) (by omega)]
  rw [extension.readByte (address + 3) (by omega)]

/-- Any owned 64-bit lane reads identically through a prefix extension. -/
theorem readUInt64 {before after : MemoryState}
    (extension : before.PrefixExtension after) (address : Nat)
    (owned : address + 8 ≤ before.heapCursor) :
    after.memory.readUInt64 address = before.memory.readUInt64 address := by
  unfold LinearMemory.readUInt64
  rw [extension.readUInt32 address (by omega)]
  rw [extension.readUInt32 (address + 4) (by omega)]

/-- Any owned object word reads identically through a prefix extension. -/
theorem readWord32 {before after : MemoryState}
    (extension : before.PrefixExtension after) (address : Nat)
    (owned : address + 4 ≤ before.heapCursor) :
    after.memory.readWord32 address = before.memory.readWord32 address := by
  unfold LinearMemory.readWord32
  rw [extension.readUInt32 address owned]

/-- A common header wholly below the old frontier decodes identically through
a prefix extension. -/
theorem readHeader {before after : MemoryState}
    (extension : before.PrefixExtension after) (address : Word32)
    (owned : address.value + headerBytes ≤ before.heapCursor) :
    Header.read after.memory address = Header.read before.memory address := by
  unfold Header.read
  dsimp only
  rw [extension.readUInt32 (address.value + headerKindOffset) (by
    simp [headerKindOffset, headerBytes] at owned ⊢; omega)]
  rw [extension.readUInt32 (address.value + headerFlagsOffset) (by
    simp [headerFlagsOffset, headerBytes] at owned ⊢; omega)]
  rw [extension.readUInt32 (address.value + headerRefCountOffset) (by
    simp [headerRefCountOffset, headerBytes] at owned ⊢; omega)]
  rw [extension.readUInt32 (address.value + headerAllocationBytesOffset) (by
    simp [headerAllocationBytesOffset, headerBytes] at owned ⊢; omega)]
  rw [extension.readUInt32 (address.value + headerAux0Offset) (by
    simp [headerAux0Offset, headerBytes] at owned ⊢; omega)]
  rw [extension.readUInt32 (address.value + headerAux1Offset) (by
    simp [headerAux1Offset, headerBytes] at owned ⊢; omega)]
  rw [extension.readUInt32 (address.value + headerAux2Offset) (by
    simp [headerAux2Offset, headerBytes] at owned ⊢; omega)]
  rw [extension.readUInt32 (address.value + headerAux3Offset) (by
    simp [headerAux3Offset, headerBytes] at owned ⊢; omega)]

/-- Successful live-header decoding exposes all checks that were discharged
by the checked reader. -/
theorem readLiveHeader_facts (state : MemoryState)
    (address : Word32) (header : Header)
    (read : state.readLiveHeader address = .ok header) :
    address.classify = .heap ∧
    Header.read state.memory address = .ok header ∧
    header.live = true ∧
    headerBytes ≤ header.allocationBytes.toNat ∧
    header.allocationBytes.toNat % target.heapAlignment = 0 ∧
    address.value + header.allocationBytes.toNat ≤ state.memory.size := by
  by_cases heap : address.classify = .heap
  · cases headerResult : Header.read state.memory address with
    | error failure =>
        simp_all [MemoryState.readLiveHeader, Bind.bind, Except.bind]
    | ok actual =>
        by_cases live : actual.live = true
        · by_cases minimum : headerBytes ≤ actual.allocationBytes.toNat
          · by_cases aligned :
                actual.allocationBytes.toNat % target.heapAlignment = 0
            · by_cases inBounds :
                address.value + actual.allocationBytes.toNat ≤ state.memory.size
              · simp [MemoryState.readLiveHeader, heap, headerResult, live,
                  minimum, aligned, inBounds, Bind.bind, Except.bind] at read
                change Except.ok actual = Except.ok header at read
                have actualEq : actual = header := Except.ok.inj read
                subst header
                exact ⟨heap, rfl, live, minimum, aligned, inBounds⟩
              · simp_all [MemoryState.readLiveHeader, Bind.bind, Except.bind]
            · simp_all [MemoryState.readLiveHeader, Bind.bind, Except.bind]
          · simp_all [MemoryState.readLiveHeader, Bind.bind, Except.bind]
        · simp_all [MemoryState.readLiveHeader, Bind.bind, Except.bind]
  · simp_all [MemoryState.readLiveHeader, Bind.bind, Except.bind]

/-- A live allocation whose full extent lies below the old cursor continues
to decode to the same checked header through a prefix extension. -/
theorem readLiveHeader_eq_ok {before after : MemoryState}
    (extension : before.PrefixExtension after)
    (address : Word32) (header : Header)
    (owned : address.value + headerBytes ≤ before.heapCursor)
    (read : before.readLiveHeader address = .ok header) :
    after.readLiveHeader address = .ok header := by
  obtain ⟨heap, headerRead, live, minimum, aligned, beforeBounds⟩ :=
    readLiveHeader_facts before address header read
  have headerReadAfter : Header.read after.memory address = .ok header := by
    rw [extension.readHeader address owned]
    exact headerRead
  have afterBounds :
      address.value + header.allocationBytes.toNat ≤ after.memory.size :=
    Nat.le_trans beforeBounds extension.memorySize
  simp [MemoryState.readLiveHeader, heap, headerReadAfter]
  simp only [Bind.bind, Except.bind]
  simp [live, minimum, aligned, afterBounds]
  rfl

end MemoryState.PrefixExtension

end Fir.Wasm.Concrete
