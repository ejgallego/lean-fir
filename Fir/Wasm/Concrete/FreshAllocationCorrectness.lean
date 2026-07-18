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

end Fir.Wasm.Concrete
