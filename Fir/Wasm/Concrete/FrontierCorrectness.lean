import Fir.Wasm.Concrete.AllocationCorrectness

namespace Fir.Wasm.Concrete

/-- The monotone allocator owns the prefix below `heapCursor`; every byte in
the as-yet unallocated suffix is still zero.  This is the concrete invariant
that justifies zero-initialized constructor fields without assuming anything
about ambient WebAssembly memory. -/
structure MemoryState.FrontierInvariant (state : MemoryState) : Prop where
  cursorAligned : state.heapCursor % target.heapAlignment = 0
  cursorInBounds : state.heapCursor ≤ state.memory.size
  unusedZero : ∀ address,
    state.heapCursor ≤ address →
    address < state.memory.size →
    state.memory[address]? = some 0

@[simp] theorem align8_eq_of_mod_eq_zero (bytes : Nat) (aligned : bytes % 8 = 0) :
    align8 bytes = bytes := by
  unfold align8
  omega

theorem MemoryState.initial_frontierInvariant :
    MemoryState.initial.FrontierInvariant := by
  refine {
    cursorAligned := by decide
    cursorInBounds := by
      simp [MemoryState.initial, LinearMemory.withPages, heapBase, wasmPageBytes]
    unusedZero := ?_ }
  intro address _ inBounds
  have addressBound : address < wasmPageBytes := by
    simpa [MemoryState.initial, LinearMemory.withPages] using inBounds
  simp [MemoryState.initial, LinearMemory.withPages, addressBound]

/-- Growing memory preserves the zero suffix, and any newly appended pages
are zero by construction. -/
theorem LinearMemory.growToFit_zero_from (memory : LinearMemory)
    (oldFrontier requiredBytes : Nat)
    (zeroFrom : ∀ address, oldFrontier ≤ address →
      address < memory.size → memory[address]? = some 0) :
    ∀ address, oldFrontier ≤ address →
      address < (memory.growToFit requiredBytes).size →
      (memory.growToFit requiredBytes)[address]? = some 0 := by
  intro address afterFrontier inBounds
  unfold LinearMemory.growToFit at inBounds ⊢
  split
  next enough =>
    simp only [if_pos enough] at inBounds ⊢
    exact zeroFrom address afterFrontier inBounds
  next notEnough =>
    simp only [if_neg notEnough] at inBounds ⊢
    by_cases inOld : address < memory.size
    · rw [Array.getElem?_append, if_pos inOld]
      exact zeroFrom address afterFrontier inOld
    · rw [Array.getElem?_append, if_neg inOld, Array.getElem?_replicate]
      rw [if_pos (by
        simp only [Array.size_append, Array.size_replicate] at inBounds
        omega)]

/-- Every successful allocation advances an aligned in-bounds frontier and
retains a zero suffix after the newly reserved extent. -/
theorem MemoryState.FrontierInvariant.allocate
    {state result : MemoryState} {requestedBytes : Nat} {address : Word32}
    (valid : state.FrontierInvariant)
    (allocated : state.allocate requestedBytes = .ok (result, address)) :
    result.FrontierInvariant := by
  have post := MemoryState.allocate_spec state result requestedBytes address allocated
  have cursorAligned : align8 state.heapCursor = state.heapCursor := by
    exact align8_eq_of_mod_eq_zero state.heapCursor (by
      simpa [target] using valid.cursorAligned)
  have frontierLe : state.heapCursor ≤ result.heapCursor := by
    rw [post.cursor, cursorAligned]
    omega
  have memoryEq :
      result.memory = state.memory.growToFit result.heapCursor := by
    rw [post.memory, post.cursor]
  refine {
    cursorAligned := ?_
    cursorInBounds := ?_
    unusedZero := ?_ }
  · rw [post.cursor]
    simp [target, align8]
  · rw [post.cursor]
    have endInBounds := post.endInBounds
    rw [post.addressValue] at endInBounds
    exact endInBounds
  · intro byte afterCursor inBounds
    rw [memoryEq]
    apply LinearMemory.growToFit_zero_from state.memory state.heapCursor
      result.heapCursor valid.unusedZero byte (Nat.le_trans frontierLe afterCursor)
    simpa [memoryEq] using inBounds

/-- Writing a header wholly inside the allocated prefix preserves alignment,
bounds, and every unused zero byte at or beyond the frontier. -/
theorem MemoryState.FrontierInvariant.writeHeader
    {state : MemoryState} {result : LinearMemory} {address : Word32}
    {header : Header} (valid : state.FrontierInvariant)
    (beforeFrontier : address.value + headerBytes ≤ state.heapCursor)
    (written : header.write state.memory address = .ok result) :
    ({ state with memory := result } : MemoryState).FrontierInvariant := by
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans beforeFrontier valid.cursorInBounds
  have finalSize := Header.write_preserves_size state.memory result address header
    headerInBounds written
  refine {
    cursorAligned := valid.cursorAligned
    cursorInBounds := by simpa [finalSize] using valid.cursorInBounds
    unusedZero := ?_ }
  intro byte afterCursor finalInBounds
  change state.heapCursor ≤ byte at afterCursor
  change byte < result.size at finalInBounds
  have oldInBounds : byte < state.memory.size := by
    rw [← finalSize]
    exact finalInBounds
  have oldZero := valid.unusedZero byte afterCursor oldInBounds
  have disjoint : address.value + headerBytes ≤ byte :=
    Nat.le_trans beforeFrontier afterCursor
  have framed := Header.readByte_of_write_eq_ok_other state.memory result address
    header byte headerInBounds written (.inr disjoint)
  cases resultByte : result[byte]? with
  | none => simp [LinearMemory.readByte, resultByte, oldZero] at framed
  | some value =>
      simp [LinearMemory.readByte, resultByte, oldZero] at framed
      subst value
      rfl

/-- Object allocation preserves the zero-frontier invariant after installing
its common header. -/
theorem MemoryState.FrontierInvariant.allocateObject
    {state result : MemoryState} {kind : ObjectKind} {payloadBytes : Nat}
    {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (valid : state.FrontierInvariant)
    (allocated : state.allocateObject kind payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (result, address)) :
    result.FrontierInvariant := by
  obtain ⟨middle, allocateResult, headerWrite, cursorEq, _⟩ :=
    MemoryState.allocateObject_header state result kind payloadBytes persistent
      aux0 aux1 aux2 aux3 address allocated
  have middleValid := valid.allocate allocateResult
  have allocationPost := MemoryState.allocate_spec state middle
    (align8 (headerBytes + payloadBytes)) address allocateResult
  have allocationAligned :
      align8 (align8 (headerBytes + payloadBytes)) =
        align8 (headerBytes + payloadBytes) := by simp
  have headerBeforeFrontier : address.value + headerBytes ≤ middle.heapCursor := by
    rw [allocationPost.addressValue, allocationPost.cursor, allocationAligned]
    have := align8_ge (headerBytes + payloadBytes)
    omega
  have finalValid := middleValid.writeHeader headerBeforeFrontier headerWrite
  have stateEq : ({ middle with memory := result.memory } : MemoryState) = result := by
    cases middle
    cases result
    simp_all
  simpa [stateEq] using finalValid

/-- Before kind-specific payload writers run, every byte after the installed
header and before the new allocation end is still zero. -/
theorem MemoryState.FrontierInvariant.allocateObject_payload_zero
    {state result : MemoryState} {kind : ObjectKind} {payloadBytes : Nat}
    {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (valid : state.FrontierInvariant)
    (allocated : state.allocateObject kind payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (result, address)) :
    ∀ byte,
      address.value + headerBytes ≤ byte →
      byte < address.value + align8 (headerBytes + payloadBytes) →
      result.memory[byte]? = some 0 := by
  obtain ⟨middle, allocateResult, headerWrite, _, _⟩ :=
    MemoryState.allocateObject_header state result kind payloadBytes persistent
      aux0 aux1 aux2 aux3 address allocated
  have allocationPost := MemoryState.allocate_spec state middle
    (align8 (headerBytes + payloadBytes)) address allocateResult
  have oldCursorAligned : align8 state.heapCursor = state.heapCursor := by
    exact align8_eq_of_mod_eq_zero state.heapCursor (by
      simpa [target] using valid.cursorAligned)
  have allocationAligned :
      align8 (align8 (headerBytes + payloadBytes)) =
        align8 (headerBytes + payloadBytes) := by simp
  have grownZero : ∀ byte, state.heapCursor ≤ byte →
      byte < middle.memory.size → middle.memory[byte]? = some 0 := by
    rw [allocationPost.memory]
    exact LinearMemory.growToFit_zero_from state.memory state.heapCursor
      (align8 state.heapCursor + align8 (align8 (headerBytes + payloadBytes)))
      valid.unusedZero
  have headerInBounds : address.value + headerBytes ≤ middle.memory.size := by
    have endInBounds := allocationPost.endInBounds
    rw [allocationAligned] at endInBounds
    have minimum := align8_ge (headerBytes + payloadBytes)
    omega
  have finalSize := Header.write_preserves_size middle.memory result.memory address
    (Header.forAllocation kind (align8 (headerBytes + payloadBytes)) persistent
      aux0 aux1 aux2 aux3) headerInBounds headerWrite
  intro byte afterHeader beforeEnd
  have afterOldCursor : state.heapCursor ≤ byte := by
    rw [allocationPost.addressValue, oldCursorAligned] at afterHeader
    omega
  have middleInBounds : byte < middle.memory.size := by
    have endInBounds := allocationPost.endInBounds
    rw [allocationAligned] at endInBounds
    omega
  have middleZero := grownZero byte afterOldCursor middleInBounds
  have framed := Header.readByte_of_write_eq_ok_other middle.memory result.memory
    address (Header.forAllocation kind (align8 (headerBytes + payloadBytes))
      persistent aux0 aux1 aux2 aux3) byte headerInBounds headerWrite (.inr afterHeader)
  cases resultByte : result.memory[byte]? with
  | none => simp [LinearMemory.readByte, resultByte, middleZero] at framed
  | some value =>
      simp [LinearMemory.readByte, resultByte, middleZero] at framed
      subst value
      rfl

end Fir.Wasm.Concrete
