import Fir.Wasm.Concrete.HeaderCorrectness

namespace Fir.Wasm.Concrete

namespace LinearMemory

theorem growToFit_size_ge (memory : LinearMemory) (requiredBytes : Nat) :
    requiredBytes ≤ (memory.growToFit requiredBytes).size := by
  unfold growToFit
  split
  · assumption
  · simp only [Array.size_append, Array.size_replicate]
    unfold wasmPageBytes
    omega

end LinearMemory

/-- Exact postcondition of a successful monotone allocation, before an object
header or payload is installed. -/
structure MemoryState.AllocatePost (before after : MemoryState)
    (requestedBytes : Nat) (address : Word32) : Prop where
  minimum : headerBytes ≤ requestedBytes
  memory : after.memory = before.memory.growToFit
    (align8 before.heapCursor + align8 requestedBytes)
  cursor : after.heapCursor = align8 before.heapCursor + align8 requestedBytes
  addressValue : address.value = align8 before.heapCursor
  addressClass : address.classify = .heap
  endWithinAddressSpace :
    address.value + align8 requestedBytes ≤ wordModulus
  endInBounds : address.value + align8 requestedBytes ≤ after.memory.size

theorem MemoryState.allocate_spec (state result : MemoryState)
    (requestedBytes : Nat) (address : Word32)
    (allocated : state.allocate requestedBytes = .ok (result, address)) :
    MemoryState.AllocatePost state result requestedBytes address := by
  have minimum : headerBytes ≤ requestedBytes := by
    by_cases enough : headerBytes ≤ requestedBytes
    · exact enough
    · have tooSmall : requestedBytes < headerBytes := Nat.lt_of_not_ge enough
      unfold MemoryState.allocate at allocated
      rw [if_pos tooSmall] at allocated
      change Except.error (MemoryError.invalidAllocationSize requestedBytes) =
        Except.ok (result, address) at allocated
      contradiction
  unfold MemoryState.allocate at allocated
  rw [if_neg (Nat.not_lt.mpr minimum)] at allocated
  dsimp only at allocated
  by_cases exhausted :
      wordModulus < align8 state.heapCursor + align8 requestedBytes
  · rw [if_pos exhausted] at allocated
    contradiction
  · rw [if_neg exhausted] at allocated
    cases hword : Word32.ofNat? (align8 state.heapCursor) with
    | none =>
        rw [hword] at allocated
        change Except.error (MemoryError.addressSpaceExhausted
          (align8 state.heapCursor)) = Except.ok (result, address) at allocated
        contradiction
    | some actual =>
        rw [hword] at allocated
        let next : MemoryState := {
          memory := state.memory.growToFit
            (align8 state.heapCursor + align8 requestedBytes)
          heapCursor := align8 state.heapCursor + align8 requestedBytes }
        change (if actual.classify = .heap then Except.ok (next, actual)
          else Except.error (MemoryError.invalidObjectAddress actual)) =
            Except.ok (result, address) at allocated
        by_cases heap : actual.classify = .heap
        · rw [if_pos heap] at allocated
          have addressValue : actual.value = align8 state.heapCursor := by
            unfold Word32.ofNat? at hword
            split at hword
            · cases hword
              rfl
            · contradiction
          have pairEq : (next, actual) = (result, address) :=
            Except.ok.inj allocated
          have resultEq : next = result := congrArg Prod.fst pairEq
          have addressEq : actual = address := congrArg Prod.snd pairEq
          rw [← resultEq, ← addressEq]
          refine {
            minimum
            memory := rfl
            cursor := rfl
            addressValue
            addressClass := heap
            endWithinAddressSpace := ?_
            endInBounds := ?_ }
          · rw [addressValue]
            omega
          · rw [addressValue]
            exact LinearMemory.growToFit_size_ge state.memory
              (align8 state.heapCursor + align8 requestedBytes)
        · rw [if_neg heap] at allocated
          contradiction

/--
Finite wasm32 address-space headroom at one concrete heap frontier.

This budget is measured in already-aligned bytes so a source evaluation can
sum the allocations on its selected path and consume them one by one. Linear
memory itself grows on demand. Positivity is kept here because physical zero
is reserved for erased values and reuse tokens; frontier alignment is supplied
separately by the ordinary heap invariant.
-/
structure MemoryState.AddressSpaceBudget (state : MemoryState)
    (remainingBytes : Nat) : Prop where
  cursorPositive : 0 < state.heapCursor
  endWithinAddressSpace :
    state.heapCursor + remainingBytes ≤ wordModulus

/--
Reserving fewer bytes preserves an address-space budget. This is the
resource-logic weakening rule used when a declaration reserves a uniform
upper bound but its concrete representation takes a nonallocating branch.
-/
theorem MemoryState.AddressSpaceBudget.weaken
    {state : MemoryState} {largerBytes smallerBytes : Nat}
    (budget : state.AddressSpaceBudget largerBytes)
    (smaller : smallerBytes ≤ largerBytes) :
    state.AddressSpaceBudget smallerBytes := {
  cursorPositive := budget.cursorPositive
  endWithinAddressSpace :=
    Nat.le_trans (Nat.add_le_add_left smaller state.heapCursor)
      budget.endWithinAddressSpace }

/-- One allocation's exact view of the reusable address-space budget. -/
abbrev MemoryState.AllocationCapacity (state : MemoryState)
    (requestedBytes : Nat) : Prop :=
  state.AddressSpaceBudget (align8 requestedBytes)

/-- A larger source-computed budget supplies any one aligned allocation that
fits inside it. -/
theorem MemoryState.AddressSpaceBudget.allocationCapacity
    {state : MemoryState} {remainingBytes requestedBytes : Nat}
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : align8 requestedBytes ≤ remainingBytes) :
    state.AllocationCapacity requestedBytes := by
  exact {
    cursorPositive := budget.cursorPositive
    endWithinAddressSpace := by
      exact Nat.le_trans (Nat.add_le_add_left fits state.heapCursor)
        budget.endWithinAddressSpace }

/--
Successful allocation consumes exactly its aligned request from a
source-computed address-space budget. This is the transport law needed by the
future structural proof over allocating direct-value spines.
-/
theorem MemoryState.AddressSpaceBudget.consume
    {before after : MemoryState} {remainingBytes requestedBytes : Nat}
    {address : Word32}
    (budget : before.AddressSpaceBudget remainingBytes)
    (cursorAligned : before.heapCursor % target.heapAlignment = 0)
    (fits : align8 requestedBytes ≤ remainingBytes)
    (post : before.AllocatePost after requestedBytes address) :
    after.AddressSpaceBudget (remainingBytes - align8 requestedBytes) := by
  have alignedCursor : align8 before.heapCursor = before.heapCursor := by
    unfold align8
    simp [target] at cursorAligned
    omega
  constructor
  · rw [post.cursor, alignedCursor]
    exact Nat.lt_of_lt_of_le budget.cursorPositive (Nat.le_add_right _ _)
  · rw [post.cursor, alignedCursor]
    have within := budget.endWithinAddressSpace
    omega

/--
An aligned live frontier with enough wasm32 address-space headroom makes the
checked raw allocator constructive. No pre-existing linear-memory size premise
is needed because `growToFit` extends memory through the requested end.
-/
theorem MemoryState.allocate_eq_ok_of_capacity
    (state : MemoryState) (requestedBytes : Nat)
    (minimum : headerBytes ≤ requestedBytes)
    (cursorAligned : state.heapCursor % target.heapAlignment = 0)
    (capacity : state.AllocationCapacity requestedBytes) :
    ∃ result address,
      state.allocate requestedBytes = .ok (result, address) := by
  have alignedCursor : align8 state.heapCursor = state.heapCursor := by
    unfold align8
    simp [target] at cursorAligned
    omega
  have requestedEnd :
      align8 state.heapCursor + align8 requestedBytes ≤ wordModulus := by
    simpa [alignedCursor] using capacity.endWithinAddressSpace
  have addressLt : align8 state.heapCursor < wordModulus := by
    have positiveBytes : 0 < align8 requestedBytes := by
      have := align8_ge requestedBytes
      have : 0 < headerBytes := by decide
      omega
    omega
  let address : Word32 := ⟨align8 state.heapCursor, addressLt⟩
  have addressOption :
      Word32.ofNat? (align8 state.heapCursor) = some address := by
    simp [Word32.ofNat?, address, addressLt]
  have addressHeap : address.classify = .heap := by
    have cursorNe : state.heapCursor ≠ 0 :=
      Nat.ne_of_gt capacity.cursorPositive
    have cursorMod8 : state.heapCursor % 8 = 0 := by
      simpa [target] using cursorAligned
    have cursorNotOdd : state.heapCursor % 2 ≠ 1 := by
      omega
    simp [Word32.classify, address, alignedCursor,
      cursorNe, cursorNotOdd, cursorMod8, cursorAligned]
  let result : MemoryState := {
    memory := state.memory.growToFit
      (align8 state.heapCursor + align8 requestedBytes)
    heapCursor := align8 state.heapCursor + align8 requestedBytes }
  refine ⟨result, address, ?_⟩
  unfold MemoryState.allocate
  rw [if_neg (Nat.not_lt.mpr minimum)]
  dsimp only
  rw [if_neg (Nat.not_lt.mpr requestedEnd), addressOption]
  simp [addressHeap, result, pure, Except.pure]

@[simp] theorem align8_align8 (bytes : Nat) : align8 (align8 bytes) = align8 bytes := by
  unfold align8
  omega

/-- A successful object allocation installs an exactly decodable common
header at the fresh address. Payload writers can extend this result using the
header frame theorem. -/
theorem MemoryState.allocateObject_header (state result : MemoryState)
    (kind : ObjectKind) (payloadBytes : Nat) (persistent : Bool)
    (aux0 aux1 aux2 aux3 : UInt32) (address : Word32)
    (allocated : state.allocateObject kind payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (result, address)) :
    ∃ middle,
      state.allocate (align8 (headerBytes + payloadBytes)) = .ok (middle, address) ∧
      (Header.forAllocation kind (align8 (headerBytes + payloadBytes))
        persistent aux0 aux1 aux2 aux3).write middle.memory address =
          .ok result.memory ∧
      result.heapCursor = middle.heapCursor ∧
      Header.read result.memory address = .ok
        (Header.forAllocation kind (align8 (headerBytes + payloadBytes))
          persistent aux0 aux1 aux2 aux3) := by
  let allocationBytes := align8 (headerBytes + payloadBytes)
  let header := Header.forAllocation kind allocationBytes persistent aux0 aux1 aux2 aux3
  unfold MemoryState.allocateObject at allocated
  dsimp only at allocated
  cases allocateResult : state.allocate allocationBytes with
  | error failure =>
      have allocateEq : state.allocate (align8 (headerBytes + payloadBytes)) =
          .error failure := by
        simpa [allocationBytes] using allocateResult
      rw [allocateEq] at allocated
      change Except.error failure = Except.ok (result, address) at allocated
      contradiction
  | ok pair =>
      rcases pair with ⟨middle, actualAddress⟩
      have allocateEq : state.allocate (align8 (headerBytes + payloadBytes)) =
          .ok (middle, actualAddress) := by
        simpa [allocationBytes] using allocateResult
      rw [allocateEq] at allocated
      change (do
        let memory ← header.write middle.memory actualAddress
        return ({ middle with memory }, actualAddress)) = .ok (result, address) at allocated
      cases writeResult : header.write middle.memory actualAddress with
      | error failure =>
          rw [writeResult] at allocated
          change Except.error failure = Except.ok (result, address) at allocated
          contradiction
      | ok finalMemory =>
          rw [writeResult] at allocated
          change Except.ok ({ middle with memory := finalMemory }, actualAddress) =
            Except.ok (result, address) at allocated
          have pairEq : ({ middle with memory := finalMemory }, actualAddress) =
              (result, address) := Except.ok.inj allocated
          have resultEq : { middle with memory := finalMemory } = result :=
            congrArg Prod.fst pairEq
          have addressEq : actualAddress = address := congrArg Prod.snd pairEq
          have allocationPost := MemoryState.allocate_spec state middle allocationBytes
            actualAddress allocateResult
          have headerInBounds :
              actualAddress.value + headerBytes ≤ middle.memory.size := by
            have := allocationPost.endInBounds
            have aligned : align8 allocationBytes = allocationBytes := by
              simp [allocationBytes]
            rw [aligned] at this
            have minimum := align8_ge (headerBytes + payloadBytes)
            dsimp only [allocationBytes] at this
            omega
          have headerRead : Header.read finalMemory actualAddress = .ok header :=
            Header.read_of_write_eq_ok middle.memory finalMemory actualAddress header
              headerInBounds writeResult
          rw [← resultEq, ← addressEq]
          exact ⟨middle, rfl, writeResult, rfl, headerRead⟩

/--
Object allocation is constructive from the same raw address-space capacity.
The common header introduces no additional resource premise: it is written
inside the extent made in-bounds by the successful growing allocation.
-/
theorem MemoryState.allocateObject_eq_ok_of_capacity
    (state : MemoryState) (kind : ObjectKind) (payloadBytes : Nat)
    (persistent : Bool) (aux0 aux1 aux2 aux3 : UInt32)
    (cursorAligned : state.heapCursor % target.heapAlignment = 0)
    (capacity :
      state.AllocationCapacity (align8 (headerBytes + payloadBytes))) :
    ∃ result address,
      state.allocateObject kind payloadBytes persistent aux0 aux1 aux2 aux3 =
        .ok (result, address) := by
  let allocationBytes := align8 (headerBytes + payloadBytes)
  obtain ⟨middle, address, allocated⟩ :=
    state.allocate_eq_ok_of_capacity allocationBytes
      (by
        have := align8_ge (headerBytes + payloadBytes)
        dsimp only [allocationBytes]
        omega)
      cursorAligned capacity
  have post := MemoryState.allocate_spec state middle allocationBytes address
    allocated
  have allocationAligned : align8 allocationBytes = allocationBytes := by
    simp [allocationBytes]
  have headerInBounds : address.value + headerBytes ≤ middle.memory.size := by
    have endInBounds := post.endInBounds
    rw [allocationAligned] at endInBounds
    have minimum := align8_ge (headerBytes + payloadBytes)
    dsimp only [allocationBytes] at endInBounds
    omega
  let header :=
    Header.forAllocation kind allocationBytes persistent aux0 aux1 aux2 aux3
  obtain ⟨memory, written, _⟩ :=
    Header.write_spec middle.memory address header headerInBounds
  refine ⟨{ middle with memory }, address, ?_⟩
  unfold MemoryState.allocateObject
  dsimp only
  rw [show align8 (headerBytes + payloadBytes) = allocationBytes by rfl]
  rw [allocated]
  change
    (do
      let memory ← header.write middle.memory address
      return ({ middle with memory }, address)) =
        .ok ({ middle with memory }, address)
  rw [written]
  rfl

/--
A successful checked object allocation consumes exactly its aligned object
extent from a larger source-path address-space budget. Header installation
changes memory bytes but not the raw allocator frontier.
-/
theorem MemoryState.AddressSpaceBudget.allocateObject
    {state result : MemoryState} {remainingBytes payloadBytes : Nat}
    {kind : ObjectKind} {persistent : Bool}
    {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (budget : state.AddressSpaceBudget remainingBytes)
    (cursorAligned : state.heapCursor % target.heapAlignment = 0)
    (fits : align8 (headerBytes + payloadBytes) ≤ remainingBytes)
    (allocated :
      state.allocateObject kind payloadBytes persistent aux0 aux1 aux2 aux3 =
        .ok (result, address)) :
    result.AddressSpaceBudget
      (remainingBytes - align8 (headerBytes + payloadBytes)) := by
  obtain ⟨middle, rawAllocation, _, cursorEq, _⟩ :=
    MemoryState.allocateObject_header state result kind payloadBytes persistent
      aux0 aux1 aux2 aux3 address allocated
  have rawPost :=
    MemoryState.allocate_spec state middle
      (align8 (headerBytes + payloadBytes)) address rawAllocation
  have consumed :=
    budget.consume cursorAligned (by simpa using fits) rawPost
  exact {
    cursorPositive := by
      rw [cursorEq]
      exact consumed.cursorPositive
    endWithinAddressSpace := by
      rw [cursorEq]
      simpa using consumed.endWithinAddressSpace }

/-- A successful object allocation passes the full checked live-header read,
including address class, liveness, aligned allocation size, and bounds. -/
theorem MemoryState.readLiveHeader_of_allocateObject_eq_ok
    (state result : MemoryState) (kind : ObjectKind) (payloadBytes : Nat)
    (persistent : Bool) (aux0 aux1 aux2 aux3 : UInt32) (address : Word32)
    (allocated : state.allocateObject kind payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (result, address)) :
    result.readLiveHeader address = .ok
      (Header.forAllocation kind (align8 (headerBytes + payloadBytes))
        persistent aux0 aux1 aux2 aux3) := by
  let allocationBytes := align8 (headerBytes + payloadBytes)
  let header := Header.forAllocation kind allocationBytes persistent aux0 aux1 aux2 aux3
  obtain ⟨middle, allocateResult, headerWrite, _, headerRead⟩ :=
    MemoryState.allocateObject_header state result kind payloadBytes persistent
      aux0 aux1 aux2 aux3 address allocated
  have allocationPost := MemoryState.allocate_spec state middle allocationBytes
    address allocateResult
  have aligned : align8 allocationBytes = allocationBytes := by
    simp [allocationBytes]
  have headerInBounds : address.value + headerBytes ≤ middle.memory.size := by
    have := allocationPost.endInBounds
    rw [aligned] at this
    have minimum := align8_ge (headerBytes + payloadBytes)
    dsimp only [allocationBytes] at this
    omega
  have finalSize := Header.write_preserves_size middle.memory result.memory address
    header headerInBounds headerWrite
  have addressNonzero : address.value ≠ 0 := by
    intro zero
    have heap := allocationPost.addressClass
    simp [Word32.classify, zero] at heap
  have allocationLt : allocationBytes < UInt32.size := by
    have within := allocationPost.endWithinAddressSpace
    rw [aligned] at within
    have belowWordModulus : allocationBytes < wordModulus := by omega
    simpa [wordModulus] using belowWordModulus
  have allocationToNat : (UInt32.ofNat allocationBytes).toNat = allocationBytes :=
    UInt32.toNat_ofNat_of_lt' allocationLt
  have minimumBytes : headerBytes ≤ allocationBytes := by
    have := align8_ge (headerBytes + payloadBytes)
    dsimp only [allocationBytes]
    omega
  have alignedBytes : allocationBytes % target.heapAlignment = 0 := by
    change align8 (headerBytes + payloadBytes) % 8 = 0
    exact align8_mod (headerBytes + payloadBytes)
  have finalInBounds : address.value + allocationBytes ≤ result.memory.size := by
    have := allocationPost.endInBounds
    rw [aligned] at this
    omega
  simp [MemoryState.readLiveHeader, allocationPost.addressClass, headerRead]
  change (if header.live = true then
    if ((headerBytes ≤ header.allocationBytes.toNat ∧
        header.allocationBytes.toNat % target.heapAlignment = 0) ∧
        address.value + header.allocationBytes.toNat ≤ result.memory.size) then
      Except.ok header
    else Except.error (MemoryError.malformedHeader address.value
      header.allocationBytes.toNat)
    else Except.error (MemoryError.deadObject address)) = Except.ok header
  simp [header, Header.forAllocation, allocationToNat, minimumBytes,
    alignedBytes, finalInBounds]

end Fir.Wasm.Concrete
