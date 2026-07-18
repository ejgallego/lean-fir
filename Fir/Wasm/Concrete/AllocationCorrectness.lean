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
