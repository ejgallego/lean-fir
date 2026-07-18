import Fir.Wasm.Concrete.OwnershipFrameCorrectness

namespace Fir.Wasm.Concrete

/-- Exact byte-level postcondition for payload scrubbing before in-place
reuse. -/
structure ZeroBytesPost (before after : LinearMemory)
    (address count : Nat) : Prop where
  size : after.size = before.size
  zeroAt : ∀ offset, offset < count →
    after.readByte (address + offset) = .ok 0
  frame : ∀ other, other < address ∨ address + count ≤ other →
    after.readByte other = before.readByte other

/-- A checked zero-range write installs every requested zero, preserves memory
size, and frames every byte outside the half-open interval. -/
theorem LinearMemory.zeroBytes_spec (memory : LinearMemory)
    (address count : Nat) (inBounds : address + count ≤ memory.size) :
    ∃ result,
      memory.zeroBytes address count = .ok result ∧
      ZeroBytesPost memory result address count := by
  induction count generalizing memory address with
  | zero =>
      exact ⟨memory, rfl, ⟨rfl, by simp, by simp⟩⟩
  | succ count ih =>
      have addressInBounds : address < memory.size := by omega
      let middle := memory.set address 0 addressInBounds
      have firstWrite : memory.writeByte address 0 = .ok middle := by
        simp [LinearMemory.writeByte, addressInBounds, middle]
      have middleSize : middle.size = memory.size := by simp [middle]
      have tailInBounds : address + 1 + count ≤ middle.size := by omega
      obtain ⟨result, tailWrite, tailPost⟩ :=
        ih middle (address + 1) tailInBounds
      refine ⟨result, ?_, ?_⟩
      · unfold LinearMemory.zeroBytes
        rw [firstWrite]
        exact tailWrite
      · refine ⟨tailPost.size.trans middleSize, ?_, ?_⟩
        · intro offset offsetLt
          cases offset with
          | zero =>
              simp only [Nat.add_zero]
              rw [tailPost.frame address (by omega)]
              simp [middle, LinearMemory.readByte]
          | succ offset =>
              have tailZero := tailPost.zeroAt offset (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailZero
        · intro other outside
          have tailOutside :
              other < address + 1 ∨ address + 1 + count ≤ other := by omega
          rw [tailPost.frame other tailOutside]
          have different : address ≠ other := by omega
          exact LinearMemory.readByte_set_other memory address other 0
            addressInBounds different

theorem LinearMemory.zeroBytes_post (memory result : LinearMemory)
    (address count : Nat) (inBounds : address + count ≤ memory.size)
    (written : memory.zeroBytes address count = .ok result) :
    ZeroBytesPost memory result address count := by
  obtain ⟨actual, actualWrite, post⟩ :=
    memory.zeroBytes_spec address count inBounds
  rw [actualWrite] at written
  cases written
  exact post

/-- Scrubbing beginning at the payload boundary leaves every common-header
word unchanged. -/
theorem Header.read_of_zeroBytes_payload (before after : LinearMemory)
    (address : Word32) (count : Nat)
    (post : ZeroBytesPost before after (address.value + headerBytes) count) :
    Header.read after address = Header.read before address := by
  have wordFrame (offset : Nat) (insideHeader : offset + 4 ≤ headerBytes) :
      after.readUInt32 (address.value + offset) =
        before.readUInt32 (address.value + offset) := by
    unfold LinearMemory.readUInt32
    rw [post.frame (address.value + offset) (by omega)]
    rw [post.frame (address.value + offset + 1) (by omega)]
    rw [post.frame (address.value + offset + 2) (by omega)]
    rw [post.frame (address.value + offset + 3) (by omega)]
  unfold Header.read
  dsimp only
  rw [wordFrame headerKindOffset (by decide)]
  rw [wordFrame headerFlagsOffset (by decide)]
  rw [wordFrame headerRefCountOffset (by decide)]
  rw [wordFrame headerAllocationBytesOffset (by decide)]
  rw [wordFrame headerAux0Offset (by decide)]
  rw [wordFrame headerAux1Offset (by decide)]
  rw [wordFrame headerAux2Offset (by decide)]
  rw [wordFrame headerAux3Offset (by decide)]

theorem MemoryState.readLiveHeader_of_zeroBytes_payload
    (state : MemoryState) (result : LinearMemory) (address : Word32)
    (count : Nat)
    (post : ZeroBytesPost state.memory result
      (address.value + headerBytes) count) :
    ({ state with memory := result } : MemoryState).readLiveHeader address =
      state.readLiveHeader address := by
  have headerFrame := Header.read_of_zeroBytes_payload state.memory result
    address count post
  unfold MemoryState.readLiveHeader
  dsimp only
  rw [headerFrame, post.size]

/-- A payload scrub wholly inside the allocated prefix preserves the global
frontier invariant. -/
theorem MemoryState.FrontierInvariant.zeroBytes
    {state : MemoryState} {result : LinearMemory} {address count : Nat}
    (valid : state.FrontierInvariant)
    (beforeFrontier : address + count ≤ state.heapCursor)
    (written : state.memory.zeroBytes address count = .ok result) :
    ({ state with memory := result } : MemoryState).FrontierInvariant := by
  have inBounds : address + count ≤ state.memory.size :=
    Nat.le_trans beforeFrontier valid.cursorInBounds
  have post := state.memory.zeroBytes_post result address count inBounds written
  refine {
    cursorAligned := valid.cursorAligned
    cursorInBounds := by simpa [post.size] using valid.cursorInBounds
    unusedZero := ?_ }
  intro byte afterCursor finalInBounds
  change state.heapCursor ≤ byte at afterCursor
  change byte < result.size at finalInBounds
  have oldInBounds : byte < state.memory.size := by
    rw [← post.size]
    exact finalInBounds
  have oldZero := valid.unusedZero byte afterCursor oldInBounds
  have framed := post.frame byte (.inr
    (Nat.le_trans beforeFrontier afterCursor))
  cases resultByte : result[byte]? with
  | none => simp [LinearMemory.readByte, resultByte, oldZero] at framed
  | some value =>
      simp [LinearMemory.readByte, resultByte, oldZero] at framed
      subst value
      rfl

/-- Scrubbing one allocation payload produces a complete allocation frame for
every allocation whose full interval is disjoint from the target interval. -/
theorem MemoryState.AllocationFrame.ofZeroBytes
    {before after : MemoryState} {target other : Word32}
    {targetBytes otherBytes : Nat} {memory : LinearMemory}
    (resultEq : after = { before with memory })
    (targetMinimum : headerBytes ≤ targetBytes)
    (targetInBounds : target.value + targetBytes ≤ before.memory.size)
    (written : before.memory.zeroBytes (target.value + headerBytes)
      (targetBytes - headerBytes) = .ok memory)
    (disjoint : target.value + targetBytes ≤ other.value ∨
      other.value + otherBytes ≤ target.value) :
    before.AllocationFrame after other otherBytes := by
  have scrubEnd :
      target.value + headerBytes + (targetBytes - headerBytes) =
        target.value + targetBytes := by omega
  have scrubInBounds :
      target.value + headerBytes + (targetBytes - headerBytes) ≤
        before.memory.size := by
    rw [scrubEnd]
    exact targetInBounds
  have post := before.memory.zeroBytes_post memory
    (target.value + headerBytes) (targetBytes - headerBytes) scrubInBounds written
  subst after
  refine ⟨rfl, post.size, ?_⟩
  intro offset offsetLt
  change memory.readByte (other.value + offset) =
    before.memory.readByte (other.value + offset)
  apply post.frame
  cases disjoint with
  | inl targetBefore =>
      right
      rw [scrubEnd]
      omega
  | inr otherBefore =>
      left
      omega

end Fir.Wasm.Concrete
