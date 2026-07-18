import Fir.Wasm.Concrete.ObjectFieldsCorrectness

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

end Fir.Wasm.Concrete
