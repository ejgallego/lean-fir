import Fir.Wasm.Concrete.Memory
import Interpreter.Wasm.Wp.Atomic

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Wasm-resident linear-memory refinement

The concrete host and the Wasm interpreter intentionally use different
physical memory models: W6 uses a finite byte array, while Talos represents
the same Wasm memory extensionally as a byte function plus a page count.  This
relation is the shared proof boundary for resident helpers.  Instruction
proofs should transport loads and stores through it instead of restating
layout facts for each helper.
-/

/-- A Talos memory and a W6 concrete heap expose exactly the same in-bounds
bytes and the same page-aligned extent.  The explicit wasm32 bound makes
address conversion facts available without smuggling them into individual
instruction proofs. -/
structure ResidentMemoryRel (heap : MemoryState) (memory : Wasm.Mem) : Prop where
  size_eq : heap.memory.size = memory.pages * wasmPageBytes
  size_le : heap.memory.size ≤ UInt32.size
  byte_eq : ∀ address, (inBounds : address < heap.memory.size) →
    memory.bytes address = heap.memory[address]

namespace ResidentMemoryRel

/-- Writing back the word just read from one address restores the Talos
memory extensionally.  Resident ABI casts use this to justify their temporary
scratch-slot overwrite without exposing the byte proof at every call site. -/
theorem write32_read32_self (memory : Wasm.Mem) (address : UInt32) :
    memory.write32 address (memory.read32 address) = memory := by
  cases memory
  simp [Wasm.Mem.write32, Wasm.Mem.read32]
  funext other
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  rfl

/-- A 32-bit Talos store is immediately observable by a matching load. -/
theorem read32_write32_self
    (memory : Wasm.Mem) (address value : UInt32) :
    (memory.write32 address value).read32 address = value := by
  cases memory
  simp [Wasm.Mem.write32, Wasm.Mem.read32]
  bv_decide

/-- Restoring the word observed before a temporary 32-bit overwrite recovers
the original memory, including every byte outside the scratch lane. -/
theorem write32_restore (memory : Wasm.Mem) (address value : UInt32) :
    (memory.write32 address value).write32 address
        (memory.read32 address) = memory := by
  cases memory
  simp [Wasm.Mem.write32, Wasm.Mem.read32]
  funext other
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  rfl

theorem initial :
    ResidentMemoryRel MemoryState.initial (Wasm.Mem.empty 1) := by
  constructor
  · simp [MemoryState.initial, LinearMemory.withPages, Wasm.Mem.empty,
      wasmPageBytes]
  · simp [MemoryState.initial, LinearMemory.withPages, UInt32.size,
      wasmPageBytes]
  · intro address inBounds
    simp [MemoryState.initial, LinearMemory.withPages, Wasm.Mem.empty]

theorem address_lt_uint32
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address bytes : Nat}
    (inBounds : address + bytes < heap.memory.size) :
    address < UInt32.size := by
  have addressInBounds : address < heap.memory.size := by omega
  exact Nat.lt_of_lt_of_le addressInBounds related.size_le

theorem address_roundtrip
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address bytes : Nat}
    (inBounds : address + bytes < heap.memory.size) :
    (UInt32.ofNat address).toNat = address := by
  exact UInt32.toNat_ofNat_of_lt' (related.address_lt_uint32 inBounds)

theorem readByte_eq
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} (inBounds : address < heap.memory.size) :
    heap.memory.readByte address = .ok (memory.bytes address) := by
  simp [LinearMemory.readByte, inBounds, related.byte_eq address inBounds]

theorem readByte_eq_read8
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} (inBounds : address < heap.memory.size) :
    heap.memory.readByte address =
      .ok (memory.read8 (UInt32.ofNat address)) := by
  rw [related.readByte_eq inBounds]
  simp [Wasm.Mem.read8,
    UInt32.toNat_ofNat_of_lt' (related.address_lt_uint32 (bytes := 0) inBounds)]

theorem readUInt32_eq_read32
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} (inBounds : address + 3 < heap.memory.size) :
    heap.memory.readUInt32 address =
      .ok (memory.read32 (UInt32.ofNat address)) := by
  have h0 : address < heap.memory.size := by omega
  have h1 : address + 1 < heap.memory.size := by omega
  have h2 : address + 2 < heap.memory.size := by omega
  have h3 : address + 3 < heap.memory.size := inBounds
  unfold LinearMemory.readUInt32
  rw [related.readByte_eq h0, related.readByte_eq h1,
    related.readByte_eq h2, related.readByte_eq h3]
  simp only [bind, Except.bind, pure, Except.pure]
  congr 1
  unfold Wasm.Mem.read32
  rw [related.address_roundtrip inBounds]
  simp only [related.byte_eq address h0, related.byte_eq (address + 1) h1,
    related.byte_eq (address + 2) h2, related.byte_eq (address + 3) h3]
  bv_decide

/-- One Wasm `i32.store` and W6's checked 32-bit store preserve the common
memory relation.  This is the byte-level frame theorem used by allocator,
header, field, cache, and scratch-slot proofs. -/
theorem writeUInt32
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} {value : UInt32} {result : LinearMemory}
    (inBounds : address + 3 < heap.memory.size)
    (written : heap.memory.writeUInt32 address value = .ok result) :
    ResidentMemoryRel { heap with memory := result }
      (memory.write32 (UInt32.ofNat address) value) := by
  obtain ⟨actual, actualWrite, actualSize, byte0, byte1, byte2, byte3, frame⟩ :=
    LinearMemory.writeUInt32_spec heap.memory address value inBounds
  rw [actualWrite] at written
  cases written
  have roundtrip : (UInt32.ofNat address).toNat = address :=
    related.address_roundtrip inBounds
  have h0 : address < result.size := by simpa [actualSize] using (by omega :
    address < heap.memory.size)
  have h1 : address + 1 < result.size := by simpa [actualSize] using (by omega :
    address + 1 < heap.memory.size)
  have h2 : address + 2 < result.size := by simpa [actualSize] using (by omega :
    address + 2 < heap.memory.size)
  have h3 : address + 3 < result.size := by simpa [actualSize] using inBounds
  have at0 : result[address] = (value &&& 0xff).toUInt8 := by
    simp [LinearMemory.readByte, h0] at byte0
    rw [byte0]
    simp [LinearMemory.byte32]
    bv_decide
  have at1 : result[address + 1] = ((value >>> 8) &&& 0xff).toUInt8 := by
    simp [LinearMemory.readByte, h1] at byte1
    rw [byte1]
    simp [LinearMemory.byte32]
    bv_decide
  have at2 : result[address + 2] = ((value >>> 16) &&& 0xff).toUInt8 := by
    simp [LinearMemory.readByte, h2] at byte2
    rw [byte2]
    simp [LinearMemory.byte32]
    bv_decide
  have at3 : result[address + 3] = ((value >>> 24) &&& 0xff).toUInt8 := by
    simp [LinearMemory.readByte, h3] at byte3
    rw [byte3]
    simp [LinearMemory.byte32]
    bv_decide
  constructor
  · simpa [Wasm.Mem.write32, actualSize] using related.size_eq
  · simpa [actualSize] using related.size_le
  · intro other otherInBounds
    simp only [Wasm.Mem.write32, roundtrip]
    by_cases eq0 : other = address
    · subst other
      simpa using at0.symm
    by_cases eq1 : other = address + 1
    · subst other
      simp [at1]
    by_cases eq2 : other = address + 2
    · subst other
      simp [at2]
    by_cases eq3 : other = address + 3
    · subst other
      simp [at3]
    simp only [eq0, eq1, eq2, eq3, if_false]
    have originalInBounds : other < heap.memory.size := by
      simpa [actualSize] using otherInBounds
    have unchanged : LinearMemory.readByte result other =
        LinearMemory.readByte heap.memory other :=
      frame other (Ne.symm eq0) (Ne.symm eq1) (Ne.symm eq2) (Ne.symm eq3)
    simp [LinearMemory.readByte, otherInBounds, originalInBounds] at unchanged
    rw [unchanged]
    exact related.byte_eq other originalInBounds

end ResidentMemoryRel

/-- Store-level packaging used by resident instruction and helper theorems.
More resident globals, starting with the allocator cursor, can be added here
without changing the byte-level relation. -/
structure ResidentStoreRel (heap : MemoryState) (store : Wasm.Store α) : Prop where
  memory : ResidentMemoryRel heap store.mem

end FirTalos.Concrete
