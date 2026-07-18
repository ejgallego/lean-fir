import Fir.Wasm.Concrete.Refinement
import Std.Tactic.BVDecide

namespace Fir.Wasm.Concrete

/-- Failures produced by checked concrete-memory operations. These remain
separate from source `RuntimeFault`s and will be embedded in the structured
target-failure boundary when concrete imports replace semantic hosts. -/
inductive MemoryError where
  | outOfBounds (address bytes memoryBytes : Nat)
  | addressSpaceExhausted (requestedEnd : Nat)
  | invalidObjectAddress (word : Word32)
  | unknownObjectKind (code : UInt32)
  | headerValueOverflow (field : String) (value : Nat)
  | nonzeroPadding (address value : Nat)
  | invalidAllocationSize (bytes : Nat)
  | malformedHeader (address allocationBytes : Nat)
  | deadObject (address : Word32)
  deriving BEq, Repr

abbrev LinearMemory := Array UInt8

def wasmPageBytes : Nat := 65536

def heapBase : Nat := 1024

namespace LinearMemory

def withPages (pages : Nat) : LinearMemory :=
  Array.replicate (pages * wasmPageBytes) 0

def readByte (memory : LinearMemory) (address : Nat) : Except MemoryError UInt8 :=
  match memory[address]? with
  | some byte => .ok byte
  | none => .error (.outOfBounds address 1 memory.size)

def writeByte (memory : LinearMemory) (address : Nat) (value : UInt8) :
    Except MemoryError LinearMemory :=
  if h : address < memory.size then
    .ok (memory.set address value h)
  else
    .error (.outOfBounds address 1 memory.size)

private def byte16 (value : UInt16) (shift : Nat) : UInt8 :=
  (value >>> UInt16.ofNat shift).toUInt8

def readUInt16 (memory : LinearMemory) (address : Nat) : Except MemoryError UInt16 := do
  let b0 ← memory.readByte address
  let b1 ← memory.readByte (address + 1)
  return b0.toUInt16 + b1.toUInt16 * 256

def writeUInt16 (memory : LinearMemory) (address : Nat) (value : UInt16) :
    Except MemoryError LinearMemory := do
  let memory ← memory.writeByte address (byte16 value 0)
  memory.writeByte (address + 1) (byte16 value 8)

private def byte32 (value : UInt32) (shift : Nat) : UInt8 :=
  (value >>> UInt32.ofNat shift).toUInt8

def readUInt32 (memory : LinearMemory) (address : Nat) : Except MemoryError UInt32 := do
  let b0 ← memory.readByte address
  let b1 ← memory.readByte (address + 1)
  let b2 ← memory.readByte (address + 2)
  let b3 ← memory.readByte (address + 3)
  return b0.toUInt32 + b1.toUInt32 * 256 + b2.toUInt32 * 65536 +
    b3.toUInt32 * 16777216

def writeUInt32 (memory : LinearMemory) (address : Nat) (value : UInt32) :
    Except MemoryError LinearMemory := do
  let memory ← memory.writeByte address (byte32 value 0)
  let memory ← memory.writeByte (address + 1) (byte32 value 8)
  let memory ← memory.writeByte (address + 2) (byte32 value 16)
  memory.writeByte (address + 3) (byte32 value 24)

/-- Write adjacent 32-bit lanes. Common headers and later fixed-width metadata
regions use this structural form so their runtime layout and proof composition
share the same operation boundary. -/
def writeUInt32s (memory : LinearMemory) (address : Nat) :
    List UInt32 → Except MemoryError LinearMemory
  | [] => .ok memory
  | value :: rest => do
      let memory ← memory.writeUInt32 address value
      writeUInt32s memory (address + 4) rest

def readUInt64 (memory : LinearMemory) (address : Nat) : Except MemoryError UInt64 := do
  let low ← memory.readUInt32 address
  let high ← memory.readUInt32 (address + 4)
  return low.toUInt64 + high.toUInt64 * 4294967296

def writeUInt64 (memory : LinearMemory) (address : Nat) (value : UInt64) :
    Except MemoryError LinearMemory := do
  let memory ← memory.writeUInt32 address value.toUInt32
  memory.writeUInt32 (address + 4) (value >>> (32 : UInt64)).toUInt32

def writeWord32 (memory : LinearMemory) (address : Nat) (value : Word32) :
    Except MemoryError LinearMemory :=
  memory.writeUInt32 address (UInt32.ofNat value.value)

def readWord32 (memory : LinearMemory) (address : Nat) : Except MemoryError Word32 := do
  let value ← memory.readUInt32 address
  let some word := Word32.ofNat? value.toNat |
    throw (.addressSpaceExhausted value.toNat)
  return word

def growToFit (memory : LinearMemory) (requiredBytes : Nat) : LinearMemory :=
  if requiredBytes ≤ memory.size then
    memory
  else
    let missing := requiredBytes - memory.size
    let pages := (missing + wasmPageBytes - 1) / wasmPageBytes
    memory ++ Array.replicate (pages * wasmPageBytes) 0

@[simp] theorem readByte_set_same (memory : LinearMemory) (address : Nat)
    (value : UInt8) (inBounds : address < memory.size) :
    readByte (memory.set address value inBounds) address = .ok value := by
  simp [readByte]

theorem readByte_set_other (memory : LinearMemory) (address other : Nat)
    (value : UInt8) (inBounds : address < memory.size) (different : address ≠ other) :
    readByte (memory.set address value inBounds) other = readByte memory other := by
  by_cases otherInBounds : other < memory.size <;>
    simp [readByte, otherInBounds, different]

private theorem assembleByte16 (value : UInt16) :
    (byte16 value 0).toUInt16 + (byte16 value 8).toUInt16 * 256 = value := by
  simp [byte16]
  bv_decide

/-- A successful 16-bit write installs both little-endian bytes, preserves
memory size, and frames every other byte. -/
theorem writeUInt16_spec (memory : LinearMemory) (address : Nat) (value : UInt16)
    (inBounds : address + 1 < memory.size) :
    ∃ result,
      writeUInt16 memory address value = .ok result ∧
      result.size = memory.size ∧
      readByte result address = .ok (byte16 value 0) ∧
      readByte result (address + 1) = .ok (byte16 value 8) ∧
      ∀ other, address ≠ other → address + 1 ≠ other →
        readByte result other = readByte memory other := by
  have h0 : address < memory.size := by omega
  let m0 := memory.set address (byte16 value 0) h0
  have h1 : address + 1 < m0.size := by simp [m0]; omega
  let result := m0.set (address + 1) (byte16 value 8) h1
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
  · unfold writeUInt16
    rw [show writeByte memory address (byte16 value 0) = .ok m0 by
      simp [writeByte, h0, m0]]
    exact show writeByte m0 (address + 1) (byte16 value 8) = .ok result by
      simp [writeByte, h1, result]
  · simp [result, m0]
  · simp [result, m0, readByte]
  · simp [result, m0, readByte]
  · intro other ne0 ne1
    rw [readByte_set_other m0 (address + 1) other _ h1 ne1]
    exact readByte_set_other memory address other _ h0 ne0

theorem readByte_of_writeUInt16_eq_ok_other (memory result : LinearMemory)
    (address : Nat) (value : UInt16) (inBounds : address + 1 < memory.size)
    (written : writeUInt16 memory address value = .ok result) (other : Nat)
    (ne0 : address ≠ other) (ne1 : address + 1 ≠ other) :
    readByte result other = readByte memory other := by
  obtain ⟨actual, actualWrite, _, _, _, frame⟩ :=
    writeUInt16_spec memory address value inBounds
  rw [actualWrite] at written
  cases written
  exact frame other ne0 ne1

theorem readUInt16_of_writeUInt16_eq_ok (memory result : LinearMemory)
    (address : Nat) (value : UInt16) (inBounds : address + 1 < memory.size)
    (written : writeUInt16 memory address value = .ok result) :
    readUInt16 result address = .ok value := by
  obtain ⟨actual, actualWrite, _, b0, b1, _⟩ :=
    writeUInt16_spec memory address value inBounds
  rw [actualWrite] at written
  cases written
  unfold readUInt16
  rw [b0, b1]
  exact congrArg Except.ok (assembleByte16 value)

private theorem assembleByte32 (value : UInt32) :
    (byte32 value 0).toUInt32 + (byte32 value 8).toUInt32 * 256 +
      (byte32 value 16).toUInt32 * 65536 +
      (byte32 value 24).toUInt32 * 16777216 = value := by
  simp [byte32]
  bv_decide

/-- A successful checked 32-bit write preserves memory size, installs the
four little-endian bytes, and leaves every other byte observationally
unchanged. This is the byte-level frame rule used by header and field proofs. -/
theorem writeUInt32_spec (memory : LinearMemory) (address : Nat) (value : UInt32)
    (inBounds : address + 3 < memory.size) :
    ∃ result,
      writeUInt32 memory address value = .ok result ∧
      result.size = memory.size ∧
      readByte result address = .ok (byte32 value 0) ∧
      readByte result (address + 1) = .ok (byte32 value 8) ∧
      readByte result (address + 2) = .ok (byte32 value 16) ∧
      readByte result (address + 3) = .ok (byte32 value 24) ∧
      ∀ other,
        address ≠ other → address + 1 ≠ other → address + 2 ≠ other →
        address + 3 ≠ other → readByte result other = readByte memory other := by
  have h0 : address < memory.size := by omega
  let m0 := memory.set address (byte32 value 0) h0
  have hm0 : m0.size = memory.size := by simp [m0]
  have h1 : address + 1 < m0.size := by omega
  let m1 := m0.set (address + 1) (byte32 value 8) h1
  have hm1 : m1.size = memory.size := by simp [m1, hm0]
  have h2 : address + 2 < m1.size := by omega
  let m2 := m1.set (address + 2) (byte32 value 16) h2
  have hm2 : m2.size = memory.size := by simp [m2, hm1]
  have h3 : address + 3 < m2.size := by omega
  let m3 := m2.set (address + 3) (byte32 value 24) h3
  refine ⟨m3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold writeUInt32
    rw [show writeByte memory address (byte32 value 0) = .ok m0 by
      simp [writeByte, h0, m0]]
    change (do
      let memory ← writeByte m0 (address + 1) (byte32 value 8)
      let memory ← writeByte memory (address + 2) (byte32 value 16)
      writeByte memory (address + 3) (byte32 value 24)) = .ok m3
    rw [show writeByte m0 (address + 1) (byte32 value 8) = .ok m1 by
      simp [writeByte, h1, m1]]
    change (do
      let memory ← writeByte m1 (address + 2) (byte32 value 16)
      writeByte memory (address + 3) (byte32 value 24)) = .ok m3
    rw [show writeByte m1 (address + 2) (byte32 value 16) = .ok m2 by
      simp [writeByte, h2, m2]]
    exact show writeByte m2 (address + 3) (byte32 value 24) = .ok m3 by
      simp [writeByte, h3, m3]
  · simp [m3, m2, m1, m0]
  · simp [m3, m2, m1, m0, readByte]
  · simp [m3, m2, m1, m0, readByte]
  · simp [m3, m2, m1, m0, readByte]
  · simp [m3, m2, m1, m0, readByte]
  · intro other ne0 ne1 ne2 ne3
    rw [readByte_set_other m2 (address + 3) other _ h3 ne3]
    rw [readByte_set_other m1 (address + 2) other _ h2 ne2]
    rw [readByte_set_other m0 (address + 1) other _ h1 ne1]
    exact readByte_set_other memory address other _ h0 ne0

theorem readByte_of_writeUInt32_eq_ok (memory result : LinearMemory)
    (address : Nat) (value : UInt32) (inBounds : address + 3 < memory.size)
    (written : writeUInt32 memory address value = .ok result) (other : Nat)
    (ne0 : address ≠ other) (ne1 : address + 1 ≠ other)
    (ne2 : address + 2 ≠ other) (ne3 : address + 3 ≠ other) :
    readByte result other = readByte memory other := by
  obtain ⟨actual, actualWrite, _, _, _, _, _, frame⟩ :=
    writeUInt32_spec memory address value inBounds
  rw [actualWrite] at written
  cases written
  exact frame other ne0 ne1 ne2 ne3

/-- A 32-bit write frames a disjoint 32-bit read. -/
theorem readUInt32_of_writeUInt32_eq_ok_other (memory result : LinearMemory)
    (address other : Nat) (value : UInt32)
    (inBounds : address + 3 < memory.size)
    (written : writeUInt32 memory address value = .ok result)
    (disjoint : address + 3 < other ∨ other + 3 < address) :
    readUInt32 result other = readUInt32 memory other := by
  have byteFrame (byteAddress : Nat)
      (ne0 : address ≠ byteAddress) (ne1 : address + 1 ≠ byteAddress)
      (ne2 : address + 2 ≠ byteAddress) (ne3 : address + 3 ≠ byteAddress) :
      readByte result byteAddress = readByte memory byteAddress :=
    readByte_of_writeUInt32_eq_ok memory result address value inBounds written
      byteAddress ne0 ne1 ne2 ne3
  unfold readUInt32
  rw [byteFrame other (by omega) (by omega) (by omega) (by omega)]
  rw [byteFrame (other + 1) (by omega) (by omega) (by omega) (by omega)]
  rw [byteFrame (other + 2) (by omega) (by omega) (by omega) (by omega)]
  rw [byteFrame (other + 3) (by omega) (by omega) (by omega) (by omega)]

/-- Reading the address just written by a successful checked 32-bit write
returns exactly the written value. -/
theorem readUInt32_of_writeUInt32_eq_ok (memory result : LinearMemory)
    (address : Nat) (value : UInt32) (inBounds : address + 3 < memory.size)
    (written : writeUInt32 memory address value = .ok result) :
    readUInt32 result address = .ok value := by
  obtain ⟨actual, actualWrite, _, b0, b1, b2, b3, _⟩ :=
    writeUInt32_spec memory address value inBounds
  rw [actualWrite] at written
  cases written
  unfold readUInt32
  rw [b0]
  change (do
    let b1 ← readByte result (address + 1)
    let b2 ← readByte result (address + 2)
    let b3 ← readByte result (address + 3)
    return (byte32 value 0).toUInt32 + b1.toUInt32 * 256 +
      b2.toUInt32 * 65536 + b3.toUInt32 * 16777216) = .ok value
  rw [b1]
  change (do
    let b2 ← readByte result (address + 2)
    let b3 ← readByte result (address + 3)
    return (byte32 value 0).toUInt32 + (byte32 value 8).toUInt32 * 256 +
      b2.toUInt32 * 65536 + b3.toUInt32 * 16777216) = .ok value
  rw [b2]
  change (do
    let b3 ← readByte result (address + 3)
    return (byte32 value 0).toUInt32 + (byte32 value 8).toUInt32 * 256 +
      (byte32 value 16).toUInt32 * 65536 + b3.toUInt32 * 16777216) = .ok value
  rw [b3]
  exact congrArg Except.ok (assembleByte32 value)

private theorem assembleUInt64 (value : UInt64) :
    value.toUInt32.toUInt64 +
      (value >>> (32 : UInt64)).toUInt32.toUInt64 * 4294967296 = value := by
  bv_decide

/-- A successful 64-bit write is exactly two successful adjacent 32-bit
writes. Exposing this middle state lets all 64-bit proofs reuse the checked
32-bit write and frame rules. -/
theorem writeUInt64_decompose (memory result : LinearMemory) (address : Nat)
    (value : UInt64) (inBounds : address + 7 < memory.size)
    (written : writeUInt64 memory address value = .ok result) :
    ∃ middle,
      writeUInt32 memory address value.toUInt32 = .ok middle ∧
      middle.size = memory.size ∧
      writeUInt32 middle (address + 4) (value >>> (32 : UInt64)).toUInt32 =
        .ok result := by
  obtain ⟨middle, lowWrite, middleSize, _, _, _, _, _⟩ :=
    writeUInt32_spec memory address value.toUInt32 (by omega)
  obtain ⟨actual, highWrite, _, _, _, _, _, _⟩ :=
    writeUInt32_spec middle (address + 4)
      (value >>> (32 : UInt64)).toUInt32 (by omega)
  have wholeWrite : writeUInt64 memory address value = .ok actual := by
    unfold writeUInt64
    rw [lowWrite]
    change writeUInt32 middle (address + 4)
      (value >>> (32 : UInt64)).toUInt32 = .ok actual
    exact highWrite
  rw [wholeWrite] at written
  cases written
  exact ⟨middle, lowWrite, middleSize, highWrite⟩

/-- Reading the address just written by a successful checked 64-bit write
returns exactly the written value. -/
theorem readUInt64_of_writeUInt64_eq_ok (memory result : LinearMemory)
    (address : Nat) (value : UInt64) (inBounds : address + 7 < memory.size)
    (written : writeUInt64 memory address value = .ok result) :
    readUInt64 result address = .ok value := by
  obtain ⟨middle, lowWrite, middleSize, highWrite⟩ :=
    writeUInt64_decompose memory result address value inBounds written
  have highInBounds : address + 4 + 3 < middle.size := by omega
  have lowReadMiddle : readUInt32 middle address = .ok value.toUInt32 :=
    readUInt32_of_writeUInt32_eq_ok memory middle address value.toUInt32
      (by omega) lowWrite
  have lowReadResult : readUInt32 result address = .ok value.toUInt32 := by
    calc
      readUInt32 result address = readUInt32 middle address :=
        readUInt32_of_writeUInt32_eq_ok_other middle result (address + 4) address
          (value >>> (32 : UInt64)).toUInt32 highInBounds highWrite (by omega)
      _ = .ok value.toUInt32 := lowReadMiddle
  have highReadResult :
      readUInt32 result (address + 4) =
        .ok (value >>> (32 : UInt64)).toUInt32 :=
    readUInt32_of_writeUInt32_eq_ok middle result (address + 4)
      (value >>> (32 : UInt64)).toUInt32 highInBounds highWrite
  unfold readUInt64
  rw [lowReadResult]
  change (do
    let high ← readUInt32 result (address + 4)
    return value.toUInt32.toUInt64 + high.toUInt64 * 4294967296) = .ok value
  rw [highReadResult]
  exact congrArg Except.ok (assembleUInt64 value)

/-- A 64-bit write frames a disjoint 32-bit read. -/
theorem readUInt32_of_writeUInt64_eq_ok_other (memory result : LinearMemory)
    (address other : Nat) (value : UInt64)
    (inBounds : address + 7 < memory.size)
    (written : writeUInt64 memory address value = .ok result)
    (disjoint : address + 7 < other ∨ other + 3 < address) :
    readUInt32 result other = readUInt32 memory other := by
  obtain ⟨middle, lowWrite, middleSize, highWrite⟩ :=
    writeUInt64_decompose memory result address value inBounds written
  calc
    readUInt32 result other = readUInt32 middle other :=
      readUInt32_of_writeUInt32_eq_ok_other middle result (address + 4) other
        (value >>> (32 : UInt64)).toUInt32 (by omega) highWrite (by omega)
    _ = readUInt32 memory other :=
      readUInt32_of_writeUInt32_eq_ok_other memory middle address other
        value.toUInt32 (by omega) lowWrite (by omega)

private theorem Word32.ofNat_uint32_value (word : Word32) :
    Word32.ofNat? (UInt32.ofNat word.value).toNat = some word := by
  cases word with
  | mk value isLt =>
      simp [Word32.ofNat?, wordModulus] at isLt ⊢
      omega

/-- Word lanes inherit the exact 32-bit checked write/read round trip. -/
theorem readWord32_of_writeWord32_eq_ok (memory result : LinearMemory)
    (address : Nat) (value : Word32) (inBounds : address + 3 < memory.size)
    (written : writeWord32 memory address value = .ok result) :
    readWord32 result address = .ok value := by
  have readBack : readUInt32 result address = .ok (UInt32.ofNat value.value) :=
    readUInt32_of_writeUInt32_eq_ok memory result address
      (UInt32.ofNat value.value) inBounds written
  unfold readWord32
  rw [readBack]
  change ((do
    let some word := Word32.ofNat? (UInt32.ofNat value.value).toNat |
      throw (.addressSpaceExhausted (UInt32.ofNat value.value).toNat)
    return word) : Except MemoryError Word32) = Except.ok value
  rw [Word32.ofNat_uint32_value]
  rfl

end LinearMemory

def ObjectKind.ofCode? (code : UInt32) : Option ObjectKind :=
  if code == ObjectKind.constructor.code then some .constructor
  else if code == ObjectKind.closure.code then some .closure
  else if code == ObjectKind.boxed.code then some .boxed
  else if code == ObjectKind.string.code then some .string
  else if code == ObjectKind.natural.code then some .natural
  else if code == ObjectKind.integer.code then some .integer
  else if code == ObjectKind.byteArray.code then some .byteArray
  else if code == ObjectKind.opaque.code then some .opaque
  else if code == ObjectKind.freed.code then some .freed
  else none

def Header.flags (header : Header) : UInt32 :=
  UInt32.ofNat ((if header.persistent then 1 else 0) + (if header.live then 2 else 0))

def Header.words (header : Header) : List UInt32 :=
  [header.kind.code, header.flags, header.refCount, header.allocationBytes,
    header.aux0, header.aux1, header.aux2, header.aux3]

def Header.write (memory : LinearMemory) (address : Word32) (header : Header) :
    Except MemoryError LinearMemory :=
  memory.writeUInt32s address.value header.words

def Header.read (memory : LinearMemory) (address : Word32) : Except MemoryError Header := do
  let base := address.value
  let kindCode ← memory.readUInt32 (base + headerKindOffset)
  let some kind := ObjectKind.ofCode? kindCode | throw (.unknownObjectKind kindCode)
  let flags ← memory.readUInt32 (base + headerFlagsOffset)
  let refCount ← memory.readUInt32 (base + headerRefCountOffset)
  let allocationBytes ← memory.readUInt32 (base + headerAllocationBytesOffset)
  let aux0 ← memory.readUInt32 (base + headerAux0Offset)
  let aux1 ← memory.readUInt32 (base + headerAux1Offset)
  let aux2 ← memory.readUInt32 (base + headerAux2Offset)
  let aux3 ← memory.readUInt32 (base + headerAux3Offset)
  return {
    kind
    persistent := flags.toNat % 2 = 1
    live := (flags.toNat / 2) % 2 = 1
    refCount
    allocationBytes
    aux0
    aux1
    aux2
    aux3 }

/-- Concrete state owned by the linear-memory runtime. World, trace, globals,
and structured faults are added in their W6 slices; allocation itself depends
only on bytes and the monotone heap cursor. -/
structure MemoryState where
  memory : LinearMemory := LinearMemory.withPages 1
  heapCursor : Nat := heapBase
  deriving Inhabited

def MemoryState.initial : MemoryState := {}

def MemoryState.allocate (state : MemoryState) (requestedBytes : Nat) :
    Except MemoryError (MemoryState × Word32) := do
  if requestedBytes < headerBytes then
    throw (.invalidAllocationSize requestedBytes)
  let bytes := align8 requestedBytes
  let addressValue := align8 state.heapCursor
  let requestedEnd := addressValue + bytes
  if wordModulus < requestedEnd then
    throw (.addressSpaceExhausted requestedEnd)
  let some address := Word32.ofNat? addressValue |
    throw (.addressSpaceExhausted addressValue)
  unless address.classify = .heap do
    throw (.invalidObjectAddress address)
  let memory := state.memory.growToFit requestedEnd
  return ({ memory, heapCursor := requestedEnd }, address)

def Header.forAllocation (kind : ObjectKind) (allocationBytes : Nat)
    (persistent := false) (aux0 : UInt32 := 0) (aux1 : UInt32 := 0)
    (aux2 : UInt32 := 0) (aux3 : UInt32 := 0) : Header := {
  kind
  persistent
  live := true
  refCount := if persistent then 0 else 1
  allocationBytes := UInt32.ofNat allocationBytes
  aux0
  aux1
  aux2
  aux3 }

def MemoryState.allocateObject (state : MemoryState) (kind : ObjectKind)
    (payloadBytes : Nat) (persistent := false) (aux0 : UInt32 := 0)
    (aux1 : UInt32 := 0) (aux2 : UInt32 := 0) (aux3 : UInt32 := 0) :
    Except MemoryError (MemoryState × Word32) := do
  let allocationBytes := align8 (headerBytes + payloadBytes)
  let (state, address) ← state.allocate allocationBytes
  let header := Header.forAllocation kind allocationBytes persistent aux0 aux1 aux2 aux3
  let memory ← header.write state.memory address
  return ({ state with memory }, address)

def MemoryState.readLiveHeader (state : MemoryState) (address : Word32) :
    Except MemoryError Header := do
  unless address.classify = .heap do
    throw (.invalidObjectAddress address)
  let header ← Header.read state.memory address
  unless header.live do
    throw (.deadObject address)
  let bytes := header.allocationBytes.toNat
  unless headerBytes ≤ bytes && bytes % target.heapAlignment = 0 &&
      address.value + bytes ≤ state.memory.size do
    throw (.malformedHeader address.value bytes)
  return header

end Fir.Wasm.Concrete
