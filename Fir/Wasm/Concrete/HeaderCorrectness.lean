import Fir.Wasm.Concrete.Memory

namespace Fir.Wasm.Concrete

namespace LinearMemory

/-- Postcondition for an adjacent sequence of checked 32-bit writes. -/
structure WriteUInt32sPost (before after : LinearMemory) (address : Nat)
    (writtenValues : List UInt32) : Prop where
  size : after.size = before.size
  wordAt : ∀ index value,
    writtenValues[index]? = some value →
    readUInt32 after (address + 4 * index) = .ok value
  frame : ∀ other,
    other + 4 ≤ address ∨ address + 4 * writtenValues.length ≤ other →
    readUInt32 after other = readUInt32 before other

theorem writeUInt32s_spec (memory : LinearMemory) (address : Nat)
    (values : List UInt32) (inBounds : address + 4 * values.length ≤ memory.size) :
    ∃ result,
      writeUInt32s memory address values = .ok result ∧
      WriteUInt32sPost memory result address values := by
  induction values generalizing memory address with
  | nil =>
      refine ⟨memory, rfl, ?_⟩
      refine ⟨rfl, ?_, ?_⟩
      · intro index value atIndex
        simp at atIndex
      · intro other _
        rfl
  | cons value rest ih =>
      simp only [List.length_cons] at inBounds
      have headInBounds : address + 3 < memory.size := by omega
      obtain ⟨middle, headWrite, middleSize, _, _, _, _, _⟩ :=
        writeUInt32_spec memory address value headInBounds
      have tailInBounds : address + 4 + 4 * rest.length ≤ middle.size := by
        omega
      obtain ⟨result, tailWrite, tailPost⟩ :=
        ih middle (address + 4) tailInBounds
      refine ⟨result, ?_, ?_⟩
      · unfold writeUInt32s
        rw [headWrite]
        change writeUInt32s middle (address + 4) rest = .ok result
        exact tailWrite
      · refine ⟨tailPost.size.trans middleSize, ?_, ?_⟩
        · intro index item atIndex
          cases index with
          | zero =>
              simp at atIndex
              subst item
              calc
                readUInt32 result address = readUInt32 middle address := by
                  simpa using tailPost.frame address (by omega)
                _ = .ok value :=
                  readUInt32_of_writeUInt32_eq_ok memory middle address value
                    headInBounds headWrite
          | succ index =>
              have tailAt : rest[index]? = some item := by
                simpa using atIndex
              have tailValue := tailPost.wordAt index item tailAt
              have addressEq :
                  address + 4 * (index + 1) = address + 4 + 4 * index := by
                omega
              rw [addressEq]
              exact tailValue
        · intro other separated
          simp only [List.length_cons] at separated
          have tailSeparated :
              other + 4 ≤ address + 4 ∨
                address + 4 + 4 * rest.length ≤ other := by
            omega
          have headSeparated : address + 3 < other ∨ other + 3 < address := by
            omega
          calc
            readUInt32 result other = readUInt32 middle other :=
              tailPost.frame other tailSeparated
            _ = readUInt32 memory other :=
              readUInt32_of_writeUInt32_eq_ok_other memory middle address other
                value headInBounds headWrite headSeparated

end LinearMemory

@[simp] theorem ObjectKind.ofCode_code (kind : ObjectKind) :
    ObjectKind.ofCode? kind.code = some kind := by
  cases kind <;> rfl

private theorem Header.rebuild_from_words (header : Header) :
    ({
      kind := header.kind
      persistent := header.flags.toNat % 2 = 1
      live := (header.flags.toNat / 2) % 2 = 1
      refCount := header.refCount
      allocationBytes := header.allocationBytes
      aux0 := header.aux0
      aux1 := header.aux1
      aux2 := header.aux2
      aux3 := header.aux3 } : Header) = header := by
  rcases header with
    ⟨kind, persistent, live, refCount, allocationBytes, aux0, aux1, aux2, aux3⟩
  cases persistent <;> cases live <;> simp [Header.flags]

/-- An in-bounds common-header write succeeds and establishes all eight word
postconditions plus a frame rule for disjoint 32-bit reads. -/
theorem Header.write_spec (memory : LinearMemory) (address : Word32)
    (header : Header) (inBounds : address.value + headerBytes ≤ memory.size) :
    ∃ result,
      header.write memory address = .ok result ∧
      LinearMemory.WriteUInt32sPost memory result address.value header.words := by
  have wordsInBounds :
      address.value + 4 * header.words.length ≤ memory.size := by
    simpa [Header.words, headerBytes] using inBounds
  obtain ⟨result, written, post⟩ :=
    LinearMemory.writeUInt32s_spec memory address.value header.words wordsInBounds
  exact ⟨result, written, post⟩

theorem Header.write_preserves_size (memory result : LinearMemory)
    (address : Word32) (header : Header)
    (inBounds : address.value + headerBytes ≤ memory.size)
    (written : header.write memory address = .ok result) :
    result.size = memory.size := by
  obtain ⟨actual, actualWrite, post⟩ := Header.write_spec memory address header inBounds
  rw [actualWrite] at written
  cases written
  exact post.size

/-- A common-header write frames every disjoint 32-bit read. -/
theorem Header.readUInt32_of_write_eq_ok_other (memory result : LinearMemory)
    (address : Word32) (header : Header) (other : Nat)
    (inBounds : address.value + headerBytes ≤ memory.size)
    (written : header.write memory address = .ok result)
    (disjoint : other + 4 ≤ address.value ∨
      address.value + headerBytes ≤ other) :
    result.readUInt32 other = memory.readUInt32 other := by
  obtain ⟨actual, actualWrite, post⟩ := Header.write_spec memory address header inBounds
  rw [actualWrite] at written
  cases written
  apply post.frame other
  simpa [Header.words, headerBytes] using disjoint

/-- Exact common-header write/read round trip. This is the first composition
layer above the verified word accesses and the basis for allocator
preservation. -/
theorem Header.read_of_write_eq_ok (memory result : LinearMemory)
    (address : Word32) (header : Header)
    (inBounds : address.value + headerBytes ≤ memory.size)
    (written : header.write memory address = .ok result) :
    Header.read result address = .ok header := by
  obtain ⟨actual, actualWrite, post⟩ := Header.write_spec memory address header inBounds
  rw [actualWrite] at written
  cases written
  have kindRead :
      result.readUInt32 (address.value + headerKindOffset) = .ok header.kind.code := by
    simpa [Header.words, headerKindOffset] using
      post.wordAt 0 header.kind.code (by simp [Header.words])
  have flagsRead :
      result.readUInt32 (address.value + headerFlagsOffset) = .ok header.flags := by
    simpa [Header.words, headerFlagsOffset] using
      post.wordAt 1 header.flags (by simp [Header.words])
  have refCountRead :
      result.readUInt32 (address.value + headerRefCountOffset) =
        .ok header.refCount := by
    simpa [Header.words, headerRefCountOffset] using
      post.wordAt 2 header.refCount (by simp [Header.words])
  have allocationBytesRead :
      result.readUInt32 (address.value + headerAllocationBytesOffset) =
        .ok header.allocationBytes := by
    simpa [Header.words, headerAllocationBytesOffset] using
      post.wordAt 3 header.allocationBytes (by simp [Header.words])
  have aux0Read :
      result.readUInt32 (address.value + headerAux0Offset) = .ok header.aux0 := by
    simpa [Header.words, headerAux0Offset] using
      post.wordAt 4 header.aux0 (by simp [Header.words])
  have aux1Read :
      result.readUInt32 (address.value + headerAux1Offset) = .ok header.aux1 := by
    simpa [Header.words, headerAux1Offset] using
      post.wordAt 5 header.aux1 (by simp [Header.words])
  have aux2Read :
      result.readUInt32 (address.value + headerAux2Offset) = .ok header.aux2 := by
    simpa [Header.words, headerAux2Offset] using
      post.wordAt 6 header.aux2 (by simp [Header.words])
  have aux3Read :
      result.readUInt32 (address.value + headerAux3Offset) = .ok header.aux3 := by
    simpa [Header.words, headerAux3Offset] using
      post.wordAt 7 header.aux3 (by simp [Header.words])
  unfold Header.read
  dsimp only
  rw [kindRead]
  change (do
    let some kind := ObjectKind.ofCode? header.kind.code |
      throw (MemoryError.unknownObjectKind header.kind.code)
    let flags ← result.readUInt32 (address.value + headerFlagsOffset)
    let refCount ← result.readUInt32 (address.value + headerRefCountOffset)
    let allocationBytes ←
      result.readUInt32 (address.value + headerAllocationBytesOffset)
    let aux0 ← result.readUInt32 (address.value + headerAux0Offset)
    let aux1 ← result.readUInt32 (address.value + headerAux1Offset)
    let aux2 ← result.readUInt32 (address.value + headerAux2Offset)
    let aux3 ← result.readUInt32 (address.value + headerAux3Offset)
    return {
      kind
      persistent := flags.toNat % 2 = 1
      live := (flags.toNat / 2) % 2 = 1
      refCount
      allocationBytes
      aux0
      aux1
      aux2
      aux3 }) = (Except.ok header : Except MemoryError Header)
  rw [ObjectKind.ofCode_code]
  change (do
    let flags ← result.readUInt32 (address.value + headerFlagsOffset)
    let refCount ← result.readUInt32 (address.value + headerRefCountOffset)
    let allocationBytes ←
      result.readUInt32 (address.value + headerAllocationBytesOffset)
    let aux0 ← result.readUInt32 (address.value + headerAux0Offset)
    let aux1 ← result.readUInt32 (address.value + headerAux1Offset)
    let aux2 ← result.readUInt32 (address.value + headerAux2Offset)
    let aux3 ← result.readUInt32 (address.value + headerAux3Offset)
    return {
      kind := header.kind
      persistent := flags.toNat % 2 = 1
      live := (flags.toNat / 2) % 2 = 1
      refCount
      allocationBytes
      aux0
      aux1
      aux2
      aux3 }) = (Except.ok header : Except MemoryError Header)
  rw [flagsRead]
  change (do
    let refCount ← result.readUInt32 (address.value + headerRefCountOffset)
    let allocationBytes ←
      result.readUInt32 (address.value + headerAllocationBytesOffset)
    let aux0 ← result.readUInt32 (address.value + headerAux0Offset)
    let aux1 ← result.readUInt32 (address.value + headerAux1Offset)
    let aux2 ← result.readUInt32 (address.value + headerAux2Offset)
    let aux3 ← result.readUInt32 (address.value + headerAux3Offset)
    return {
      kind := header.kind
      persistent := header.flags.toNat % 2 = 1
      live := (header.flags.toNat / 2) % 2 = 1
      refCount
      allocationBytes
      aux0
      aux1
      aux2
      aux3 }) = (Except.ok header : Except MemoryError Header)
  rw [refCountRead]
  change (do
    let allocationBytes ←
      result.readUInt32 (address.value + headerAllocationBytesOffset)
    let aux0 ← result.readUInt32 (address.value + headerAux0Offset)
    let aux1 ← result.readUInt32 (address.value + headerAux1Offset)
    let aux2 ← result.readUInt32 (address.value + headerAux2Offset)
    let aux3 ← result.readUInt32 (address.value + headerAux3Offset)
    return {
      kind := header.kind
      persistent := header.flags.toNat % 2 = 1
      live := (header.flags.toNat / 2) % 2 = 1
      refCount := header.refCount
      allocationBytes
      aux0
      aux1
      aux2
      aux3 }) = (Except.ok header : Except MemoryError Header)
  rw [allocationBytesRead]
  change (do
    let aux0 ← result.readUInt32 (address.value + headerAux0Offset)
    let aux1 ← result.readUInt32 (address.value + headerAux1Offset)
    let aux2 ← result.readUInt32 (address.value + headerAux2Offset)
    let aux3 ← result.readUInt32 (address.value + headerAux3Offset)
    return {
      kind := header.kind
      persistent := header.flags.toNat % 2 = 1
      live := (header.flags.toNat / 2) % 2 = 1
      refCount := header.refCount
      allocationBytes := header.allocationBytes
      aux0
      aux1
      aux2
      aux3 }) = (Except.ok header : Except MemoryError Header)
  rw [aux0Read]
  change (do
    let aux1 ← result.readUInt32 (address.value + headerAux1Offset)
    let aux2 ← result.readUInt32 (address.value + headerAux2Offset)
    let aux3 ← result.readUInt32 (address.value + headerAux3Offset)
    return {
      kind := header.kind
      persistent := header.flags.toNat % 2 = 1
      live := (header.flags.toNat / 2) % 2 = 1
      refCount := header.refCount
      allocationBytes := header.allocationBytes
      aux0 := header.aux0
      aux1
      aux2
      aux3 }) = (Except.ok header : Except MemoryError Header)
  rw [aux1Read]
  change (do
    let aux2 ← result.readUInt32 (address.value + headerAux2Offset)
    let aux3 ← result.readUInt32 (address.value + headerAux3Offset)
    return {
      kind := header.kind
      persistent := header.flags.toNat % 2 = 1
      live := (header.flags.toNat / 2) % 2 = 1
      refCount := header.refCount
      allocationBytes := header.allocationBytes
      aux0 := header.aux0
      aux1 := header.aux1
      aux2
      aux3 }) = (Except.ok header : Except MemoryError Header)
  rw [aux2Read]
  change (do
    let aux3 ← result.readUInt32 (address.value + headerAux3Offset)
    return {
      kind := header.kind
      persistent := header.flags.toNat % 2 = 1
      live := (header.flags.toNat / 2) % 2 = 1
      refCount := header.refCount
      allocationBytes := header.allocationBytes
      aux0 := header.aux0
      aux1 := header.aux1
      aux2 := header.aux2
      aux3 }) = (Except.ok header : Except MemoryError Header)
  rw [aux3Read]
  exact congrArg Except.ok (Header.rebuild_from_words header)

end Fir.Wasm.Concrete
