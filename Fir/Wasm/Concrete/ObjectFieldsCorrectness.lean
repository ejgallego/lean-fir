import Fir.Wasm.Concrete.Runtime
import Fir.Wasm.Concrete.FrontierCorrectness

namespace Fir.Wasm.Concrete

/-- Exact postcondition for the constructor object-field writer.  Besides the
two lane reads for every slot, it exposes word- and byte-level frame rules for
the header, later payload regions, and older allocations. -/
structure WriteObjectFieldsPost (before after : LinearMemory)
    (base index : Nat) (fields : List Word32) : Prop where
  size : after.size = before.size
  fieldAt : ∀ offset field,
    fields[offset]? = some field →
    after.readWord32 (objectFieldAddress base (index + offset)) = .ok field
  paddingAt : ∀ offset field,
    fields[offset]? = some field →
    after.readUInt32 (objectFieldAddress base (index + offset) + 4) = .ok 0
  wordFrame : ∀ other,
    other + 4 ≤ objectFieldAddress base index ∨
      objectFieldAddress base (index + fields.length) ≤ other →
    after.readUInt32 other = before.readUInt32 other
  byteFrame : ∀ other,
    other < objectFieldAddress base index ∨
      objectFieldAddress base (index + fields.length) ≤ other →
    after.readByte other = before.readByte other

theorem writeObjectFields_spec (memory : LinearMemory) (base index : Nat)
    (fields : List Word32)
    (inBounds : objectFieldAddress base (index + fields.length) ≤ memory.size) :
    ∃ result,
      writeObjectFields memory base index fields = .ok result ∧
      WriteObjectFieldsPost memory result base index fields := by
  induction fields generalizing memory index with
  | nil =>
      refine ⟨memory, rfl, ?_⟩
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · intro offset field atOffset
        simp at atOffset
      · intro offset field atOffset
        simp at atOffset
      · intro other _
        rfl
      · intro other _
        rfl
  | cons field rest ih =>
      let slot := objectFieldAddress base index
      have lowInBounds : slot + 3 < memory.size := by
        simp only [List.length_cons] at inBounds
        simp [slot, objectFieldAddress, target] at inBounds ⊢
        omega
      obtain ⟨lowMemory, lowWrite, lowSize, _, _, _, _, lowByteFrame⟩ :=
        LinearMemory.writeUInt32_spec memory slot (UInt32.ofNat field.value)
          lowInBounds
      have paddingInBounds : slot + 4 + 3 < lowMemory.size := by
        simp only [List.length_cons] at inBounds
        simp [slot, objectFieldAddress, target] at inBounds ⊢
        omega
      obtain ⟨slotMemory, paddingWrite, slotSize, _, _, _, _, paddingByteFrame⟩ :=
        LinearMemory.writeUInt32_spec lowMemory (slot + 4) 0 paddingInBounds
      have tailInBounds :
          objectFieldAddress base (index + 1 + rest.length) ≤ slotMemory.size := by
        simp only [List.length_cons] at inBounds
        simp [objectFieldAddress, target] at inBounds ⊢
        omega
      obtain ⟨result, tailWrite, tailPost⟩ :=
        ih slotMemory (index + 1) tailInBounds
      refine ⟨result, ?_, ?_⟩
      · unfold writeObjectFields
        change (do
          let memory ← memory.writeUInt32 slot (UInt32.ofNat field.value)
          let memory ← memory.writeUInt32 (slot + 4) 0
          writeObjectFields memory base (index + 1) rest) = .ok result
        rw [lowWrite]
        change (do
          let memory ← lowMemory.writeUInt32 (slot + 4) 0
          writeObjectFields memory base (index + 1) rest) = .ok result
        rw [paddingWrite]
        exact tailWrite
      · refine ⟨tailPost.size.trans (slotSize.trans lowSize), ?_, ?_, ?_, ?_⟩
        · intro offset item atOffset
          cases offset with
          | zero =>
              simp at atOffset
              subst item
              have lowRead : lowMemory.readWord32 slot = .ok field :=
                LinearMemory.readWord32_of_writeWord32_eq_ok memory lowMemory slot field
                  lowInBounds lowWrite
              have paddedRead : slotMemory.readWord32 slot = .ok field := by
                unfold LinearMemory.readWord32
                rw [LinearMemory.readUInt32_of_writeUInt32_eq_ok_other lowMemory
                  slotMemory (slot + 4) slot 0 paddingInBounds paddingWrite (by omega)]
                exact lowRead
              calc
                result.readWord32 (objectFieldAddress base (index + 0)) =
                    slotMemory.readWord32 slot := by
                      change result.readWord32 slot = slotMemory.readWord32 slot
                      unfold LinearMemory.readWord32
                      rw [tailPost.wordFrame slot (by
                        simp [slot, objectFieldAddress, target]
                        omega)]
                _ = .ok field := paddedRead
          | succ offset =>
              have restAt : rest[offset]? = some item := by simpa using atOffset
              have tailAt := tailPost.fieldAt offset item restAt
              simpa [objectFieldAddress, target, Nat.add_assoc, Nat.succ_eq_add_one,
                Nat.add_comm, Nat.add_left_comm] using tailAt
        · intro offset item atOffset
          cases offset with
          | zero =>
              simp at atOffset
              subst item
              have paddingRead : slotMemory.readUInt32 (slot + 4) = .ok 0 :=
                LinearMemory.readUInt32_of_writeUInt32_eq_ok lowMemory slotMemory
                  (slot + 4) 0 paddingInBounds paddingWrite
              calc
                result.readUInt32 (objectFieldAddress base (index + 0) + 4) =
                    slotMemory.readUInt32 (slot + 4) := by
                      change result.readUInt32 (slot + 4) =
                        slotMemory.readUInt32 (slot + 4)
                      rw [tailPost.wordFrame (slot + 4) (by
                        simp [slot, objectFieldAddress, target]
                        omega)]
                _ = .ok 0 := paddingRead
          | succ offset =>
              have restAt : rest[offset]? = some item := by simpa using atOffset
              have tailAt := tailPost.paddingAt offset item restAt
              simpa [objectFieldAddress, target, Nat.add_assoc, Nat.succ_eq_add_one,
                Nat.add_comm, Nat.add_left_comm] using tailAt
        · intro other separated
          simp only [List.length_cons] at separated
          have tailSeparated :
              other + 4 ≤ objectFieldAddress base (index + 1) ∨
                objectFieldAddress base (index + 1 + rest.length) ≤ other := by
            simp [objectFieldAddress, target] at separated ⊢
            omega
          have paddingSeparated : slot + 4 + 3 < other ∨ other + 3 < slot + 4 := by
            simp [slot, objectFieldAddress, target] at separated ⊢
            omega
          have lowSeparated : slot + 3 < other ∨ other + 3 < slot := by
            simp [slot, objectFieldAddress, target] at separated ⊢
            omega
          calc
            result.readUInt32 other = slotMemory.readUInt32 other :=
              tailPost.wordFrame other tailSeparated
            _ = lowMemory.readUInt32 other :=
              LinearMemory.readUInt32_of_writeUInt32_eq_ok_other lowMemory slotMemory
                (slot + 4) other 0 paddingInBounds paddingWrite paddingSeparated
            _ = memory.readUInt32 other :=
              LinearMemory.readUInt32_of_writeUInt32_eq_ok_other memory lowMemory
                slot other (UInt32.ofNat field.value) lowInBounds lowWrite lowSeparated
        · intro other separated
          simp only [List.length_cons] at separated
          have tailSeparated :
              other < objectFieldAddress base (index + 1) ∨
                objectFieldAddress base (index + 1 + rest.length) ≤ other := by
            simp [objectFieldAddress, target] at separated ⊢
            omega
          calc
            result.readByte other = slotMemory.readByte other :=
              tailPost.byteFrame other tailSeparated
            _ = lowMemory.readByte other :=
              paddingByteFrame other
                (by simp [slot, objectFieldAddress, target] at separated ⊢; omega)
                (by simp [slot, objectFieldAddress, target] at separated ⊢; omega)
                (by simp [slot, objectFieldAddress, target] at separated ⊢; omega)
                (by simp [slot, objectFieldAddress, target] at separated ⊢; omega)
            _ = memory.readByte other :=
              lowByteFrame other
                (by simp [slot, objectFieldAddress, target] at separated ⊢; omega)
                (by simp [slot, objectFieldAddress, target] at separated ⊢; omega)
                (by simp [slot, objectFieldAddress, target] at separated ⊢; omega)
                (by simp [slot, objectFieldAddress, target] at separated ⊢; omega)

theorem writeObjectFields_post (memory result : LinearMemory) (base index : Nat)
    (fields : List Word32)
    (inBounds : objectFieldAddress base (index + fields.length) ≤ memory.size)
    (written : writeObjectFields memory base index fields = .ok result) :
    WriteObjectFieldsPost memory result base index fields := by
  obtain ⟨actual, actualWrite, post⟩ :=
    writeObjectFields_spec memory base index fields inBounds
  rw [actualWrite] at written
  cases written
  exact post

/-- Payload writes occur strictly after the common header and therefore leave
its decoder unchanged. -/
theorem Header.read_of_writeObjectFields (memory result : LinearMemory)
    (address : Word32) (index : Nat) (fields : List Word32)
    (post : WriteObjectFieldsPost memory result address.value index fields) :
    Header.read result address = Header.read memory address := by
  have frame (offset : Nat) (withinHeader : offset + 4 ≤ headerBytes) :
      result.readUInt32 (address.value + offset) =
        memory.readUInt32 (address.value + offset) := by
    apply post.wordFrame
    left
    simp [objectFieldAddress, target]
    omega
  unfold Header.read
  dsimp only
  rw [frame headerKindOffset (by decide)]
  rw [frame headerFlagsOffset (by decide)]
  rw [frame headerRefCountOffset (by decide)]
  rw [frame headerAllocationBytesOffset (by decide)]
  rw [frame headerAux0Offset (by decide)]
  rw [frame headerAux1Offset (by decide)]
  rw [frame headerAux2Offset (by decide)]
  rw [frame headerAux3Offset (by decide)]

theorem MemoryState.readLiveHeader_of_writeObjectFields
    (state : MemoryState) (result : LinearMemory) (address : Word32)
    (index : Nat) (fields : List Word32)
    (post : WriteObjectFieldsPost state.memory result address.value index fields) :
    ({ state with memory := result } : MemoryState).readLiveHeader address =
      state.readLiveHeader address := by
  have headerFrame :=
    Header.read_of_writeObjectFields state.memory result address index fields post
  unfold MemoryState.readLiveHeader
  dsimp only
  rw [headerFrame, post.size]

/-- A successfully decoded live constructor header is accepted by the public
constructor-header checker. -/
theorem readConstructorHeader_eq_ok_of_readLiveHeader
    (state : MemoryState) (address : Word32) (header : Header)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor) :
    readConstructorHeader state address = .ok header := by
  have heap : address.classify = .heap := by
    have checked := headerRead
    unfold MemoryState.readLiveHeader at checked
    split at checked
    next heap => exact heap
    next => contradiction
  unfold readConstructorHeader
  simp [heap, headerRead]
  simp only [Bind.bind, Except.bind]
  simp [liftMemory, headerKind]
  rfl

/-- Every byte beginning at the end of a bulk object-field write is framed. -/
theorem WriteObjectFieldsPost.readByte_suffix
    {before after : LinearMemory} {base index : Nat} {fields : List Word32}
    (post : WriteObjectFieldsPost before after base index fields)
    (address : Nat)
    (suffix : objectFieldAddress base (index + fields.length) ≤ address) :
    after.readByte address = before.readByte address :=
  post.byteFrame address (.inr suffix)

/-- A 16-bit read beginning after a bulk object-field write is unchanged. -/
theorem WriteObjectFieldsPost.readUInt16_suffix
    {before after : LinearMemory} {base index : Nat} {fields : List Word32}
    (post : WriteObjectFieldsPost before after base index fields)
    (address : Nat)
    (suffix : objectFieldAddress base (index + fields.length) ≤ address) :
    after.readUInt16 address = before.readUInt16 address := by
  unfold LinearMemory.readUInt16
  rw [post.readByte_suffix address suffix]
  rw [post.readByte_suffix (address + 1) (by omega)]

/-- A 32-bit read beginning after a bulk object-field write is unchanged. -/
theorem WriteObjectFieldsPost.readUInt32_suffix
    {before after : LinearMemory} {base index : Nat} {fields : List Word32}
    (post : WriteObjectFieldsPost before after base index fields)
    (address : Nat)
    (suffix : objectFieldAddress base (index + fields.length) ≤ address) :
    after.readUInt32 address = before.readUInt32 address :=
  post.wordFrame address (.inr suffix)

/-- A 64-bit read beginning after a bulk object-field write is unchanged. -/
theorem WriteObjectFieldsPost.readUInt64_suffix
    {before after : LinearMemory} {base index : Nat} {fields : List Word32}
    (post : WriteObjectFieldsPost before after base index fields)
    (address : Nat)
    (suffix : objectFieldAddress base (index + fields.length) ≤ address) :
    after.readUInt64 address = before.readUInt64 address := by
  unfold LinearMemory.readUInt64
  rw [post.readUInt32_suffix address suffix]
  rw [post.readUInt32_suffix (address + 4) (by omega)]

/-- A bulk object-field write reads back every installed slot through the
public checked constructor decoder. -/
theorem readObjectField_of_writeObjectFields_at
    (state : MemoryState) (memory : LinearMemory) (address : Word32)
    (header : Header) (fields : List Word32) (index : Nat) (field : Word32)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (indexValid : index < header.aux1.toNat)
    (post : WriteObjectFieldsPost state.memory memory address.value 0 fields)
    (atIndex : fields[index]? = some field) :
    readObjectField ({ state with memory } : MemoryState) address index =
      .ok field := by
  have heap : address.classify = .heap := by
    have checked := headerRead
    unfold MemoryState.readLiveHeader at checked
    split at checked
    next heap => exact heap
    next => contradiction
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      fields post]
    exact headerRead
  have constructorHeaderAfter :
      readConstructorHeader ({ state with memory } : MemoryState) address =
        .ok header := by
    unfold readConstructorHeader
    simp [heap, headerAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have fieldRead : memory.readWord32 (objectFieldAddress address.value index) =
      .ok field := by
    simpa only [Nat.zero_add] using post.fieldAt index field atIndex
  have paddingRead :
      memory.readUInt32 (objectFieldAddress address.value index + 4) = .ok 0 := by
    simpa only [Nat.zero_add] using post.paddingAt index field atIndex
  have exactField : memory.readWord32
      (address.value + headerBytes + target.semanticSlotBytes * index) =
      .ok field := by
    simpa [objectFieldAddress] using fieldRead
  have exactPadding : memory.readUInt32
      (address.value + headerBytes + target.semanticSlotBytes * index + 4) =
      .ok 0 := by
    simpa [objectFieldAddress] using paddingRead
  unfold readObjectField
  rw [constructorHeaderAfter]
  simp only [Bind.bind, Except.bind]
  simp [indexValid, exactField, exactPadding, liftMemory]
  rfl

/-- Slots at or beyond the bulk writer's half-open interval continue to
decode exactly as before. -/
theorem readObjectField_of_writeObjectFields_suffix
    (state : MemoryState) (memory : LinearMemory) (address : Word32)
    (header : Header) (fields : List Word32) (index : Nat)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (retained : fields.length ≤ index)
    (post : WriteObjectFieldsPost state.memory memory address.value 0 fields) :
    readObjectField ({ state with memory } : MemoryState) address index =
      readObjectField state address index := by
  have heap : address.classify = .heap := by
    have checked := headerRead
    unfold MemoryState.readLiveHeader at checked
    split at checked
    next heap => exact heap
    next => contradiction
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      fields post]
    exact headerRead
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have constructorHeaderAfter :
      readConstructorHeader ({ state with memory } : MemoryState) address =
        .ok header := by
    unfold readConstructorHeader
    simp [heap, headerAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have lowFrame :
      memory.readUInt32 (objectFieldAddress address.value index) =
        state.memory.readUInt32 (objectFieldAddress address.value index) := by
    apply post.wordFrame
    right
    simp [objectFieldAddress, target]
    omega
  have paddingFrame :
      memory.readUInt32 (objectFieldAddress address.value index + 4) =
        state.memory.readUInt32 (objectFieldAddress address.value index + 4) := by
    apply post.wordFrame
    right
    simp [objectFieldAddress, target]
    omega
  have lowFrame' :
      memory.readUInt32 (address.value + headerBytes +
        target.semanticSlotBytes * index) =
      state.memory.readUInt32 (address.value + headerBytes +
        target.semanticSlotBytes * index) := by
    simpa [objectFieldAddress] using lowFrame
  have paddingFrame' :
      memory.readUInt32 (address.value + headerBytes +
        target.semanticSlotBytes * index + 4) =
      state.memory.readUInt32 (address.value + headerBytes +
        target.semanticSlotBytes * index + 4) := by
    simpa [objectFieldAddress] using paddingFrame
  unfold readObjectField
  rw [constructorHeaderAfter, constructorHeaderBefore]
  simp only [Bind.bind, Except.bind]
  unfold LinearMemory.readWord32
  rw [lowFrame', paddingFrame']

/-- A bounded bulk object-field prefix write leaves every checked `USize`
projection unchanged. -/
theorem readUSizeField_of_writeObjectFields
    (state : MemoryState) (memory : LinearMemory) (address : Word32)
    (header : Header) (fields : List Word32) (index : Nat)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (writtenFits : fields.length ≤ header.aux1.toNat)
    (post : WriteObjectFieldsPost state.memory memory address.value 0 fields) :
    readUSizeField ({ state with memory } : MemoryState) address index =
      readUSizeField state address index := by
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      fields post]
    exact headerRead
  have constructorHeaderBefore :=
    readConstructorHeader_eq_ok_of_readLiveHeader state address header headerRead
      headerKind
  have constructorHeaderAfter :=
    readConstructorHeader_eq_ok_of_readLiveHeader
      ({ state with memory } : MemoryState) address header headerAfter headerKind
  have payloadFrame : memory.readUInt64
        (address.value + headerBytes +
          target.semanticSlotBytes * (header.aux1.toNat + index)) =
      state.memory.readUInt64
        (address.value + headerBytes +
          target.semanticSlotBytes * (header.aux1.toNat + index)) := by
    apply post.readUInt64_suffix
    simp [objectFieldAddress, target]
    omega
  unfold readUSizeField
  rw [constructorHeaderAfter, constructorHeaderBefore]
  simp only [Bind.bind, Except.bind]
  rw [payloadFrame]

/-- A bounded bulk object-field prefix write leaves every checked packed-byte
projection unchanged. -/
theorem readScalarUInt8Field_of_writeObjectFields
    (state : MemoryState) (memory : LinearMemory) (address : Word32)
    (header : Header) (fields : List Word32) (slotIndex byteOffset : Nat)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (writtenFits : fields.length ≤ header.aux1.toNat)
    (slotIndexEq : slotIndex = header.aux1.toNat + header.aux2.toNat)
    (post : WriteObjectFieldsPost state.memory memory address.value 0 fields) :
    readScalarUInt8Field ({ state with memory } : MemoryState) address
        slotIndex byteOffset =
      readScalarUInt8Field state address slotIndex byteOffset := by
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      fields post]
    exact headerRead
  have constructorHeaderBefore :=
    readConstructorHeader_eq_ok_of_readLiveHeader state address header headerRead
      headerKind
  have constructorHeaderAfter :=
    readConstructorHeader_eq_ok_of_readLiveHeader
      ({ state with memory } : MemoryState) address header headerAfter headerKind
  have payloadFrame : memory.readByte
        (address.value + headerBytes + target.semanticSlotBytes * slotIndex +
          byteOffset) =
      state.memory.readByte
        (address.value + headerBytes + target.semanticSlotBytes * slotIndex +
          byteOffset) := by
    apply post.readByte_suffix
    simp [objectFieldAddress, target, slotIndexEq]
    omega
  have payloadFrame' : memory.readByte
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset) =
      state.memory.readByte
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset) := by
    simpa [slotIndexEq] using payloadFrame
  unfold readScalarUInt8Field
  rw [constructorHeaderAfter, constructorHeaderBefore]
  simp only [Bind.bind, Except.bind]
  by_cases fieldFits : byteOffset + 1 ≤ header.aux3.toNat
  · simp [scalarFieldAddress, slotIndexEq, fieldFits]
    change liftMemory (memory.readByte
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset)) =
      liftMemory (state.memory.readByte
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset))
    rw [payloadFrame']
  · simp [scalarFieldAddress, slotIndexEq, fieldFits]
    rfl

/-- A bounded bulk object-field prefix write leaves every checked packed
16-bit projection unchanged. -/
theorem readScalarUInt16Field_of_writeObjectFields
    (state : MemoryState) (memory : LinearMemory) (address : Word32)
    (header : Header) (fields : List Word32) (slotIndex byteOffset : Nat)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (writtenFits : fields.length ≤ header.aux1.toNat)
    (slotIndexEq : slotIndex = header.aux1.toNat + header.aux2.toNat)
    (post : WriteObjectFieldsPost state.memory memory address.value 0 fields) :
    readScalarUInt16Field ({ state with memory } : MemoryState) address
        slotIndex byteOffset =
      readScalarUInt16Field state address slotIndex byteOffset := by
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      fields post]
    exact headerRead
  have constructorHeaderBefore :=
    readConstructorHeader_eq_ok_of_readLiveHeader state address header headerRead
      headerKind
  have constructorHeaderAfter :=
    readConstructorHeader_eq_ok_of_readLiveHeader
      ({ state with memory } : MemoryState) address header headerAfter headerKind
  have payloadFrame : memory.readUInt16
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset) =
      state.memory.readUInt16
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset) := by
    apply post.readUInt16_suffix
    simp [objectFieldAddress, target]
    omega
  unfold readScalarUInt16Field
  rw [constructorHeaderAfter, constructorHeaderBefore]
  simp only [Bind.bind, Except.bind]
  by_cases fieldFits : byteOffset + 2 ≤ header.aux3.toNat
  · simp [scalarFieldAddress, slotIndexEq, fieldFits]
    change liftMemory (memory.readUInt16
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset)) =
      liftMemory (state.memory.readUInt16
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset))
    rw [payloadFrame]
  · simp [scalarFieldAddress, slotIndexEq, fieldFits]
    rfl

/-- A bounded bulk object-field prefix write leaves every checked packed
32-bit projection unchanged. -/
theorem readScalarUInt32Field_of_writeObjectFields
    (state : MemoryState) (memory : LinearMemory) (address : Word32)
    (header : Header) (fields : List Word32) (slotIndex byteOffset : Nat)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (writtenFits : fields.length ≤ header.aux1.toNat)
    (slotIndexEq : slotIndex = header.aux1.toNat + header.aux2.toNat)
    (post : WriteObjectFieldsPost state.memory memory address.value 0 fields) :
    readScalarUInt32Field ({ state with memory } : MemoryState) address
        slotIndex byteOffset =
      readScalarUInt32Field state address slotIndex byteOffset := by
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      fields post]
    exact headerRead
  have constructorHeaderBefore :=
    readConstructorHeader_eq_ok_of_readLiveHeader state address header headerRead
      headerKind
  have constructorHeaderAfter :=
    readConstructorHeader_eq_ok_of_readLiveHeader
      ({ state with memory } : MemoryState) address header headerAfter headerKind
  have payloadFrame : memory.readUInt32
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset) =
      state.memory.readUInt32
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset) := by
    apply post.readUInt32_suffix
    simp [objectFieldAddress, target]
    omega
  unfold readScalarUInt32Field
  rw [constructorHeaderAfter, constructorHeaderBefore]
  simp only [Bind.bind, Except.bind]
  by_cases fieldFits : byteOffset + 4 ≤ header.aux3.toNat
  · simp [scalarFieldAddress, slotIndexEq, fieldFits]
    change liftMemory (memory.readUInt32
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset)) =
      liftMemory (state.memory.readUInt32
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset))
    rw [payloadFrame]
  · simp [scalarFieldAddress, slotIndexEq, fieldFits]
    rfl

/-- A bounded bulk object-field prefix write leaves every checked packed
64-bit projection unchanged. -/
theorem readScalarUInt64Field_of_writeObjectFields
    (state : MemoryState) (memory : LinearMemory) (address : Word32)
    (header : Header) (fields : List Word32) (slotIndex byteOffset : Nat)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (writtenFits : fields.length ≤ header.aux1.toNat)
    (slotIndexEq : slotIndex = header.aux1.toNat + header.aux2.toNat)
    (post : WriteObjectFieldsPost state.memory memory address.value 0 fields) :
    readScalarUInt64Field ({ state with memory } : MemoryState) address
        slotIndex byteOffset =
      readScalarUInt64Field state address slotIndex byteOffset := by
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      fields post]
    exact headerRead
  have constructorHeaderBefore :=
    readConstructorHeader_eq_ok_of_readLiveHeader state address header headerRead
      headerKind
  have constructorHeaderAfter :=
    readConstructorHeader_eq_ok_of_readLiveHeader
      ({ state with memory } : MemoryState) address header headerAfter headerKind
  have payloadFrame : memory.readUInt64
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset) =
      state.memory.readUInt64
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset) := by
    apply post.readUInt64_suffix
    simp [objectFieldAddress, target]
    omega
  unfold readScalarUInt64Field
  rw [constructorHeaderAfter, constructorHeaderBefore]
  simp only [Bind.bind, Except.bind]
  by_cases fieldFits : byteOffset + 8 ≤ header.aux3.toNat
  · simp [scalarFieldAddress, slotIndexEq, fieldFits]
    change liftMemory (memory.readUInt64
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset)) =
      liftMemory (state.memory.readUInt64
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + header.aux2.toNat) + byteOffset))
    rw [payloadFrame]
  · simp [scalarFieldAddress, slotIndexEq, fieldFits]
    rfl

/-- A payload writer contained in the allocated prefix preserves the global
zero-frontier invariant. -/
theorem MemoryState.FrontierInvariant.writeObjectFields
    {state : MemoryState} {result : LinearMemory} {base index : Nat}
    {fields : List Word32} (valid : state.FrontierInvariant)
    (beforeFrontier : objectFieldAddress base (index + fields.length) ≤
      state.heapCursor)
    (written : Fir.Wasm.Concrete.writeObjectFields state.memory base index fields =
      .ok result) :
    ({ state with memory := result } : MemoryState).FrontierInvariant := by
  have inBounds : objectFieldAddress base (index + fields.length) ≤
      state.memory.size := Nat.le_trans beforeFrontier valid.cursorInBounds
  have post := writeObjectFields_post state.memory result base index fields
    inBounds written
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
  have framed := post.byteFrame byte (.inr
    (Nat.le_trans beforeFrontier afterCursor))
  cases resultByte : result[byte]? with
  | none => simp [LinearMemory.readByte, resultByte, oldZero] at framed
  | some value =>
      simp [LinearMemory.readByte, resultByte, oldZero] at framed
      subst value
      rfl

/-- Installing constructor object slots after a successful object allocation
preserves the checked header and frontier, establishes every field/padding
read, and leaves the remainder of the fresh payload zero. -/
theorem MemoryState.FrontierInvariant.allocateObject_writeObjectFields
    {state middle : MemoryState} {finalMemory : LinearMemory}
    {kind : ObjectKind} {payloadBytes : Nat} {persistent : Bool}
    {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    {fields : List Word32}
    (valid : state.FrontierInvariant)
    (allocated : state.allocateObject kind payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (middle, address))
    (fieldsEnd : objectFieldAddress address.value fields.length ≤
      address.value + align8 (headerBytes + payloadBytes))
    (written : Fir.Wasm.Concrete.writeObjectFields middle.memory address.value 0
      fields = Except.ok finalMemory) :
    let final : MemoryState := { middle with memory := finalMemory }
    final.FrontierInvariant ∧
    final.readLiveHeader address = .ok
      (Header.forAllocation kind (align8 (headerBytes + payloadBytes))
        persistent aux0 aux1 aux2 aux3) ∧
    WriteObjectFieldsPost middle.memory finalMemory address.value 0 fields ∧
    ∀ byte,
      objectFieldAddress address.value fields.length ≤ byte →
      byte < address.value + align8 (headerBytes + payloadBytes) →
      finalMemory[byte]? = some 0 := by
  dsimp only
  have middleValid := valid.allocateObject allocated
  obtain ⟨allocatedMiddle, allocateResult, _, cursorEq, _⟩ :=
    MemoryState.allocateObject_header state middle kind payloadBytes persistent
      aux0 aux1 aux2 aux3 address allocated
  have allocationPost := MemoryState.allocate_spec state allocatedMiddle
    (align8 (headerBytes + payloadBytes)) address allocateResult
  have allocationAligned :
      align8 (align8 (headerBytes + payloadBytes)) =
        align8 (headerBytes + payloadBytes) := by simp
  have middleCursor : middle.heapCursor =
      address.value + align8 (headerBytes + payloadBytes) := by
    rw [cursorEq, allocationPost.cursor, allocationPost.addressValue,
      allocationAligned]
  have beforeFrontier : objectFieldAddress address.value (0 + fields.length) ≤
      middle.heapCursor := by
    simp only [Nat.zero_add]
    rw [middleCursor]
    exact fieldsEnd
  have post := writeObjectFields_post middle.memory finalMemory address.value 0
    fields (Nat.le_trans beforeFrontier middleValid.cursorInBounds) written
  have finalValid := middleValid.writeObjectFields beforeFrontier written
  have headerBefore :=
    MemoryState.readLiveHeader_of_allocateObject_eq_ok state middle kind payloadBytes
      persistent aux0 aux1 aux2 aux3 address allocated
  have headerAfter := MemoryState.readLiveHeader_of_writeObjectFields middle
    finalMemory address 0 fields post
  have headerRead : ({ middle with memory := finalMemory } : MemoryState).readLiveHeader
      address = .ok (Header.forAllocation kind
        (align8 (headerBytes + payloadBytes)) persistent aux0 aux1 aux2 aux3) := by
    rw [headerAfter]
    exact headerBefore
  refine ⟨finalValid, headerRead, post, ?_⟩
  have freshZero := valid.allocateObject_payload_zero allocated
  intro byte afterFields beforeEnd
  have middleZero := freshZero byte (by
    simp [objectFieldAddress, target] at afterFields ⊢
    omega) beforeEnd
  have framed := post.byteFrame byte (.inr (by simpa using afterFields))
  cases finalByte : finalMemory[byte]? with
  | none => simp [LinearMemory.readByte, finalByte, middleZero] at framed
  | some value =>
      simp [LinearMemory.readByte, finalByte, middleZero] at framed
      subst value
      rfl

end Fir.Wasm.Concrete
