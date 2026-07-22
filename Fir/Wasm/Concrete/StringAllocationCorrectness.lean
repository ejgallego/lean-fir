import Fir.Wasm.Concrete.FreshAllocationCorrectness

namespace Fir.Wasm.Concrete

/-- Exact spatial postcondition for installing one contiguous UTF-8 payload. -/
structure WriteStringBytesPost (before after : LinearMemory)
    (base index : Nat) (bytes : List UInt8) : Prop where
  size : after.size = before.size
  byteAt : ∀ offset byte,
    bytes[offset]? = some byte →
    after.readByte (base + headerBytes + index + offset) = .ok byte
  byteFrame : ∀ other,
    other < base + headerBytes + index ∨
      base + headerBytes + index + bytes.length ≤ other →
    after.readByte other = before.readByte other

/-- The recursive string writer installs every byte exactly and frames every
address outside its contiguous payload interval. -/
theorem writeStringBytes_spec (memory : LinearMemory) (base index : Nat)
    (bytes : List UInt8)
    (inBounds : base + headerBytes + index + bytes.length ≤ memory.size) :
    ∃ result,
      writeStringBytes memory base index bytes = .ok result ∧
      WriteStringBytesPost memory result base index bytes := by
  induction bytes generalizing memory index with
  | nil =>
      refine ⟨memory, rfl, rfl, ?_, ?_⟩
      · intro offset byte atOffset
        simp at atOffset
      · intro other _
        rfl
  | cons byte rest ih =>
      let slot := base + headerBytes + index
      have slotInBounds : slot < memory.size := by
        simp only [List.length_cons] at inBounds
        simp [slot] at inBounds ⊢
        omega
      let next := memory.set slot byte slotInBounds
      have headWrite : memory.writeByte slot byte = .ok next := by
        simp [LinearMemory.writeByte, slotInBounds, next]
      have nextSize : next.size = memory.size := by simp [next]
      have tailInBounds :
          base + headerBytes + (index + 1) + rest.length ≤ next.size := by
        rw [nextSize]
        simp only [List.length_cons] at inBounds
        omega
      obtain ⟨result, tailWrite, tailPost⟩ := ih next (index + 1) tailInBounds
      refine ⟨result, ?_, ?_⟩
      · unfold writeStringBytes
        change (do
          let memory ← memory.writeByte slot byte
          writeStringBytes memory base (index + 1) rest) = .ok result
        rw [headWrite]
        exact tailWrite
      · refine ⟨tailPost.size.trans nextSize, ?_, ?_⟩
        · intro offset item atOffset
          cases offset with
          | zero =>
              simp at atOffset
              subst item
              calc
                result.readByte (base + headerBytes + index + 0) =
                    LinearMemory.readByte next slot := by
                      apply tailPost.byteFrame
                      left
                      simp [slot]
                _ = .ok byte := by
                      exact LinearMemory.readByte_set_same memory slot byte
                        slotInBounds
          | succ offset =>
              have restAt : rest[offset]? = some item := by simpa using atOffset
              have read := tailPost.byteAt offset item restAt
              simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using read
        · intro other separated
          have tailSeparated :
              other < base + headerBytes + (index + 1) ∨
                base + headerBytes + (index + 1) + rest.length ≤ other := by
            simp only [List.length_cons] at separated
            omega
          have different : slot ≠ other := by
            simp only [List.length_cons] at separated
            simp [slot] at separated ⊢
            omega
          calc
            result.readByte other = LinearMemory.readByte next other :=
              tailPost.byteFrame other tailSeparated
            _ = memory.readByte other := by
              exact LinearMemory.readByte_set_other memory slot other byte
                slotInBounds different

/-- Reading a byte sequence described by an exact writer post returns that
same sequence in source order. -/
theorem readStringBytes_of_byteAt
    (memory : LinearMemory) (base index : Nat) (bytes : List UInt8)
    (byteAt : ∀ offset byte,
      bytes[offset]? = some byte →
      memory.readByte (base + headerBytes + index + offset) = .ok byte) :
    readStringBytes memory base index bytes.length = .ok bytes := by
  induction bytes generalizing index with
  | nil => rfl
  | cons byte rest ih =>
      have headRead : memory.readByte (base + headerBytes + index) = .ok byte := by
        simpa using byteAt 0 byte (by simp)
      simp only [List.length_cons]
      unfold readStringBytes
      rw [headRead]
      have tailAt : ∀ offset item,
          rest[offset]? = some item →
          memory.readByte (base + headerBytes + (index + 1) + offset) =
            .ok item := by
        intro offset item atOffset
        have read := byteAt (offset + 1) item (by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using atOffset)
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using read
      rw [ih (index + 1) tailAt]
      rfl

/-- An exact string writer post gives the public raw decoder result. -/
theorem WriteStringBytesPost.readStringBytes
    {before after : LinearMemory} {base index : Nat} {bytes : List UInt8}
    (post : WriteStringBytesPost before after base index bytes) :
    Fir.Wasm.Concrete.readStringBytes after base index bytes.length = .ok bytes :=
  readStringBytes_of_byteAt after base index bytes post.byteAt

/-- A successful bounded UTF-8 payload write has the exact decoder result and
spatial frame. -/
theorem writeStringBytes_post
    (memory result : LinearMemory) (base index : Nat) (bytes : List UInt8)
    (inBounds : base + headerBytes + index + bytes.length ≤ memory.size)
    (written : writeStringBytes memory base index bytes = .ok result) :
    WriteStringBytesPost memory result base index bytes := by
  obtain ⟨actual, actualWrite, post⟩ :=
    writeStringBytes_spec memory base index bytes inBounds
  rw [actualWrite] at written
  cases written
  exact post

theorem WriteStringBytesPost.readUInt32_prefix
    {before after : LinearMemory} {base index : Nat} {bytes : List UInt8}
    (post : WriteStringBytesPost before after base index bytes)
    (address : Nat)
    (beforeBytes : address + 4 ≤ base + headerBytes + index) :
    after.readUInt32 address = before.readUInt32 address := by
  unfold LinearMemory.readUInt32
  rw [post.byteFrame address (.inl (by omega))]
  rw [post.byteFrame (address + 1) (.inl (by omega))]
  rw [post.byteFrame (address + 2) (.inl (by omega))]
  rw [post.byteFrame (address + 3) (.inl (by omega))]

/-- UTF-8 payload installation starts after and therefore preserves the common
object header. -/
theorem Header.read_of_writeStringBytes
    (before after : LinearMemory) (address : Word32) (bytes : List UInt8)
    (post : WriteStringBytesPost before after address.value 0 bytes) :
    Header.read after address = Header.read before address := by
  have frame (offset : Nat) (withinHeader : offset + 4 ≤ headerBytes) :
      after.readUInt32 (address.value + offset) =
        before.readUInt32 (address.value + offset) := by
    apply post.readUInt32_prefix
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

theorem MemoryState.readLiveHeader_of_writeStringBytes
    (state : MemoryState) (result : LinearMemory) (address : Word32)
    (bytes : List UInt8)
    (post : WriteStringBytesPost state.memory result address.value 0 bytes) :
    ({ state with memory := result } : MemoryState).readLiveHeader address =
      state.readLiveHeader address := by
  have headerRead := Header.read_of_writeStringBytes state.memory result address
    bytes post
  unfold MemoryState.readLiveHeader
  dsimp only
  rw [headerRead, post.size]

/-- A bounded UTF-8 payload write preserves the allocator's zero-suffix
invariant. -/
theorem MemoryState.FrontierInvariant.writeStringBytes
    {state : MemoryState} {result : LinearMemory} {base index : Nat}
    {bytes : List UInt8} (valid : state.FrontierInvariant)
    (beforeFrontier : base + headerBytes + index + bytes.length ≤
      state.heapCursor)
    (written : writeStringBytes state.memory base index bytes = .ok result) :
    ({ state with memory := result } : MemoryState).FrontierInvariant := by
  have inBounds : base + headerBytes + index + bytes.length ≤
      state.memory.size := Nat.le_trans beforeFrontier valid.cursorInBounds
  have post := writeStringBytes_post state.memory result base index bytes
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
  | some byteValue =>
      simp [LinearMemory.readByte, resultByte, oldZero] at framed
      subst byteValue
      rfl

private theorem uint32Field_string_success (field : String) (value : Nat)
    (result : UInt32) (encoded : uint32Field field value = .ok result) :
    value < UInt32.size ∧ result = UInt32.ofNat value := by
  unfold uint32Field at encoded
  split at encoded
  next fits => exact ⟨fits, (Except.ok.inj encoded).symm⟩
  next overflow => contradiction

/-- A successful concrete string allocation decomposes into one checked object
allocation followed by the exact UTF-8 byte writer. -/
theorem allocateString_decompose
    (state result : MemoryState) (value : String) (address : Word32)
    (allocated : allocateString state value = .ok (result, address)) :
    let bytes := stringUtf8Bytes value
    ∃ byteCount middle,
      uint32Field "string UTF-8 byte count" bytes.length = .ok byteCount ∧
      state.allocateObject .string bytes.length false stringUtf8Marker byteCount =
        .ok (middle, address) ∧
      writeStringBytes middle.memory address.value 0 bytes =
        .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  dsimp only
  unfold allocateString at allocated
  dsimp only at allocated
  cases countResult :
      uint32Field "string UTF-8 byte count" (stringUtf8Bytes value).length with
  | error failure =>
      rw [countResult] at allocated
      contradiction
  | ok byteCount =>
      rw [countResult] at allocated
      simp only [Bind.bind, Except.bind] at allocated
      cases objectAllocation : state.allocateObject .string
          (stringUtf8Bytes value).length false stringUtf8Marker byteCount with
      | error failure =>
          rw [objectAllocation] at allocated
          contradiction
      | ok pair =>
          rcases pair with ⟨middle, actualAddress⟩
          rw [objectAllocation] at allocated
          change (do
            let memory ← liftMemory <|
              writeStringBytes middle.memory actualAddress.value 0
                (stringUtf8Bytes value)
            return ({ middle with memory }, actualAddress)) =
              .ok (result, address) at allocated
          cases byteWrite : writeStringBytes middle.memory actualAddress.value 0
              (stringUtf8Bytes value) with
          | error failure =>
              rw [byteWrite] at allocated
              contradiction
          | ok finalMemory =>
              rw [byteWrite] at allocated
              change Except.ok ({ middle with memory := finalMemory }, actualAddress) =
                Except.ok (result, address) at allocated
              have pairEq : ({ middle with memory := finalMemory }, actualAddress) =
                  (result, address) := Except.ok.inj allocated
              have resultEq : { middle with memory := finalMemory } = result :=
                congrArg Prod.fst pairEq
              have addressEq : actualAddress = address := congrArg Prod.snd pairEq
              subst result
              subst address
              exact ⟨byteCount, middle, rfl, objectAllocation, byteWrite, rfl⟩

/-- String allocation preserves every byte owned by the old concrete heap. -/
theorem allocateString_prefixExtension
    (state result : MemoryState) (value : String) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocateString state value = .ok (result, address)) :
    state.PrefixExtension result := by
  obtain ⟨byteCount, middle, _, objectAllocation, byteWrite, cursorEq⟩ :=
    allocateString_decompose state result value address allocated
  have objectExtension := valid.allocateObject_prefixExtension objectAllocation
  have freshAddress := valid.allocateObject_address objectAllocation
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadEnd : address.value + headerBytes + 0 +
      (stringUtf8Bytes value).length ≤ middle.heapCursor := by
    rw [middleExtent]
    have aligned := align8_ge
      (headerBytes + (stringUtf8Bytes value).length)
    omega
  have payloadPost := writeStringBytes_post middle.memory result.memory
    address.value 0 (stringUtf8Bytes value)
    (Nat.le_trans payloadEnd middleValid.cursorInBounds) byteWrite
  refine {
    cursor := by simpa [cursorEq] using objectExtension.cursor
    memorySize := Nat.le_trans objectExtension.memorySize (by
      rw [payloadPost.size]
      exact Nat.le_refl _)
    readByte := ?_ }
  intro byte beforeCursor
  calc
    result.memory.readByte byte = middle.memory.readByte byte :=
      payloadPost.byteFrame byte (.inl (by
        rw [freshAddress]
        omega))
    _ = state.memory.readByte byte := objectExtension.readByte byte beforeCursor

/-- Fully decoded shape of one fresh ordinary UTF-8 string allocation. The
relation compares canonical source bytes directly and records every header
field needed by the checked public decoder. -/
structure StringObjectRel (state : MemoryState) (address : Word32)
    (value : String) (header : Header) : Prop where
  headerRead : state.readLiveHeader address = .ok header
  headerKind : header.kind = .string
  ordinary : header.persistent = false
  marker : header.aux0 = stringUtf8Marker
  byteCount : header.aux1.toNat = (stringUtf8Bytes value).length
  reserved2 : header.aux2 = 0
  reserved3 : header.aux3 = 0
  allocationBytes : header.allocationBytes.toNat =
    align8 (headerBytes + (stringUtf8Bytes value).length)
  extent : address.value + header.allocationBytes.toNat ≤ state.heapCursor
  bytesFit : headerBytes + header.aux1.toNat ≤
    header.allocationBytes.toNat
  rawDecoded : readStringBytes state.memory address.value 0 header.aux1.toNat =
    .ok (stringUtf8Bytes value)
  refCountOne : header.refCount.toNat = 1

/-- The exact byte-level relation discharges every check in the public string
payload decoder. -/
theorem StringObjectRel.readPayload
    {state : MemoryState} {address : Word32} {value : String} {header : Header}
    (related : StringObjectRel state address value header) :
    readStringPayload state address = .ok (stringUtf8Bytes value) := by
  have heap := (MemoryState.PrefixExtension.readLiveHeader_facts
    state address header related.headerRead).1
  unfold readStringPayload
  simp only [heap, ↓reduceIte, Bind.bind, Except.bind]
  rw [related.headerRead]
  simp only [liftMemory]
  have kindCheck : (header.kind == ObjectKind.string) = true := by
    rw [related.headerKind]
    decide
  rw [if_pos kindCheck]
  have metadataCheck :
      (header.aux0 == stringUtf8Marker && header.aux2 == 0 &&
        header.aux3 == 0 && decide (headerBytes + header.aux1.toNat ≤
          header.allocationBytes.toNat)) = true := by
    simp [related.marker, related.reserved2, related.reserved3,
      related.bytesFit]
  rw [if_pos metadataCheck]
  rw [related.rawDecoded]

/-- A successful fresh string allocation preserves the frontier invariant and
establishes the exact checked UTF-8 object relation. -/
theorem allocateString_objectRel
    (state result : MemoryState) (value : String) (address : Word32)
    (valid : state.FrontierInvariant)
    (allocated : allocateString state value = .ok (result, address)) :
    result.FrontierInvariant ∧
      ∃ header, StringObjectRel result address value header := by
  obtain ⟨byteCount, middle, countEncoded, objectAllocation, byteWrite,
      cursorEq⟩ := allocateString_decompose state result value address allocated
  obtain ⟨countFits, countEq⟩ := uint32Field_string_success
    "string UTF-8 byte count" (stringUtf8Bytes value).length byteCount countEncoded
  have countToNat : byteCount.toNat = (stringUtf8Bytes value).length := by
    rw [countEq]
    exact UInt32.toNat_ofNat_of_lt' countFits
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadEnd : address.value + headerBytes + 0 +
      (stringUtf8Bytes value).length ≤ middle.heapCursor := by
    rw [middleExtent]
    have aligned := align8_ge
      (headerBytes + (stringUtf8Bytes value).length)
    omega
  have payloadInBounds : address.value + headerBytes + 0 +
      (stringUtf8Bytes value).length ≤ middle.memory.size :=
    Nat.le_trans payloadEnd middleValid.cursorInBounds
  have payloadPost := writeStringBytes_post middle.memory result.memory
    address.value 0 (stringUtf8Bytes value) payloadInBounds byteWrite
  have stateEq : ({ middle with memory := result.memory } : MemoryState) = result := by
    cases middle
    cases result
    simp_all
  have finalValid : result.FrontierInvariant := by
    rw [← stateEq]
    exact middleValid.writeStringBytes payloadEnd byteWrite
  let allocationBytes :=
    align8 (headerBytes + (stringUtf8Bytes value).length)
  let header := Header.forAllocation .string allocationBytes false
    stringUtf8Marker byteCount
  have headerBefore : middle.readLiveHeader address = .ok header := by
    simpa [header, allocationBytes] using
      MemoryState.readLiveHeader_of_allocateObject_eq_ok state middle .string
        (stringUtf8Bytes value).length false stringUtf8Marker byteCount 0 0 address
        objectAllocation
  have headerFrame := middle.readLiveHeader_of_writeStringBytes result.memory
    address (stringUtf8Bytes value) payloadPost
  have headerRead : result.readLiveHeader address = .ok header := by
    rw [← stateEq, headerFrame]
    exact headerBefore
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state middle .string
      (stringUtf8Bytes value).length false stringUtf8Marker byteCount 0 0 address
      objectAllocation
  have allocationPost := MemoryState.allocate_spec state rawState allocationBytes
    address (by simpa [allocationBytes] using rawAllocation)
  have addressNonzero : address.value ≠ 0 := by
    intro zero
    have heap := allocationPost.addressClass
    simp [Word32.classify, zero] at heap
  have allocationLt : allocationBytes < UInt32.size := by
    have within := allocationPost.endWithinAddressSpace
    have aligned : align8 allocationBytes = allocationBytes := by
      simp [allocationBytes]
    rw [aligned] at within
    have belowWordModulus : allocationBytes < wordModulus := by omega
    simpa [wordModulus] using belowWordModulus
  have allocationToNat : (UInt32.ofNat allocationBytes).toNat = allocationBytes :=
    UInt32.toNat_ofNat_of_lt' allocationLt
  have resultExtent : address.value + allocationBytes ≤ result.heapCursor := by
    rw [cursorEq, middleExtent]
    exact Nat.le_refl _
  have decodedBytes : readStringBytes result.memory address.value 0
      (stringUtf8Bytes value).length = .ok (stringUtf8Bytes value) :=
    payloadPost.readStringBytes
  have bytesFit : headerBytes + (stringUtf8Bytes value).length ≤
      allocationBytes := by
    exact align8_ge _
  refine ⟨finalValid, header, {
    headerRead := headerRead
    headerKind := by rfl
    ordinary := by rfl
    marker := by rfl
    byteCount := countToNat
    reserved2 := by rfl
    reserved3 := by rfl
    allocationBytes := by
      change (UInt32.ofNat allocationBytes).toNat = allocationBytes
      exact allocationToNat
    extent := by
      change address.value + (UInt32.ofNat allocationBytes).toNat ≤
        result.heapCursor
      rw [allocationToNat]
      exact resultExtent
    bytesFit := by
      change headerBytes + byteCount.toNat ≤
        (UInt32.ofNat allocationBytes).toNat
      rw [countToNat, allocationToNat]
      exact bytesFit
    rawDecoded := by
      change readStringBytes result.memory address.value 0 byteCount.toNat =
        .ok (stringUtf8Bytes value)
      rw [countToNat]
      exact decodedBytes
    refCountOne := by rfl }⟩

end Fir.Wasm.Concrete
