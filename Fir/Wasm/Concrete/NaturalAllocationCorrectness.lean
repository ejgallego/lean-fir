import Fir.Wasm.Concrete.HeapRefinement
import Fir.Wasm.Concrete.FreshAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Mathematical value of a little-endian base-`2^64` limb list. -/
def naturalLimbsValue : List UInt64 → Nat
  | [] => 0
  | limb :: rest => limb.toNat + UInt64.size * naturalLimbsValue rest

/--
Exact wasm32 frontier cost of a concrete natural literal.

Small source naturals that fit the wasm32 immediate payload allocate nothing.
Larger source-tagged values use one persistent promoted-tag object, while
source heap naturals use their complete little-endian limb extent.
-/
def naturalAllocationBytes (value : Nat) : Nat :=
  if value ≤ maxTaggedPayload then
    if value ≤ maxImmediatePayload then
      0
    else
      align8 (headerBytes + target.semanticSlotBytes)
  else
    align8
      (headerBytes + target.semanticSlotBytes * (naturalLimbs value).length)

/-- The executable limb splitter preserves the represented natural. -/
theorem naturalLimbs_value (value : Nat) :
    naturalLimbsValue (naturalLimbs value) = value := by
  induction value using naturalLimbs.induct with
  | case1 value small =>
      rw [naturalLimbs]
      simp [small, naturalLimbsValue, UInt64.toNat_ofNat_of_lt' small]
  | case2 value large ih =>
      rw [naturalLimbs]
      simp only [large, ↓reduceDIte, naturalLimbsValue]
      rw [ih]
      have remainder : value % UInt64.size < UInt64.size :=
        Nat.mod_lt _ (by decide)
      rw [UInt64.toNat_ofNat_of_lt' remainder]
      exact Nat.mod_add_div value UInt64.size

theorem LinearMemory.readUInt64_of_byteFrame
    (before after : LinearMemory) (address : Nat)
    (frame : ∀ offset, offset < 8 →
      after.readByte (address + offset) = before.readByte (address + offset)) :
    after.readUInt64 address = before.readUInt64 address := by
  have h0 : after.readByte address = before.readByte address := by
    simpa using frame 0 (by decide)
  have h1 : after.readByte (address + 1) = before.readByte (address + 1) :=
    frame 1 (by decide)
  have h2 : after.readByte (address + 2) = before.readByte (address + 2) :=
    frame 2 (by decide)
  have h3 : after.readByte (address + 3) = before.readByte (address + 3) :=
    frame 3 (by decide)
  have h4 : after.readByte (address + 4) = before.readByte (address + 4) :=
    frame 4 (by decide)
  have h5 : after.readByte (address + 4 + 1) =
      before.readByte (address + 4 + 1) := by
    simpa [Nat.add_assoc] using frame 5 (by decide)
  have h6 : after.readByte (address + 4 + 2) =
      before.readByte (address + 4 + 2) := by
    simpa [Nat.add_assoc] using frame 6 (by decide)
  have h7 : after.readByte (address + 4 + 3) =
      before.readByte (address + 4 + 3) := by
    simpa [Nat.add_assoc] using frame 7 (by decide)
  unfold LinearMemory.readUInt64 LinearMemory.readUInt32
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- Exact result of installing a contiguous list of natural limbs. -/
structure WriteNaturalLimbsPost (before after : LinearMemory)
    (base index : Nat) (limbs : List UInt64) : Prop where
  size : after.size = before.size
  limbAt : ∀ offset limb,
    limbs[offset]? = some limb →
    after.readUInt64
      (base + headerBytes + target.semanticSlotBytes * (index + offset)) = .ok limb
  byteFrame : ∀ other,
    other < base + headerBytes + target.semanticSlotBytes * index ∨
      base + headerBytes + target.semanticSlotBytes * (index + limbs.length) ≤ other →
    after.readByte other = before.readByte other

/-- The recursive writer installs every limb exactly and frames all bytes
outside its contiguous payload interval. -/
theorem writeNaturalLimbs_spec (memory : LinearMemory) (base index : Nat)
    (limbs : List UInt64)
    (inBounds : base + headerBytes +
      target.semanticSlotBytes * (index + limbs.length) ≤ memory.size) :
    ∃ result,
      writeNaturalLimbs memory base index limbs = .ok result ∧
      WriteNaturalLimbsPost memory result base index limbs := by
  induction limbs generalizing memory index with
  | nil =>
      refine ⟨memory, rfl, rfl, ?_, ?_⟩
      · intro offset limb atOffset
        simp at atOffset
      · intro other _
        rfl
  | cons limb rest ih =>
      let slot := base + headerBytes + target.semanticSlotBytes * index
      have slotInBounds : slot + 7 < memory.size := by
        simp only [List.length_cons] at inBounds
        simp [slot, target] at inBounds ⊢
        omega
      obtain ⟨slotMemory, slotWrite, _, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec memory slot limb.toUInt32 (by omega)
      obtain ⟨writtenMemory, highWrite, _, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec slotMemory (slot + 4)
          (limb >>> (32 : UInt64)).toUInt32 (by omega)
      have slotWrite64 : memory.writeUInt64 slot limb = .ok writtenMemory := by
        unfold LinearMemory.writeUInt64
        rw [slotWrite]
        exact highWrite
      have slotSize := LinearMemory.size_of_writeUInt64_eq_ok memory writtenMemory
        slot limb slotInBounds slotWrite64
      have slotRead := LinearMemory.readUInt64_of_writeUInt64_eq_ok memory
        writtenMemory slot limb slotInBounds slotWrite64
      have tailInBounds : base + headerBytes +
          target.semanticSlotBytes * (index + 1 + rest.length) ≤
            writtenMemory.size := by
        rw [slotSize]
        simp only [List.length_cons] at inBounds
        simp [target] at inBounds ⊢
        omega
      obtain ⟨result, tailWrite, tailPost⟩ :=
        ih writtenMemory (index + 1) tailInBounds
      refine ⟨result, ?_, ?_⟩
      · unfold writeNaturalLimbs
        change (do
          let memory ← memory.writeUInt64 slot limb
          writeNaturalLimbs memory base (index + 1) rest) = .ok result
        rw [slotWrite64]
        exact tailWrite
      · refine ⟨tailPost.size.trans slotSize, ?_, ?_⟩
        · intro offset item atOffset
          cases offset with
          | zero =>
              simp at atOffset
              subst item
              calc
                result.readUInt64
                    (base + headerBytes + target.semanticSlotBytes * (index + 0)) =
                    writtenMemory.readUInt64 slot := by
                      apply LinearMemory.readUInt64_of_byteFrame
                      intro byte byteLt
                      apply tailPost.byteFrame
                      left
                      simp [target]
                      omega
                _ = .ok limb := slotRead
          | succ offset =>
              have restAt : rest[offset]? = some item := by simpa using atOffset
              have read := tailPost.limbAt offset item restAt
              simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using read
        · intro other separated
          simp only [List.length_cons] at separated
          have tailSeparated :
              other < base + headerBytes +
                  target.semanticSlotBytes * (index + 1) ∨
                base + headerBytes +
                  target.semanticSlotBytes * (index + 1 + rest.length) ≤ other := by
            simp [target] at separated ⊢
            omega
          have slotSeparated : other < slot ∨ slot + 7 < other := by
            simp [slot, target] at separated ⊢
            omega
          calc
            result.readByte other = writtenMemory.readByte other :=
              tailPost.byteFrame other tailSeparated
            _ = memory.readByte other :=
              LinearMemory.readByte_of_writeUInt64_eq_ok_other memory writtenMemory
                slot limb slotInBounds slotWrite64 other slotSeparated

/-- Reading exactly a list of known limbs reconstructs its mathematical
little-endian value. -/
theorem readNaturalLimbs_of_limbAt
    (memory : LinearMemory) (base index : Nat) (limbs : List UInt64)
    (limbAt : ∀ offset limb,
      limbs[offset]? = some limb →
      memory.readUInt64
        (base + headerBytes + target.semanticSlotBytes * (index + offset)) =
          .ok limb) :
    Fir.Wasm.Concrete.readNaturalLimbs memory base index limbs.length =
      .ok (naturalLimbsValue limbs) := by
  induction limbs generalizing index with
  | nil => rfl
  | cons limb rest ih =>
      have headRead : memory.readUInt64
          (base + headerBytes + target.semanticSlotBytes * index) = .ok limb := by
        simpa using limbAt 0 limb (by simp)
      simp only [List.length_cons]
      unfold Fir.Wasm.Concrete.readNaturalLimbs
      rw [headRead]
      have tailAt : ∀ offset item,
          rest[offset]? = some item →
          memory.readUInt64
            (base + headerBytes +
              target.semanticSlotBytes * (index + 1 + offset)) = .ok item := by
        intro offset item atOffset
        have read := limbAt (offset + 1) item (by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using atOffset)
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using read
      rw [ih (index + 1) tailAt]
      rfl

/-- Reading exactly the limbs described by an exact writer post reconstructs
their mathematical little-endian value. -/
theorem WriteNaturalLimbsPost.readNaturalLimbs
    {before after : LinearMemory} {base index : Nat} {limbs : List UInt64}
    (post : WriteNaturalLimbsPost before after base index limbs) :
    Fir.Wasm.Concrete.readNaturalLimbs after base index limbs.length =
      .ok (naturalLimbsValue limbs) :=
  readNaturalLimbs_of_limbAt after base index limbs post.limbAt

/-- A successful bounded natural-limb write has the exact decoder result. -/
theorem readNaturalLimbs_of_write_eq_ok
    (memory result : LinearMemory) (base index : Nat) (limbs : List UInt64)
    (inBounds : base + headerBytes +
      target.semanticSlotBytes * (index + limbs.length) ≤ memory.size)
    (written : writeNaturalLimbs memory base index limbs = .ok result) :
    readNaturalLimbs result base index limbs.length =
      .ok (naturalLimbsValue limbs) := by
  obtain ⟨actual, actualWrite, post⟩ :=
    writeNaturalLimbs_spec memory base index limbs inBounds
  rw [actualWrite] at written
  cases written
  exact post.readNaturalLimbs

theorem writeNaturalLimbs_post
    (memory result : LinearMemory) (base index : Nat) (limbs : List UInt64)
    (inBounds : base + headerBytes +
      target.semanticSlotBytes * (index + limbs.length) ≤ memory.size)
    (written : writeNaturalLimbs memory base index limbs = .ok result) :
    WriteNaturalLimbsPost memory result base index limbs := by
  obtain ⟨actual, actualWrite, post⟩ :=
    writeNaturalLimbs_spec memory base index limbs inBounds
  rw [actualWrite] at written
  cases written
  exact post

theorem WriteNaturalLimbsPost.readUInt32_prefix
    {before after : LinearMemory} {base index : Nat} {limbs : List UInt64}
    (post : WriteNaturalLimbsPost before after base index limbs)
    (address : Nat)
    (beforeLimbs : address + 4 ≤
      base + headerBytes + target.semanticSlotBytes * index) :
    after.readUInt32 address = before.readUInt32 address := by
  unfold LinearMemory.readUInt32
  rw [post.byteFrame address (.inl (by omega))]
  rw [post.byteFrame (address + 1) (.inl (by omega))]
  rw [post.byteFrame (address + 2) (.inl (by omega))]
  rw [post.byteFrame (address + 3) (.inl (by omega))]

/-- Natural payload installation begins after, and therefore preserves, the
common object header. -/
theorem Header.read_of_writeNaturalLimbs
    (before after : LinearMemory) (address : Word32) (limbs : List UInt64)
    (post : WriteNaturalLimbsPost before after address.value 0 limbs) :
    Header.read after address = Header.read before address := by
  have frame (offset : Nat) (withinHeader : offset + 4 ≤ headerBytes) :
      after.readUInt32 (address.value + offset) =
        before.readUInt32 (address.value + offset) := by
    apply post.readUInt32_prefix
    simp [target]
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

theorem MemoryState.readLiveHeader_of_writeNaturalLimbs
    (state : MemoryState) (result : LinearMemory) (address : Word32)
    (limbs : List UInt64)
    (post : WriteNaturalLimbsPost state.memory result address.value 0 limbs) :
    ({ state with memory := result } : MemoryState).readLiveHeader address =
      state.readLiveHeader address := by
  have headerRead := Header.read_of_writeNaturalLimbs state.memory result address
    limbs post
  unfold MemoryState.readLiveHeader
  dsimp only
  rw [headerRead, post.size]

/-- A bounded limb payload write preserves the allocator's zero-suffix
invariant. -/
theorem MemoryState.FrontierInvariant.writeNaturalLimbs
    {state : MemoryState} {result : LinearMemory} {base index : Nat}
    {limbs : List UInt64} (valid : state.FrontierInvariant)
    (beforeFrontier : base + headerBytes +
      target.semanticSlotBytes * (index + limbs.length) ≤ state.heapCursor)
    (written : writeNaturalLimbs state.memory base index limbs = .ok result) :
    ({ state with memory := result } : MemoryState).FrontierInvariant := by
  have inBounds : base + headerBytes +
      target.semanticSlotBytes * (index + limbs.length) ≤ state.memory.size :=
    Nat.le_trans beforeFrontier valid.cursorInBounds
  have post := writeNaturalLimbs_post state.memory result base index limbs
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

theorem uint32Field_success (field : String) (value : Nat) (result : UInt32)
    (encoded : uint32Field field value = .ok result) :
    value < UInt32.size ∧ result = UInt32.ofNat value := by
  unfold uint32Field at encoded
  split at encoded
  next fits =>
    exact ⟨fits, (Except.ok.inj encoded).symm⟩
  next overflow => contradiction

/--
One exact source-path budget makes natural allocation constructive and
transports the residual budget across all three concrete representations:
wasm32 immediate, persistent promoted tag, and ordinary heap natural.
-/
theorem MemoryState.FrontierInvariant.allocateNatural_eq_ok_of_budget
    {state : MemoryState} (valid : state.FrontierInvariant) (value : Nat)
    {remainingBytes : Nat}
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : naturalAllocationBytes value ≤ remainingBytes) :
    ∃ result address,
      allocateNatural state value = .ok (result, address) ∧
        result.AddressSpaceBudget
          (remainingBytes - naturalAllocationBytes value) := by
  by_cases sourceTagged : value ≤ maxTaggedPayload
  · have valueLt : value < UInt64.size := by
      have taggedBound : maxTaggedPayload < UInt64.size := by decide
      omega
    have payloadToNat : (UInt64.ofNat value).toNat = value :=
      UInt64.toNat_ofNat_of_lt' valueLt
    by_cases immediate : value ≤ maxImmediatePayload
    · refine
        ⟨state, Word32.encodeImmediate value immediate, ?_, ?_⟩
      · simp [allocateNatural, sourceTagged, encodeTagged, payloadToNat,
          immediate]
      · simpa [naturalAllocationBytes, sourceTagged, immediate] using budget
    · have allocationFits :
          align8 (headerBytes + target.semanticSlotBytes) ≤ remainingBytes := by
        simpa [naturalAllocationBytes, sourceTagged, immediate] using fits
      obtain ⟨middle, address, objectAllocation⟩ :=
        state.allocateObject_eq_ok_of_capacity .natural
          target.semanticSlotBytes true promotedTagMarker 1 0 0
          valid.cursorAligned
          (budget.allocationCapacity (by
            simpa only [align8_align8] using allocationFits))
      have middleValid := valid.allocateObject objectAllocation
      have middleExtent := MemoryState.allocateObject_extent objectAllocation
      have payloadInBounds :
          address.value + headerBytes +
              target.semanticSlotBytes * (0 + [UInt64.ofNat value].length) ≤
            middle.memory.size := by
        have cursorInBounds := middleValid.cursorInBounds
        rw [middleExtent] at cursorInBounds
        have extent :=
          align8_ge (headerBytes + target.semanticSlotBytes)
        simp [target] at cursorInBounds extent ⊢
        omega
      obtain ⟨memory, payloadWrite, _⟩ :=
        writeNaturalLimbs_spec middle.memory address.value 0
          [UInt64.ofNat value] payloadInBounds
      let result : MemoryState := { middle with memory }
      have allocated :
          allocateNatural state value = .ok (result, address) := by
        have notImmediate :
            ¬(UInt64.ofNat value).toNat ≤ maxImmediatePayload := by
          rw [payloadToNat]
          exact immediate
        unfold allocateNatural
        rw [if_pos sourceTagged]
        unfold encodeTagged
        rw [dif_neg notImmediate]
        unfold allocatePromotedTag
        simp only [Bind.bind, Except.bind]
        have objectAllocation8 :
            state.allocateObject .natural 8 true promotedTagMarker 1 =
              .ok (middle, address) := by
          simpa [target] using objectAllocation
        rw [objectAllocation8]
        simp only [liftMemory]
        have write64 :
            middle.memory.writeUInt64 (address.value + headerBytes)
                (UInt64.ofNat value) =
              .ok memory := by
          cases writeEq :
              middle.memory.writeUInt64 (address.value + headerBytes)
                (UInt64.ofNat value) with
          | error failure =>
              simp [Fir.Wasm.Concrete.writeNaturalLimbs, target, writeEq,
                Bind.bind, Except.bind] at payloadWrite
          | ok actual =>
              have actualEq : actual = memory := by
                simpa [Fir.Wasm.Concrete.writeNaturalLimbs, target, writeEq,
                  Bind.bind, Except.bind] using payloadWrite
              subst actual
              rfl
        rw [write64]
        rfl
      have middleBudget :=
        budget.allocateObject valid.cursorAligned allocationFits
          objectAllocation
      have resultBudget :
          result.AddressSpaceBudget
            (remainingBytes -
              align8 (headerBytes + target.semanticSlotBytes)) := {
        cursorPositive := middleBudget.cursorPositive
        endWithinAddressSpace := middleBudget.endWithinAddressSpace }
      exact ⟨result, address, allocated, by
        simpa [naturalAllocationBytes, sourceTagged, immediate] using
          resultBudget⟩
  · let limbs := naturalLimbs value
    have allocationFits :
        align8
            (headerBytes + target.semanticSlotBytes * limbs.length) ≤
          remainingBytes := by
      simpa [naturalAllocationBytes, sourceTagged, limbs] using fits
    have limbCountFits : limbs.length < UInt32.size := by
      have endWithin :
          state.heapCursor +
              align8
                (align8
                  (headerBytes + target.semanticSlotBytes * limbs.length)) ≤
            wordModulus := by
        simpa [limbs] using
          (budget.allocationCapacity (by
            simpa only [align8_align8] using allocationFits)).endWithinAddressSpace
      simp only [align8_align8] at endWithin
      have extent :=
        align8_ge (headerBytes + target.semanticSlotBytes * limbs.length)
      have cursorPositive := budget.cursorPositive
      have belowWordModulus : limbs.length < wordModulus := by
        simp [target] at endWithin extent
        omega
      simpa [wordModulus] using belowWordModulus
    have limbCount :
        uint32Field "natural limb count" limbs.length =
          .ok (UInt32.ofNat limbs.length) := by
      simp [uint32Field, limbCountFits]
    obtain ⟨middle, address, objectAllocation⟩ :=
      state.allocateObject_eq_ok_of_capacity .natural
        (target.semanticSlotBytes * limbs.length) false bigNaturalMarker
        (UInt32.ofNat limbs.length) 0 0 valid.cursorAligned
        (budget.allocationCapacity (by
          simpa only [align8_align8] using allocationFits))
    have middleValid := valid.allocateObject objectAllocation
    have middleExtent := MemoryState.allocateObject_extent objectAllocation
    have payloadInBounds :
        address.value + headerBytes +
            target.semanticSlotBytes * (0 + limbs.length) ≤
          middle.memory.size := by
      have payloadEnd :
          address.value + headerBytes +
              target.semanticSlotBytes * (0 + limbs.length) ≤
            middle.heapCursor := by
        simp only [Nat.zero_add]
        rw [middleExtent]
        have extent :=
          align8_ge (headerBytes + target.semanticSlotBytes * limbs.length)
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left extent address.value
      exact Nat.le_trans payloadEnd middleValid.cursorInBounds
    obtain ⟨memory, payloadWrite, _⟩ :=
      writeNaturalLimbs_spec middle.memory address.value 0 limbs
        payloadInBounds
    let result : MemoryState := { middle with memory }
    have allocated :
        allocateNatural state value = .ok (result, address) := by
      unfold allocateNatural
      rw [if_neg sourceTagged]
      dsimp only
      change
        (do
          let limbCount ← uint32Field "natural limb count" limbs.length
          let (state, address) ← liftMemory <|
            state.allocateObject .natural
              (target.semanticSlotBytes * limbs.length) false
              bigNaturalMarker limbCount
          let memory ← liftMemory <|
            Fir.Wasm.Concrete.writeNaturalLimbs
              state.memory address.value 0 limbs
          return ({ state with memory }, address)) =
          .ok (result, address)
      rw [limbCount]
      simp only [Bind.bind, Except.bind]
      rw [objectAllocation]
      simp only [liftMemory]
      rw [payloadWrite]
      rfl
    have middleBudget :=
      budget.allocateObject valid.cursorAligned allocationFits objectAllocation
    have resultBudget :
        result.AddressSpaceBudget
          (remainingBytes -
            align8
              (headerBytes + target.semanticSlotBytes * limbs.length)) := {
      cursorPositive := middleBudget.cursorPositive
      endWithinAddressSpace := middleBudget.endWithinAddressSpace }
    exact ⟨result, address, allocated, by
      simpa [naturalAllocationBytes, sourceTagged, limbs] using resultBudget⟩

/-- A successful heap-backed natural literal is one checked object allocation
followed by the canonical limb writer. -/
theorem allocateNatural_heap_decompose
    (state result : MemoryState) (value : Nat) (address : Word32)
    (large : maxTaggedPayload < value)
    (allocated : allocateNatural state value = .ok (result, address)) :
    let limbs := naturalLimbs value
    ∃ limbCount middle,
      uint32Field "natural limb count" limbs.length = .ok limbCount ∧
      state.allocateObject .natural
        (target.semanticSlotBytes * limbs.length) false bigNaturalMarker limbCount =
          .ok (middle, address) ∧
      writeNaturalLimbs middle.memory address.value 0 limbs =
        .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  dsimp only
  unfold allocateNatural at allocated
  rw [if_neg (Nat.not_le.mpr large)] at allocated
  dsimp only at allocated
  cases countResult : uint32Field "natural limb count" (naturalLimbs value).length with
  | error failure =>
      rw [countResult] at allocated
      contradiction
  | ok limbCount =>
      rw [countResult] at allocated
      simp only [Bind.bind, Except.bind] at allocated
      cases objectAllocation : state.allocateObject .natural
          (target.semanticSlotBytes * (naturalLimbs value).length) false
          bigNaturalMarker limbCount with
      | error failure =>
          rw [objectAllocation] at allocated
          change Except.error (ConcreteError.ofMemory failure) =
            Except.ok (result, address) at allocated
          contradiction
      | ok pair =>
          rcases pair with ⟨middle, actualAddress⟩
          rw [objectAllocation] at allocated
          change (do
            let memory ← liftMemory <|
              writeNaturalLimbs middle.memory actualAddress.value 0
                (naturalLimbs value)
            return ({ middle with memory }, actualAddress)) =
              .ok (result, address) at allocated
          cases limbWrite : writeNaturalLimbs middle.memory actualAddress.value 0
              (naturalLimbs value) with
          | error failure =>
              rw [limbWrite] at allocated
              change Except.error (ConcreteError.ofMemory failure) =
                Except.ok (result, address) at allocated
              contradiction
          | ok finalMemory =>
              rw [limbWrite] at allocated
              change Except.ok ({ middle with memory := finalMemory }, actualAddress) =
                Except.ok (result, address) at allocated
              have pairEq : ({ middle with memory := finalMemory }, actualAddress) =
                  (result, address) := Except.ok.inj allocated
              have resultEq : { middle with memory := finalMemory } = result :=
                congrArg Prod.fst pairEq
              have addressEq : actualAddress = address := congrArg Prod.snd pairEq
              subst result
              subst address
              exact ⟨limbCount, middle, rfl, objectAllocation,
                limbWrite, rfl⟩

/-- Heap-backed natural allocation preserves every byte owned by the old
concrete heap. -/
theorem allocateNatural_heap_prefixExtension
    (state result : MemoryState) (value : Nat) (address : Word32)
    (valid : state.FrontierInvariant)
    (large : maxTaggedPayload < value)
    (allocated : allocateNatural state value = .ok (result, address)) :
    state.PrefixExtension result := by
  obtain ⟨limbCount, middle, _, objectAllocation, limbWrite, cursorEq⟩ :=
    allocateNatural_heap_decompose state result value address large allocated
  have objectExtension := valid.allocateObject_prefixExtension objectAllocation
  have freshAddress := valid.allocateObject_address objectAllocation
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadEnd : address.value + headerBytes +
      target.semanticSlotBytes * (0 + (naturalLimbs value).length) ≤
        middle.heapCursor := by
    simp only [Nat.zero_add]
    rw [middleExtent]
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (naturalLimbs value).length)
    simpa [Nat.add_assoc] using Nat.add_le_add_left aligned address.value
  have payloadPost := writeNaturalLimbs_post middle.memory result.memory
    address.value 0 (naturalLimbs value)
    (Nat.le_trans payloadEnd middleValid.cursorInBounds) limbWrite
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
        simp [target]
        omega))
    _ = state.memory.readByte byte := objectExtension.readByte byte beforeCursor

/-- Fully decoded shape of a fresh heap-backed natural. -/
structure NaturalObjectRel (state : MemoryState) (address : Word32)
    (value : Nat) (header : Header) : Prop where
  headerRead : state.readLiveHeader address = .ok header
  headerKind : header.kind = .natural
  ordinary : header.persistent = false
  marker : header.aux0 = bigNaturalMarker
  extent : address.value + header.allocationBytes.toNat ≤ state.heapCursor
  limbsFit : headerBytes + target.semanticSlotBytes * header.aux1.toNat ≤
    header.allocationBytes.toNat
  decoded : readNatural state address = .ok value
  refCountOne : header.refCount.toNat = 1

/-- A successful large-natural allocation establishes the exact checked
object decoder and preserves the allocator frontier invariant. -/
theorem allocateNatural_heap_objectRel
    (state result : MemoryState) (value : Nat) (address : Word32)
    (valid : state.FrontierInvariant)
    (large : maxTaggedPayload < value)
    (allocated : allocateNatural state value = .ok (result, address)) :
    result.FrontierInvariant ∧
      ∃ header, NaturalObjectRel result address value header := by
  obtain ⟨limbCount, middle, countEncoded, objectAllocation, limbWrite,
      cursorEq⟩ :=
    allocateNatural_heap_decompose state result value address large allocated
  obtain ⟨countFits, countEq⟩ := uint32Field_success
    "natural limb count" (naturalLimbs value).length limbCount countEncoded
  have countToNat : limbCount.toNat = (naturalLimbs value).length := by
    rw [countEq]
    exact UInt32.toNat_ofNat_of_lt' countFits
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadEnd : address.value + headerBytes +
      target.semanticSlotBytes * (0 + (naturalLimbs value).length) ≤
        middle.heapCursor := by
    simp only [Nat.zero_add]
    rw [middleExtent]
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (naturalLimbs value).length)
    simpa [Nat.add_assoc] using Nat.add_le_add_left aligned address.value
  have payloadInBounds : address.value + headerBytes +
      target.semanticSlotBytes * (0 + (naturalLimbs value).length) ≤
        middle.memory.size := Nat.le_trans payloadEnd middleValid.cursorInBounds
  have payloadPost := writeNaturalLimbs_post middle.memory result.memory
    address.value 0 (naturalLimbs value) payloadInBounds limbWrite
  have stateEq : ({ middle with memory := result.memory } : MemoryState) = result := by
    cases middle
    cases result
    simp_all
  have finalValid : result.FrontierInvariant := by
    rw [← stateEq]
    exact middleValid.writeNaturalLimbs payloadEnd limbWrite
  let allocationBytes := align8
    (headerBytes + target.semanticSlotBytes * (naturalLimbs value).length)
  let header := Header.forAllocation .natural allocationBytes false
    bigNaturalMarker limbCount
  have headerBefore : middle.readLiveHeader address = .ok header := by
    simpa [header, allocationBytes] using
      MemoryState.readLiveHeader_of_allocateObject_eq_ok state middle .natural
        (target.semanticSlotBytes * (naturalLimbs value).length) false
        bigNaturalMarker limbCount 0 0 address objectAllocation
  have headerFrame := middle.readLiveHeader_of_writeNaturalLimbs result.memory
    address (naturalLimbs value) payloadPost
  have headerRead : result.readLiveHeader address = .ok header := by
    rw [← stateEq, headerFrame]
    exact headerBefore
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state middle .natural
      (target.semanticSlotBytes * (naturalLimbs value).length) false
      bigNaturalMarker limbCount 0 0 address objectAllocation
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
  have addressHeap : address.classify = .heap := by
    have checked := headerRead
    unfold MemoryState.readLiveHeader at checked
    split at checked
    next heap => exact heap
    next => contradiction
  have decodedLimbs := readNaturalLimbs_of_write_eq_ok middle.memory result.memory
    address.value 0 (naturalLimbs value) payloadInBounds limbWrite
  have decoded : readNatural result address = .ok value := by
    unfold readNatural
    simp only [addressHeap, ↓reduceIte, Bind.bind, Except.bind]
    rw [headerRead]
    simp only [liftMemory]
    have accepted : header.kind == ObjectKind.natural &&
        header.aux0 == bigNaturalMarker := by
      simp [header, Header.forAllocation]
      change (ObjectKind.natural == ObjectKind.natural) = true
      decide
    rw [accepted]
    simp only [↓reduceIte]
    change liftMemory (readNaturalLimbs result.memory address.value 0
      header.aux1.toNat) = .ok value
    rw [show header.aux1.toNat = (naturalLimbs value).length by
      simp [header, Header.forAllocation, countToNat]]
    rw [decodedLimbs]
    simp [liftMemory, naturalLimbs_value]
  refine ⟨finalValid, header, {
    headerRead
    headerKind := rfl
    ordinary := rfl
    marker := rfl
    extent := ?_
    limbsFit := ?_
    decoded
    refCountOne := rfl }⟩
  · simpa [header, Header.forAllocation, allocationToNat] using resultExtent
  · have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (naturalLimbs value).length)
    simpa [header, Header.forAllocation, allocationBytes, allocationToNat,
      countToNat] using aligned

def semanticNaturalCell (value : Nat) : HeapCell := {
  object := .natural value }

def semanticNaturalResult (runtime : RuntimeState) (value : Nat) : RuntimeState := {
  runtime with
  heap := (runtime.nextLocation, semanticNaturalCell value) :: runtime.heap
  nextLocation := runtime.nextLocation + 1 }

theorem semanticLiteral_natural_heap_eq (runtime : RuntimeState) (value : Nat)
    (large : maxTaggedPayload < value) :
    literal runtime (.nat value) =
      (semanticNaturalResult runtime value,
        .object (.heap runtime.nextLocation)) := by
  simp only [literal]
  rw [if_neg (Nat.not_le.mpr large)]
  simp [alloc, semanticNaturalResult, semanticNaturalCell]

/-- Heap-backed natural literal allocation extends the complete live-heap
relation and relates its wasm32 address to the fresh semantic natural. -/
theorem allocateNatural_heap_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (value : Nat) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (large : maxTaggedPayload < value)
    (allocated : allocateNatural state value = .ok (result, address)) :
    let nextWitness := witness.bindNatural runtime.nextLocation address value
    LiveHeapRel result nextWitness (semanticNaturalResult runtime value) ∧
      ValueRel nextWitness .tobject (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨_, _, _, objectAllocation, _, _⟩ :=
    allocateNatural_heap_decompose state result value address large allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have extension := allocateNatural_heap_prefixExtension state result value address
    related.frontier large allocated
  obtain ⟨finalFrontier, header, objectRelated⟩ :=
    allocateNatural_heap_objectRel state result value address related.frontier
      large allocated
  have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
    cases found : witness.locations.lookup? runtime.nextLocation with
    | none => rfl
    | some oldAddress =>
        exfalso
        obtain ⟨cell, semanticFound, _⟩ :=
          related.concreteToSemantic runtime.nextLocation oldAddress found
        have beforeNext :=
          related.locationsBeforeNext runtime.nextLocation cell semanticFound
        exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    omega
  have witnessExtension := witness.bindNatural_extends runtime.nextLocation address
    value locationFresh descriptorFresh
  have locationAddressFresh : ∀ old oldAddress,
      witness.locations.lookup? old = some oldAddress → oldAddress ≠ address := by
    intro old oldAddress found equal
    obtain ⟨cell, _, cellRelated⟩ :=
      related.concreteToSemantic old oldAddress found
    have owned := cellRelated.headerOwned
    subst oldAddress
    simp [headerBytes] at owned
    omega
  have promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.Contains payload oldAddress → address ≠ oldAddress := by
    intro payload oldAddress found equal
    have promoted := related.promoted payload oldAddress found
    obtain ⟨oldHeader, _, _, _, _, _, extent, payloadFits⟩ := promoted.header
    subst oldAddress
    simp [headerBytes] at payloadFits extent
    omega
  obtain ⟨addressHeap, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address header
      objectRelated.headerRead
  have headerOwned : address.value + headerBytes ≤ result.heapCursor :=
    Nat.le_trans (Nat.add_le_add_left headerMinimum address.value)
      objectRelated.extent
  have witnessWellFormed := related.witnessWellFormed.bindNatural
    runtime.nextLocation address value addressHeap locationAddressFresh
      promotedAddressFresh
  have newRegion : ∃ newHeader,
      Header.read result.memory address = .ok newHeader ∧
      headerBytes ≤ newHeader.allocationBytes.toNat ∧
      newHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + newHeader.allocationBytes.toNat ≤ result.heapCursor :=
    ⟨header, rawHeaderRead, headerMinimum, headerAligned, objectRelated.extent⟩
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial extension address freshAddress
      (fun other different =>
        witness.lookup_bindNatural_descriptor_other runtime.nextLocation address
          other value different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindNatural runtime.nextLocation address value) address
      (semanticNaturalCell value) := by
    apply LiveCellRel.natural
      (RefinementWitness.lookup_bindNatural_descriptor witness runtime.nextLocation
        address value)
      (by rfl) objectRelated.headerRead objectRelated.headerKind
        objectRelated.marker objectRelated.extent
        objectRelated.limbsFit objectRelated.decoded
    · simpa [semanticNaturalCell] using objectRelated.refCountOne
    · simpa [semanticNaturalCell] using objectRelated.ordinary
    · rfl
  refine ⟨?_, ValueRel.new_natural_result witness runtime.nextLocation address value⟩
  refine {
    frontier := finalFrontier
    witnessWellFormed
    locationsBeforeNext := ?_
    releaseFuelBound := ?_
    descriptorsOwned := ?_
    descriptorRegion
    descriptorDisjoint
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      change runtime.nextLocation < runtime.nextLocation + 1
      exact Nat.lt_succ_self runtime.nextLocation
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticNaturalResult, findCell?, isNew, Ne.symm isNew] using found
      have oldBefore := related.locationsBeforeNext location cell oldFound
      exact Nat.lt_trans oldBefore (Nat.lt_succ_self runtime.nextLocation)
  · have cursorGrowth : state.heapCursor + headerBytes ≤ result.heapCursor := by
      rw [← freshAddress]
      exact headerOwned
    have oldFuel := related.releaseFuelBound
    simp [semanticNaturalResult, headerBytes] at oldFuel cursorGrowth ⊢
    omega
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact headerOwned
    · rw [witness.lookup_bindNatural_descriptor_other runtime.nextLocation address
        other value isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticNaturalCell value := by
        simpa [semanticNaturalResult, findCell?] using found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindNatural_location witness runtime.nextLocation
          address value,
        .live newCellRelated⟩
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticNaturalResult, findCell?, isNew, Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindNatural, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticNaturalCell value,
        by simp [semanticNaturalResult, findCell?], .live newCellRelated⟩
    · rw [witness.lookup_bindNatural_location_other runtime.nextLocation location
        address value isNew] at mapped
      obtain ⟨cell, oldFound, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticNaturalResult, findCell?, isNew, Ne.symm isNew],
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro payload concreteAddress mapped
    exact ((related.promoted payload concreteAddress mapped).prefixExtension extension)
      |>.witnessExtension witnessExtension

end Fir.Wasm.Concrete
