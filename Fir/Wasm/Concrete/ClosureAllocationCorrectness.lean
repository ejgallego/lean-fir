import Fir.Wasm.Concrete.ClosureCorrectness
import Fir.Wasm.Concrete.ConstructorAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Exact result of installing one typed closure capture. -/
structure WriteClosureCapturePost (before after : LinearMemory)
    (address : Nat) (kind : AbiKind) (value : LaneValue) : Prop where
  size : after.size = before.size
  read : after.readClosureCapture address kind = .ok value
  byteFrame : ∀ other, other < address ∨ address + 7 < other →
    after.readByte other = before.readByte other

theorem LinearMemory.writeClosureCapture_spec (memory : LinearMemory)
    (address : Nat) (kind : AbiKind) (value : LaneValue)
    (typed : value.valueType = kind.valueType)
    (inBounds : address + 7 < memory.size) :
    ∃ result,
      memory.writeClosureCapture address kind value = .ok result ∧
      WriteClosureCapturePost memory result address kind value := by
  cases value with
  | word32 word =>
      have kindType : kind.valueType = .i32 := by
        simpa [LaneValue.valueType] using typed.symm
      obtain ⟨low, lowWrite, lowSize, _, _, _, _, lowFrame⟩ :=
        LinearMemory.writeUInt32_spec memory address (UInt32.ofNat word.value)
          (by omega)
      obtain ⟨result, paddingWrite, paddingSize, _, _, _, _, paddingFrame⟩ :=
        LinearMemory.writeUInt32_spec low (address + 4) 0 (by omega)
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · simp only [LinearMemory.writeClosureCapture, kindType]
        unfold LinearMemory.writeWord32
        rw [lowWrite]
        exact paddingWrite
      · exact paddingSize.trans lowSize
      · have lowRead : result.readWord32 address = .ok word := by
          unfold LinearMemory.readWord32
          rw [LinearMemory.readUInt32_of_writeUInt32_eq_ok_other low result
            (address + 4) address 0 (by omega) paddingWrite (by omega)]
          exact LinearMemory.readWord32_of_writeWord32_eq_ok memory low address word
            (by omega) lowWrite
        have paddingRead : result.readUInt32 (address + 4) = .ok 0 :=
          LinearMemory.readUInt32_of_writeUInt32_eq_ok low result (address + 4) 0
            (by omega) paddingWrite
        unfold LinearMemory.readClosureCapture
        rw [kindType, lowRead, paddingRead]
        rfl
      · intro other separated
        calc
          result.readByte other = low.readByte other :=
            paddingFrame other (by omega) (by omega) (by omega) (by omega)
          _ = memory.readByte other :=
            lowFrame other (by omega) (by omega) (by omega) (by omega)
  | word64 word =>
      have kindType : kind.valueType = .i64 := by
        simpa [LaneValue.valueType] using typed.symm
      obtain ⟨middle, lowWrite, _, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec memory address word.toUInt32 (by omega)
      obtain ⟨result, highWrite, _, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec middle (address + 4)
          (word >>> (32 : UInt64)).toUInt32 (by omega)
      have written : memory.writeUInt64 address word = .ok result := by
        unfold LinearMemory.writeUInt64
        rw [lowWrite]
        exact highWrite
      have size := LinearMemory.size_of_writeUInt64_eq_ok memory result address word
        inBounds written
      have read := LinearMemory.readUInt64_of_writeUInt64_eq_ok memory result address
        word inBounds written
      refine ⟨result, ?_, size, ?_, ?_⟩
      · simpa [LinearMemory.writeClosureCapture, kindType] using written
      · unfold LinearMemory.readClosureCapture
        simp only [kindType, Bind.bind, Except.bind]
        rw [read]
        rfl
      · intro other separated
        exact LinearMemory.readByte_of_writeUInt64_eq_ok_other memory result address
          word inBounds written other separated
  | float32Bits bits =>
      have kindType : kind.valueType = .f32 := by
        simpa [LaneValue.valueType] using typed.symm
      obtain ⟨low, lowWrite, lowSize, _, _, _, _, lowFrame⟩ :=
        LinearMemory.writeUInt32_spec memory address bits (by omega)
      obtain ⟨result, paddingWrite, paddingSize, _, _, _, _, paddingFrame⟩ :=
        LinearMemory.writeUInt32_spec low (address + 4) 0 (by omega)
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · simp only [LinearMemory.writeClosureCapture, kindType]
        rw [lowWrite]
        exact paddingWrite
      · exact paddingSize.trans lowSize
      · have lowRead : result.readUInt32 address = .ok bits := by
          rw [LinearMemory.readUInt32_of_writeUInt32_eq_ok_other low result
            (address + 4) address 0 (by omega) paddingWrite (by omega)]
          exact LinearMemory.readUInt32_of_writeUInt32_eq_ok memory low address bits
            (by omega) lowWrite
        have paddingRead : result.readUInt32 (address + 4) = .ok 0 :=
          LinearMemory.readUInt32_of_writeUInt32_eq_ok low result (address + 4) 0
            (by omega) paddingWrite
        unfold LinearMemory.readClosureCapture
        rw [kindType, lowRead, paddingRead]
        rfl
      · intro other separated
        calc
          result.readByte other = low.readByte other :=
            paddingFrame other (by omega) (by omega) (by omega) (by omega)
          _ = memory.readByte other :=
            lowFrame other (by omega) (by omega) (by omega) (by omega)
  | float64Bits bits =>
      have kindType : kind.valueType = .f64 := by
        simpa [LaneValue.valueType] using typed.symm
      obtain ⟨middle, lowWrite, _, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec memory address bits.toUInt32 (by omega)
      obtain ⟨result, highWrite, _, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec middle (address + 4)
          (bits >>> (32 : UInt64)).toUInt32 (by omega)
      have written : memory.writeUInt64 address bits = .ok result := by
        unfold LinearMemory.writeUInt64
        rw [lowWrite]
        exact highWrite
      have size := LinearMemory.size_of_writeUInt64_eq_ok memory result address bits
        inBounds written
      have read := LinearMemory.readUInt64_of_writeUInt64_eq_ok memory result address
        bits inBounds written
      refine ⟨result, ?_, size, ?_, ?_⟩
      · simpa [LinearMemory.writeClosureCapture, kindType] using written
      · unfold LinearMemory.readClosureCapture
        simp only [kindType, Bind.bind, Except.bind]
        rw [read]
        rfl
      · intro other separated
        exact LinearMemory.readByte_of_writeUInt64_eq_ok_other memory result address
          bits inBounds written other separated

/-- An eight-byte capture decoder depends only on the bytes in its slot. -/
theorem LinearMemory.readClosureCapture_of_byteFrame
    (before after : LinearMemory) (address : Nat) (kind : AbiKind)
    (frame : ∀ offset, offset < 8 →
      after.readByte (address + offset) = before.readByte (address + offset)) :
    after.readClosureCapture address kind = before.readClosureCapture address kind := by
  have readUInt32 (start : Nat) (offset : Nat)
      (startEq : start = address + offset) (within : offset + 3 < 8) :
      after.readUInt32 start = before.readUInt32 start := by
    subst start
    unfold LinearMemory.readUInt32
    rw [frame offset (by omega)]
    rw [show after.readByte (address + offset + 1) =
        before.readByte (address + offset + 1) by
      simpa only [Nat.add_assoc] using frame (offset + 1) (by omega)]
    rw [show after.readByte (address + offset + 2) =
        before.readByte (address + offset + 2) by
      simpa only [Nat.add_assoc] using frame (offset + 2) (by omega)]
    rw [show after.readByte (address + offset + 3) =
        before.readByte (address + offset + 3) by
      simpa only [Nat.add_assoc] using frame (offset + 3) (by omega)]
  have low : after.readUInt32 address = before.readUInt32 address :=
    readUInt32 address 0 (by omega) (by omega)
  have high : after.readUInt32 (address + 4) = before.readUInt32 (address + 4) :=
    readUInt32 (address + 4) 4 rfl (by omega)
  have word : after.readWord32 address = before.readWord32 address := by
    unfold LinearMemory.readWord32
    rw [low]
  have wide : after.readUInt64 address = before.readUInt64 address := by
    unfold LinearMemory.readUInt64
    rw [low, high]
  unfold LinearMemory.readClosureCapture
  cases kind.valueType <;> simp only [Bind.bind, Except.bind]
  · rw [word, high]
  · rw [wide]
  · rw [low, high]
  · rw [wide]

/-- Exact postcondition for the heterogeneous closure-capture writer. -/
structure WriteClosureCapturesPost (before after : LinearMemory)
    (base index : Nat) (captures : List (AbiKind × LaneValue)) : Prop where
  size : after.size = before.size
  captureAt : ∀ offset kind value,
    captures[offset]? = some (kind, value) →
    after.readClosureCapture (closureCaptureAddress base (index + offset)) kind =
      .ok value
  byteFrame : ∀ other,
    other < closureCaptureAddress base index ∨
      closureCaptureAddress base (index + captures.length) ≤ other →
    after.readByte other = before.readByte other

theorem LinearMemory.writeClosureCaptures_spec (memory : LinearMemory)
    (base index : Nat) (captures : List (AbiKind × LaneValue))
    (typed : ∀ (offset : Nat) (kind : AbiKind) (value : LaneValue),
      captures[offset]? = some (kind, value) →
      value.valueType = kind.valueType)
    (inBounds : closureCaptureAddress base (index + captures.length) ≤
      memory.size) :
    ∃ result,
      memory.writeClosureCaptures base index captures = .ok result ∧
      WriteClosureCapturesPost memory result base index captures := by
  induction captures generalizing memory index with
  | nil =>
      refine ⟨memory, rfl, rfl, ?_, ?_⟩
      · intro offset kind value atOffset
        simp at atOffset
      · intro other _
        rfl
  | cons capture rest ih =>
      rcases capture with ⟨kind, value⟩
      let slot := closureCaptureAddress base index
      have currentTyped : value.valueType = kind.valueType :=
        typed 0 kind value (by simp)
      have slotInBounds : slot + 7 < memory.size := by
        simp only [List.length_cons] at inBounds
        simp [slot, closureCaptureAddress, target] at inBounds ⊢
        omega
      obtain ⟨slotMemory, slotWrite, slotPost⟩ :=
        memory.writeClosureCapture_spec slot kind value currentTyped slotInBounds
      have tailTyped : ∀ (offset : Nat) (tailKind : AbiKind)
          (tailValue : LaneValue),
          rest[offset]? = some (tailKind, tailValue) →
          tailValue.valueType = tailKind.valueType := by
        intro offset tailKind tailValue atOffset
        exact typed (offset + 1) tailKind tailValue (by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using atOffset)
      have tailInBounds :
          closureCaptureAddress base (index + 1 + rest.length) ≤
            slotMemory.size := by
        rw [slotPost.size]
        simp only [List.length_cons] at inBounds
        simp [closureCaptureAddress, target] at inBounds ⊢
        omega
      obtain ⟨result, tailWrite, tailPost⟩ :=
        ih slotMemory (index + 1) tailTyped tailInBounds
      refine ⟨result, ?_, ?_⟩
      · unfold LinearMemory.writeClosureCaptures
        rw [slotWrite]
        exact tailWrite
      · refine ⟨tailPost.size.trans slotPost.size, ?_, ?_⟩
        · intro offset itemKind itemValue atOffset
          cases offset with
          | zero =>
              simp at atOffset
              rcases atOffset with ⟨rfl, rfl⟩
              calc
                result.readClosureCapture
                    (closureCaptureAddress base (index + 0)) kind =
                    slotMemory.readClosureCapture slot kind := by
                  apply LinearMemory.readClosureCapture_of_byteFrame
                  intro byte byteLt
                  apply tailPost.byteFrame
                  left
                  simp [closureCaptureAddress, target]
                  omega
                _ = .ok value := slotPost.read
          | succ offset =>
              have restAt : rest[offset]? = some (itemKind, itemValue) := by
                simpa using atOffset
              have read := tailPost.captureAt offset itemKind itemValue restAt
              simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using read
        · intro other separated
          simp only [List.length_cons] at separated
          have tailSeparated :
              other < closureCaptureAddress base (index + 1) ∨
                closureCaptureAddress base (index + 1 + rest.length) ≤ other := by
            simp [closureCaptureAddress, target] at separated ⊢
            omega
          have slotSeparated : other < slot ∨ slot + 7 < other := by
            simp [slot, closureCaptureAddress, target] at separated ⊢
            omega
          calc
            result.readByte other = slotMemory.readByte other :=
              tailPost.byteFrame other tailSeparated
            _ = memory.readByte other := slotPost.byteFrame other slotSeparated

theorem LinearMemory.writeClosureCaptures_post (memory result : LinearMemory)
    (base index : Nat) (captures : List (AbiKind × LaneValue))
    (typed : ∀ (offset : Nat) (kind : AbiKind) (value : LaneValue),
      captures[offset]? = some (kind, value) →
      value.valueType = kind.valueType)
    (inBounds : closureCaptureAddress base (index + captures.length) ≤
      memory.size)
    (written : memory.writeClosureCaptures base index captures = .ok result) :
    WriteClosureCapturesPost memory result base index captures := by
  obtain ⟨actual, actualWrite, post⟩ :=
    memory.writeClosureCaptures_spec base index captures typed inBounds
  rw [actualWrite] at written
  cases written
  exact post

theorem WriteClosureCapturesPost.readUInt32_prefix
    {before after : LinearMemory} {base index : Nat}
    {captures : List (AbiKind × LaneValue)}
    (post : WriteClosureCapturesPost before after base index captures)
    (address : Nat)
    (beforeCaptures : address + 4 ≤ closureCaptureAddress base index) :
    after.readUInt32 address = before.readUInt32 address := by
  unfold LinearMemory.readUInt32
  rw [post.byteFrame address (.inl (by omega))]
  rw [post.byteFrame (address + 1) (.inl (by omega))]
  rw [post.byteFrame (address + 2) (.inl (by omega))]
  rw [post.byteFrame (address + 3) (.inl (by omega))]

/-- Capture installation starts after the common header. -/
theorem Header.read_of_writeClosureCaptures
    (before after : LinearMemory) (address : Word32)
    (captures : List (AbiKind × LaneValue))
    (post : WriteClosureCapturesPost before after address.value 0 captures) :
    Header.read after address = Header.read before address := by
  have frame (offset : Nat) (withinHeader : offset + 4 ≤ headerBytes) :
      after.readUInt32 (address.value + offset) =
        before.readUInt32 (address.value + offset) := by
    apply post.readUInt32_prefix
    simp [closureCaptureAddress, target]
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

theorem MemoryState.readLiveHeader_of_writeClosureCaptures
    (state : MemoryState) (memory : LinearMemory) (address : Word32)
    (captures : List (AbiKind × LaneValue))
    (post : WriteClosureCapturesPost state.memory memory address.value 0 captures) :
    ({ state with memory } : MemoryState).readLiveHeader address =
      state.readLiveHeader address := by
  have headerFrame :=
    Header.read_of_writeClosureCaptures state.memory memory address captures post
  unfold MemoryState.readLiveHeader
  dsimp only
  rw [headerFrame, post.size]

/-- A successful closure allocation is exactly the checked common-object
allocation followed by the heterogeneous capture writer. -/
theorem allocateClosure_decompose
    (state result : MemoryState) (dispatch : ClosureDispatchTable)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (captures : Array LaneValue) (address : Word32) (targetId : UInt32)
    (count : captureKinds.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.size < UInt32.size)
    (allocated : allocateClosure state dispatch function arity captureKinds captures =
      .ok (result, address)) :
    ∃ middle,
      state.allocateObject .closure
        ((ClosureLayout.ofCaptures captureKinds).allocationBytes - headerBytes)
        false targetId (UInt32.ofNat arity) (UInt32.ofNat captures.size) 0 =
          .ok (middle, address) ∧
      middle.memory.writeClosureCaptures address.value 0
        (captureKinds.toList.zip captures.toList) = .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  unfold allocateClosure at allocated
  simp [count, capturesLtArity, targetIdEq, uint32Field, arityFits, fixedFits] at allocated
  change (do
    let (middle, actualAddress) ← liftMemory <|
      state.allocateObject .closure
        ((ClosureLayout.ofCaptures captureKinds).allocationBytes - headerBytes)
        false targetId (UInt32.ofNat arity) (UInt32.ofNat captures.size) 0
    let memory ← liftMemory <| middle.memory.writeClosureCaptures
      actualAddress.value 0 (captureKinds.toList.zip captures.toList)
    return ({ middle with memory }, actualAddress)) =
      .ok (result, address) at allocated
  cases objectAllocation : state.allocateObject .closure
      ((ClosureLayout.ofCaptures captureKinds).allocationBytes - headerBytes)
      false targetId (UInt32.ofNat arity) (UInt32.ofNat captures.size) 0 with
  | error failure =>
      rw [objectAllocation] at allocated
      change Except.error (ConcreteError.target failure) =
        Except.ok (result, address) at allocated
      contradiction
  | ok pair =>
      rcases pair with ⟨middle, actualAddress⟩
      rw [objectAllocation] at allocated
      change (do
        let memory ← liftMemory <| middle.memory.writeClosureCaptures
          actualAddress.value 0 (captureKinds.toList.zip captures.toList)
        return ({ middle with memory }, actualAddress)) =
          .ok (result, address) at allocated
      cases captureWrite : middle.memory.writeClosureCaptures
          actualAddress.value 0 (captureKinds.toList.zip captures.toList) with
      | error failure =>
          rw [captureWrite] at allocated
          change Except.error (ConcreteError.target failure) =
            Except.ok (result, address) at allocated
          contradiction
      | ok finalMemory =>
          rw [captureWrite] at allocated
          change Except.ok ({ middle with memory := finalMemory }, actualAddress) =
            Except.ok (result, address) at allocated
          have pairEq : ({ middle with memory := finalMemory }, actualAddress) =
              (result, address) := Except.ok.inj allocated
          have resultEq : { middle with memory := finalMemory } = result :=
            congrArg Prod.fst pairEq
          have addressEq : actualAddress = address := congrArg Prod.snd pairEq
          subst result
          subst address
          exact ⟨middle, rfl, captureWrite, rfl⟩

private theorem List.lookup_zip
    {left : List α} {right : List β} {index : Nat} {a : α} {b : β}
    (atIndex : (left.zip right)[index]? = some (a, b)) :
    left[index]? = some a ∧ right[index]? = some b := by
  induction index generalizing left right with
  | zero =>
      cases left <;> cases right <;> simp_all
  | succ index ih =>
      cases left with
      | nil => simp_all
      | cons leftHead leftTail =>
          cases right with
          | nil => simp_all
          | cons rightHead rightTail =>
              exact ih atIndex

private theorem List.lookup_zip_of
    {left : List α} {right : List β} {index : Nat} {a : α} {b : β}
    (leftAt : left[index]? = some a) (rightAt : right[index]? = some b) :
    (left.zip right)[index]? = some (a, b) := by
  induction index generalizing left right with
  | zero =>
      cases left <;> cases right <;> simp_all
  | succ index ih =>
      cases left with
      | nil => simp_all
      | cons leftHead leftTail =>
          cases right with
          | nil => simp_all
          | cons rightHead rightTail =>
              exact ih leftAt rightAt

theorem Array.lookup_zip_toList
    {kinds : Array AbiKind} {values : Array LaneValue}
    {index : Nat} {kind : AbiKind} {value : LaneValue}
    (atIndex : (kinds.toList.zip values.toList)[index]? = some (kind, value)) :
    kinds[index]? = some kind ∧ values[index]? = some value := by
  obtain ⟨kindAt, valueAt⟩ := List.lookup_zip atIndex
  exact ⟨by simpa using kindAt, by simpa using valueAt⟩

theorem Array.lookup_zip_toList_of
    {kinds : Array AbiKind} {values : Array LaneValue}
    {index : Nat} {kind : AbiKind} {value : LaneValue}
    (kindAt : kinds[index]? = some kind) (valueAt : values[index]? = some value) :
    (kinds.toList.zip values.toList)[index]? = some (kind, value) := by
  apply List.lookup_zip_of
  · simpa using kindAt
  · simpa using valueAt

/-- Successful concrete closure allocation installs validated dispatch
metadata and every typed capture slot under the fresh closure witness. -/
theorem allocateClosure_objectRel
    (state result : MemoryState) (witness : RefinementWitness)
    (dispatch : ClosureDispatchTable) (function : Lean.Name) (arity : Nat)
    (captureKinds : Array AbiKind) (captures : Array LaneValue)
    (semantic : Array Value) (location : Location) (address : Word32)
    (targetId : UInt32)
    (valid : state.FrontierInvariant)
    (count : captureKinds.size = captures.size)
    (semanticCount : semantic.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (targetLookup : dispatch.lookup? targetId = some function)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.size < UInt32.size)
    (captureRelated : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue)
        (value : Value),
      captureKinds[index]? = some kind →
      captures[index]? = some lane →
      semantic[index]? = some value →
      ValueRel witness kind lane value)
    (locationFresh : witness.locations.lookup? location = none)
    (descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value)
    (allocated : allocateClosure state dispatch function arity captureKinds captures =
      .ok (result, address)) :
    result.FrontierInvariant ∧
    ClosureObjectRel result
      (witness.bindClosure location address function arity captureKinds)
      dispatch address function arity captureKinds semantic := by
  let layout := ClosureLayout.ofCaptures captureKinds
  let captureList := captureKinds.toList.zip captures.toList
  have layoutMinimum : headerBytes ≤ layout.allocationBytes := by
    dsimp only [layout]
    simp only [ClosureLayout.ofCaptures]
    exact Nat.le_trans (by omega) (align8_ge _)
  have layoutAligned : align8 layout.allocationBytes = layout.allocationBytes := by
    apply align8_eq_of_mod_eq_zero
    have aligned := ClosureLayout.ofCaptures_aligned captureKinds
    simpa only [layout, target] using aligned
  have allocationEq :
      align8 (headerBytes + (layout.allocationBytes - headerBytes)) =
        layout.allocationBytes := by
    rw [Nat.add_sub_of_le layoutMinimum, layoutAligned]
  have layoutExact :
      layout.allocationBytes = headerBytes + target.semanticSlotBytes * captures.size := by
    dsimp only [layout]
    simp only [ClosureLayout.ofCaptures]
    rw [count]
    apply align8_eq_of_mod_eq_zero
    simp [target, headerBytes]
  obtain ⟨middle, objectAllocation, captureWrite, cursorEq⟩ :=
    allocateClosure_decompose state result dispatch function arity captureKinds
      captures address targetId count capturesLtArity targetIdEq arityFits fixedFits
      allocated
  have middleValid := valid.allocateObject objectAllocation
  have captureListLength : captureList.length = captures.size := by
    simp [captureList, count]
  have captureListTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      captureList[index]? = some (kind, lane) →
      lane.valueType = kind.valueType := by
    intro index kind lane atIndex
    obtain ⟨kindAt, laneAt⟩ := Array.lookup_zip_toList atIndex
    obtain ⟨indexLt, _⟩ := Array.getElem?_eq_some_iff.mp laneAt
    have semanticIndex : index < semantic.size := by omega
    let value := semantic[index]'semanticIndex
    have valueAt : semantic[index]? = some value := by
      simp [value, semanticIndex]
    exact (captureRelated index kind lane value kindAt laneAt valueAt).physical_type
  have objectExtent := MemoryState.allocateObject_extent objectAllocation
  have middleExtent : middle.heapCursor = address.value + layout.allocationBytes := by
    rw [objectExtent, allocationEq]
  have captureEnd : closureCaptureAddress address.value
      (0 + captureList.length) ≤ middle.memory.size := by
    rw [Nat.zero_add, captureListLength]
    have endEq : closureCaptureAddress address.value captures.size =
        middle.heapCursor := by
      rw [middleExtent, layoutExact]
      simp [closureCaptureAddress, target]
      omega
    rw [endEq]
    exact middleValid.cursorInBounds
  have capturePost := LinearMemory.writeClosureCaptures_post middle.memory
    result.memory address.value 0 captureList captureListTyped captureEnd captureWrite
  have stateEq : ({ middle with memory := result.memory } : MemoryState) = result := by
    cases middle
    cases result
    simp_all
  have finalValidMiddle :
      ({ middle with memory := result.memory } : MemoryState).FrontierInvariant := by
    refine {
      cursorAligned := middleValid.cursorAligned
      cursorInBounds := by simpa [capturePost.size] using middleValid.cursorInBounds
      unusedZero := ?_ }
    intro byte afterCursor finalInBounds
    have middleInBounds : byte < middle.memory.size := by
      rw [← capturePost.size]
      exact finalInBounds
    have middleZero := middleValid.unusedZero byte afterCursor middleInBounds
    have afterCaptures :
        closureCaptureAddress address.value (0 + captureList.length) ≤ byte := by
      rw [Nat.zero_add, captureListLength]
      have endEq : closureCaptureAddress address.value captures.size =
          middle.heapCursor := by
        rw [middleExtent, layoutExact]
        simp [closureCaptureAddress, target]
        omega
      rw [endEq]
      exact afterCursor
    have framed := capturePost.byteFrame byte (.inr afterCaptures)
    cases finalByte : result.memory[byte]? with
    | none => simp [LinearMemory.readByte, finalByte, middleZero] at framed
    | some value =>
        simp [LinearMemory.readByte, finalByte, middleZero] at framed
        subst value
        rfl
  have finalValid : result.FrontierInvariant := by
    simpa [stateEq] using finalValidMiddle
  have headerBefore :=
    MemoryState.readLiveHeader_of_allocateObject_eq_ok state middle .closure
      (layout.allocationBytes - headerBytes) false targetId
      (UInt32.ofNat arity) (UInt32.ofNat captures.size) 0 address objectAllocation
  have headerAfter := MemoryState.readLiveHeader_of_writeClosureCaptures middle
    result.memory address captureList capturePost
  have exactHeader : result.readLiveHeader address = .ok
      (Header.forAllocation .closure layout.allocationBytes false targetId
        (UInt32.ofNat arity) (UInt32.ofNat captures.size) 0) := by
    rw [← stateEq, headerAfter]
    simpa [allocationEq] using headerBefore
  have addressHeap : address.classify = .heap := by
    have checked := exactHeader
    unfold MemoryState.readLiveHeader at checked
    split at checked
    next heap => exact heap
    next => contradiction
  have arityToNat : (UInt32.ofNat arity).toNat = arity :=
    UInt32.toNat_ofNat_of_lt' arityFits
  have fixedToNat : (UInt32.ofNat captures.size).toNat = captures.size :=
    UInt32.toNat_ofNat_of_lt' fixedFits
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state middle .closure
      (layout.allocationBytes - headerBytes) false targetId
      (UInt32.ofNat arity) (UInt32.ofNat captures.size) 0 address objectAllocation
  have allocationPost := MemoryState.allocate_spec state rawState
    (align8 (headerBytes + (layout.allocationBytes - headerBytes))) address
      rawAllocation
  have layoutLt : layout.allocationBytes < UInt32.size := by
    have endWithin := allocationPost.endWithinAddressSpace
    have allocatedBytesEq :
        align8 (align8 (headerBytes + (layout.allocationBytes - headerBytes))) =
          layout.allocationBytes := by
      rw [align8_align8, allocationEq]
    have nonzero : address.value ≠ 0 := by
      intro zero
      simp [Word32.classify, zero] at addressHeap
    have allocatedLt :
        align8 (align8 (headerBytes + (layout.allocationBytes - headerBytes))) <
          wordModulus := by
      omega
    rw [allocatedBytesEq] at allocatedLt
    simpa [wordModulus] using allocatedLt
  have allocationBytesToNat :
      (UInt32.ofNat layout.allocationBytes).toNat = layout.allocationBytes :=
    UInt32.toNat_ofNat_of_lt' layoutLt
  have requiredBytes :
      align8 (headerBytes + target.semanticSlotBytes * captures.size) =
        layout.allocationBytes := by
    rw [← layoutExact, layoutAligned]
  have closureHeader : readClosureHeader result address = .ok
      (Header.forAllocation .closure layout.allocationBytes false targetId
        (UInt32.ofNat arity) (UInt32.ofNat captures.size) 0) := by
    unfold readClosureHeader
    simp only [addressHeap, if_true]
    rw [exactHeader]
    simp only [liftMemory, Bind.bind, Except.bind]
    simp [Header.forAllocation, arityToNat, fixedToNat, allocationBytesToNat,
      capturesLtArity, requiredBytes]
    rw [if_pos (by decide)]
    rfl
  let metadata : ClosureMetadata := {
    header := Header.forAllocation .closure layout.allocationBytes false targetId
      (UInt32.ofNat arity) (UInt32.ofNat captures.size) 0
    targetId
    function
    arity
    fixed := captures.size }
  have metadataRead : readClosureMetadata result dispatch address = .ok metadata := by
    unfold readClosureMetadata
    rw [closureHeader]
    simp only [Bind.bind, Except.bind]
    simp only [Header.forAllocation]
    rw [targetLookup]
    simp [metadata, arityToNat, fixedToNat]
    change Except.ok metadata = Except.ok metadata
    rfl
  have extension := witness.bindClosure_extends location address function arity
    captureKinds locationFresh descriptorFresh
  refine ⟨finalValid, ?_⟩
  refine {
    descriptor := by
      exact witness.lookup_bindClosure_descriptor location address function arity
        captureKinds
    metadata := ⟨metadata, metadataRead, rfl, rfl, ?_⟩
    captureKindsSize := count.trans semanticCount.symm
    captures := ?_ }
  · exact semanticCount.symm
  · intro index kind value kindAt valueAt
    obtain ⟨indexLt, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
    have captureIndex : index < captures.size := by omega
    let lane := captures[index]'captureIndex
    have laneAt : captures[index]? = some lane := by
      simp [lane, captureIndex]
    have listAt : captureList[index]? = some (kind, lane) := by
      apply Array.lookup_zip_toList_of kindAt laneAt
    have read := capturePost.captureAt index kind lane listAt
    exact ⟨lane, by simpa only [Nat.zero_add] using read,
      (captureRelated index kind lane value kindAt laneAt valueAt).witnessExtension
        extension⟩

end Fir.Wasm.Concrete
