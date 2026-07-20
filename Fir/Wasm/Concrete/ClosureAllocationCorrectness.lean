import Fir.Wasm.Concrete.ClosureCorrectness
import Fir.Wasm.Concrete.ClosureHeapCorrectness
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
    (descriptors : ClosureDescriptorTable)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (captures : Array LaneValue) (address : Word32) (targetId descriptorId : UInt32)
    (count : captureKinds.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (descriptorIdEq : closureDescriptorId descriptors captureKinds = .ok descriptorId)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.size < UInt32.size)
    (allocated : allocateClosure state dispatch descriptors function arity
      captureKinds captures = .ok (result, address)) :
    ∃ middle,
      state.allocateObject .closure
        ((ClosureLayout.ofCaptures captureKinds).allocationBytes - headerBytes)
        false targetId (UInt32.ofNat arity) (UInt32.ofNat captures.size)
          descriptorId =
          .ok (middle, address) ∧
      middle.memory.writeClosureCaptures address.value 0
        (captureKinds.toList.zip captures.toList) = .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  unfold allocateClosure at allocated
  simp [count, capturesLtArity, targetIdEq, descriptorIdEq, uint32Field,
    arityFits, fixedFits] at allocated
  change (do
    let (middle, actualAddress) ← liftMemory <|
      state.allocateObject .closure
        ((ClosureLayout.ofCaptures captureKinds).allocationBytes - headerBytes)
        false targetId (UInt32.ofNat arity) (UInt32.ofNat captures.size)
          descriptorId
    let memory ← liftMemory <| middle.memory.writeClosureCaptures
      actualAddress.value 0 (captureKinds.toList.zip captures.toList)
    return ({ middle with memory }, actualAddress)) =
      .ok (result, address) at allocated
  cases objectAllocation : state.allocateObject .closure
      ((ClosureLayout.ofCaptures captureKinds).allocationBytes - headerBytes)
      false targetId (UInt32.ofNat arity) (UInt32.ofNat captures.size)
        descriptorId with
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
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (function : Lean.Name) (arity : Nat)
    (captureKinds : Array AbiKind) (captures : Array LaneValue)
    (semantic : Array Value) (location : Location) (address : Word32)
    (targetId descriptorId : UInt32)
    (valid : state.FrontierInvariant)
    (count : captureKinds.size = captures.size)
    (semanticCount : semantic.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (targetLookup : dispatch.lookup? targetId = some function)
    (descriptorIdEq : closureDescriptorId descriptors captureKinds = .ok descriptorId)
    (descriptorLookup : descriptors.lookup? descriptorId = some captureKinds)
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
    (allocated : allocateClosure state dispatch descriptors function arity
      captureKinds captures = .ok (result, address)) :
    result.FrontierInvariant ∧
    ClosureObjectRel result
      (witness.bindClosure location address function arity captureKinds)
      dispatch descriptors address function arity captureKinds semantic ∧
    result.readLiveHeader address = .ok
      (Header.forAllocation .closure
        (ClosureLayout.ofCaptures captureKinds).allocationBytes false targetId
        (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId) ∧
    closureCaptureAddress address.value semantic.size ≤ result.heapCursor := by
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
    allocateClosure_decompose state result dispatch descriptors function arity
      captureKinds captures address targetId descriptorId count capturesLtArity
      targetIdEq descriptorIdEq arityFits fixedFits allocated
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
      (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId address
      objectAllocation
  have headerAfter := MemoryState.readLiveHeader_of_writeClosureCaptures middle
    result.memory address captureList capturePost
  have exactHeader : result.readLiveHeader address = .ok
      (Header.forAllocation .closure layout.allocationBytes false targetId
        (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId) := by
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
      (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId address
      objectAllocation
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
        (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId) := by
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
      (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId
    targetId
    descriptorId
    function
    arity
    fixed := captures.size
    captureKinds }
  have metadataRead : readClosureMetadata result dispatch descriptors address =
      .ok metadata := by
    unfold readClosureMetadata
    rw [closureHeader]
    simp only [Bind.bind, Except.bind]
    simp only [Header.forAllocation]
    rw [targetLookup]
    rw [descriptorLookup]
    simp [metadata, arityToNat, fixedToNat, count]
    change Except.ok metadata = Except.ok metadata
    rfl
  have extension := witness.bindClosure_extends location address function arity
    captureKinds locationFresh descriptorFresh
  have objectRelated : ClosureObjectRel result
      (witness.bindClosure location address function arity captureKinds)
      dispatch descriptors address function arity captureKinds semantic := by
    refine {
      descriptor := by
        exact witness.lookup_bindClosure_descriptor location address function arity
          captureKinds
      metadata := ⟨metadata, metadataRead, rfl, rfl, ?_, rfl⟩
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
  have semanticExtent : closureCaptureAddress address.value semantic.size ≤
      result.heapCursor := by
    have endAtMiddle : closureCaptureAddress address.value captures.size =
        middle.heapCursor := by
      rw [middleExtent, layoutExact]
      simp [closureCaptureAddress, target]
      omega
    rw [semanticCount, cursorEq, endAtMiddle]
    omega
  exact ⟨finalValid, objectRelated, by simpa [layout] using exactHeader,
    semanticExtent⟩

/-- The strengthened allocation postcondition assembles the canonical fresh
semantic closure cell. Exact module-table agreement prevents the local
decoder from being installed under unrelated whole-heap metadata. -/
theorem ClosureObjectRel.freshCellRel
    {result : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {captures : Array LaneValue} {semantic : Array Value}
    {location : Location} {address : Word32} {targetId descriptorId : UInt32}
    (related : ClosureObjectRel result
      (witness.bindClosure location address function arity captureKinds)
      dispatch descriptors address function arity captureKinds semantic)
    (dispatchEq : witness.closureDispatch = dispatch)
    (descriptorsEq : witness.closureDescriptors = descriptors)
    (descriptorLookup : descriptors.lookup? descriptorId = some captureKinds)
    (fixedFits : captures.size < UInt32.size)
    (semanticCount : semantic.size = captures.size)
    (headerRead : result.readLiveHeader address = .ok
      (Header.forAllocation .closure
        (ClosureLayout.ofCaptures captureKinds).allocationBytes false targetId
        (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId))
    (extent : closureCaptureAddress address.value semantic.size ≤
      result.heapCursor) :
    ClosureCellRel result
      (witness.bindClosure location address function arity captureKinds) address
      ({ object := .closure function arity semantic } : HeapCell) := by
  let header := Header.forAllocation .closure
    (ClosureLayout.ofCaptures captureKinds).allocationBytes false targetId
    (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId
  have tablesRelated : ClosureObjectRel result
      (witness.bindClosure location address function arity captureKinds)
      (witness.bindClosure location address function arity captureKinds).closureDispatch
      (witness.bindClosure location address function arity captureKinds).closureDescriptors
      address function arity captureKinds semantic := by
    simpa [RefinementWitness.bindClosure, dispatchEq, descriptorsEq] using related
  have descriptorAt :
      (witness.bindClosure location address function arity captureKinds).closureDescriptors.lookup?
          header.aux3 = some captureKinds := by
    simpa [header, Header.forAllocation, RefinementWitness.bindClosure,
      descriptorsEq] using descriptorLookup
  have fixedCount : header.aux2.toNat = semantic.size := by
    rw [semanticCount]
    simp [header, Header.forAllocation,
      UInt32.toNat_ofNat_of_lt' fixedFits]
  exact .closure rfl tablesRelated (by simpa [header] using headerRead) rfl
    descriptorAt rfl fixedCount extent rfl rfl rfl

/-- Successful allocation establishes both the concrete frontier invariant
and the canonical fresh semantic closure cell under the module's tables. -/
theorem allocateClosure_cellRel
    (state result : MemoryState) (witness : RefinementWitness)
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (function : Lean.Name) (arity : Nat)
    (captureKinds : Array AbiKind) (captures : Array LaneValue)
    (semantic : Array Value) (location : Location) (address : Word32)
    (targetId descriptorId : UInt32)
    (valid : state.FrontierInvariant)
    (count : captureKinds.size = captures.size)
    (semanticCount : semantic.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (targetLookup : dispatch.lookup? targetId = some function)
    (descriptorIdEq : closureDescriptorId descriptors captureKinds = .ok descriptorId)
    (descriptorLookup : descriptors.lookup? descriptorId = some captureKinds)
    (dispatchEq : witness.closureDispatch = dispatch)
    (descriptorsEq : witness.closureDescriptors = descriptors)
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
    (allocated : allocateClosure state dispatch descriptors function arity
      captureKinds captures = .ok (result, address)) :
    result.FrontierInvariant ∧
    ClosureCellRel result
      (witness.bindClosure location address function arity captureKinds) address
      ({ object := .closure function arity semantic } : HeapCell) := by
  obtain ⟨finalValid, objectRelated, headerRead, extent⟩ :=
    allocateClosure_objectRel state result witness dispatch descriptors function
      arity captureKinds captures semantic location address targetId descriptorId
      valid count semanticCount capturesLtArity targetIdEq targetLookup descriptorIdEq
      descriptorLookup arityFits fixedFits captureRelated locationFresh
      descriptorFresh allocated
  exact ⟨finalValid, objectRelated.freshCellRel dispatchEq descriptorsEq
    descriptorLookup fixedFits semanticCount headerRead extent⟩

/-- A public closure allocation preserves every byte below the old frontier,
so all previously decoded objects can be transported uniformly. -/
theorem allocateClosure_prefixExtension
    (state result : MemoryState) (dispatch : ClosureDispatchTable)
    (descriptors : ClosureDescriptorTable)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (captures : Array LaneValue) (address : Word32) (targetId descriptorId : UInt32)
    (valid : state.FrontierInvariant)
    (count : captureKinds.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (descriptorIdEq : closureDescriptorId descriptors captureKinds = .ok descriptorId)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.size < UInt32.size)
    (captureTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      captureKinds[index]? = some kind →
      captures[index]? = some lane →
      lane.valueType = kind.valueType)
    (allocated : allocateClosure state dispatch descriptors function arity
      captureKinds captures = .ok (result, address)) :
    state.PrefixExtension result := by
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
  obtain ⟨middle, objectAllocation, captureWrite, cursorEq⟩ :=
    allocateClosure_decompose state result dispatch descriptors function arity
      captureKinds captures address targetId descriptorId count capturesLtArity
      targetIdEq descriptorIdEq arityFits fixedFits allocated
  have objectExtension := valid.allocateObject_prefixExtension objectAllocation
  have middleValid := valid.allocateObject objectAllocation
  have captureListLength : captureList.length = captures.size := by
    simp [captureList, count]
  have listTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      captureList[index]? = some (kind, lane) →
      lane.valueType = kind.valueType := by
    intro index kind lane atIndex
    obtain ⟨kindAt, laneAt⟩ := Array.lookup_zip_toList atIndex
    exact captureTyped index kind lane kindAt laneAt
  have objectExtent := MemoryState.allocateObject_extent objectAllocation
  have captureEnd : closureCaptureAddress address.value
      (0 + captureList.length) ≤ middle.memory.size := by
    have endAtCursor : closureCaptureAddress address.value captures.size ≤
        middle.heapCursor := by
      unfold closureCaptureAddress
      rw [objectExtent, allocationEq]
      dsimp only [layout, ClosureLayout.ofCaptures]
      rw [count]
      simpa only [Nat.add_assoc] using Nat.add_le_add_left
        (align8_ge (headerBytes + target.semanticSlotBytes * captures.size))
        address.value
    rw [Nat.zero_add, captureListLength]
    exact Nat.le_trans endAtCursor middleValid.cursorInBounds
  have capturePost := LinearMemory.writeClosureCaptures_post middle.memory
    result.memory address.value 0 captureList listTyped captureEnd captureWrite
  have freshAddress := valid.allocateObject_address objectAllocation
  refine {
    cursor := by simpa [cursorEq] using objectExtension.cursor
    memorySize := by
      calc
        state.memory.size ≤ middle.memory.size := objectExtension.memorySize
        _ = result.memory.size := capturePost.size.symm
    readByte := ?_ }
  intro byte beforeCursor
  calc
    result.memory.readByte byte = middle.memory.readByte byte :=
      capturePost.byteFrame byte (.inl (by
        simp [closureCaptureAddress, target, freshAddress]
        omega))
    _ = state.memory.readByte byte := objectExtension.readByte byte beforeCursor

def semanticClosureCell (function : Lean.Name) (arity : Nat)
    (captures : Array Value) : HeapCell := {
  object := .closure function arity captures }

def semanticClosureResult (runtime : RuntimeState) (function : Lean.Name)
    (arity : Nat) (captures : Array Value) : RuntimeState := {
  runtime with
  heap := (runtime.nextLocation, semanticClosureCell function arity captures) ::
    runtime.heap
  nextLocation := runtime.nextLocation + 1 }

@[simp] theorem alloc_closure_eq (runtime : RuntimeState) (function : Lean.Name)
    (arity : Nat) (captures : Array Value) :
    alloc runtime (.closure function arity captures) =
      (semanticClosureResult runtime function arity captures,
        .heap runtime.nextLocation) := rfl

/-- A successful concrete closure allocation extends the complete live heap,
installs the fresh closure cell under the immutable module tables, and relates
the returned address at both closure-compatible object ABI kinds. -/
theorem allocateClosure_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState)
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (function : Lean.Name) (arity : Nat)
    (captureKinds : Array AbiKind) (captures : Array LaneValue)
    (semantic : Array Value) (address : Word32)
    (targetId descriptorId : UInt32)
    (related : LiveHeapRel state witness runtime)
    (count : captureKinds.size = captures.size)
    (semanticCount : semantic.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (targetLookup : dispatch.lookup? targetId = some function)
    (descriptorIdEq : closureDescriptorId descriptors captureKinds = .ok descriptorId)
    (descriptorLookup : descriptors.lookup? descriptorId = some captureKinds)
    (dispatchEq : witness.closureDispatch = dispatch)
    (descriptorsEq : witness.closureDescriptors = descriptors)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.size < UInt32.size)
    (captureTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      captureKinds[index]? = some kind →
      captures[index]? = some lane →
      lane.valueType = kind.valueType)
    (captureRelated : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue)
        (value : Value),
      captureKinds[index]? = some kind →
      captures[index]? = some lane →
      semantic[index]? = some value →
      ValueRel witness kind lane value)
    (allocated : allocateClosure state dispatch descriptors function arity
      captureKinds captures = .ok (result, address)) :
    let nextWitness := witness.bindClosure runtime.nextLocation address function arity
      captureKinds
    LiveHeapRel result nextWitness
        (semanticClosureResult runtime function arity semantic) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      ValueRel nextWitness .tobject (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨middle, objectAllocation, _, cursorEq⟩ :=
    allocateClosure_decompose state result dispatch descriptors function arity
      captureKinds captures address targetId descriptorId count capturesLtArity
      targetIdEq descriptorIdEq arityFits fixedFits allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have heapExtension := allocateClosure_prefixExtension state result dispatch descriptors
    function arity captureKinds captures address targetId descriptorId
    related.frontier count capturesLtArity targetIdEq descriptorIdEq arityFits
    fixedFits captureTyped allocated
  have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
    cases found : witness.locations.lookup? runtime.nextLocation with
    | none => rfl
    | some oldAddress =>
        exfalso
        obtain ⟨cell, semanticFound, _⟩ :=
          related.concreteToSemantic runtime.nextLocation oldAddress found
        exact (Nat.lt_irrefl runtime.nextLocation)
          (related.locationsBeforeNext runtime.nextLocation cell semanticFound)
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    omega
  have witnessExtension := witness.bindClosure_extends runtime.nextLocation address
    function arity captureKinds locationFresh descriptorFresh
  obtain ⟨finalFrontier, objectRelated, exactHeader, closureExtent⟩ :=
    allocateClosure_objectRel state result witness dispatch descriptors function
      arity captureKinds captures semantic runtime.nextLocation address targetId
      descriptorId related.frontier count semanticCount capturesLtArity targetIdEq
      targetLookup descriptorIdEq descriptorLookup arityFits fixedFits captureRelated
      locationFresh descriptorFresh allocated
  have closureRelated := objectRelated.freshCellRel dispatchEq descriptorsEq
    descriptorLookup fixedFits semanticCount exactHeader closureExtent
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
  let header := Header.forAllocation .closure
    (ClosureLayout.ofCaptures captureKinds).allocationBytes false targetId
      (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId
  have headerRead : result.readLiveHeader address = .ok header := by
    simpa [header] using exactHeader
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts result address header
      headerRead).1
  have witnessWellFormed := related.witnessWellFormed.bindClosure
    runtime.nextLocation address function arity captureKinds addressHeap
      locationAddressFresh promotedAddressFresh
  obtain ⟨_, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address header headerRead
  let layout := ClosureLayout.ofCaptures captureKinds
  have layoutMinimum : headerBytes ≤ layout.allocationBytes := by
    dsimp only [layout]
    simp only [ClosureLayout.ofCaptures]
    exact Nat.le_trans (by omega) (align8_ge _)
  have layoutAligned : align8 layout.allocationBytes = layout.allocationBytes := by
    apply align8_eq_of_mod_eq_zero
    simpa only [layout, target] using ClosureLayout.ofCaptures_aligned captureKinds
  have allocationEq :
      align8 (headerBytes + (layout.allocationBytes - headerBytes)) =
        layout.allocationBytes := by
    rw [Nat.add_sub_of_le layoutMinimum, layoutAligned]
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state middle .closure
      (layout.allocationBytes - headerBytes) false targetId
      (UInt32.ofNat arity) (UInt32.ofNat captures.size) descriptorId address (by
        simpa [layout] using objectAllocation)
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
      have addressClass := allocationPost.addressClass
      simp [Word32.classify, zero] at addressClass
    have allocatedLt :
        align8 (align8 (headerBytes + (layout.allocationBytes - headerBytes))) <
          wordModulus := by omega
    rw [allocatedBytesEq] at allocatedLt
    simpa [wordModulus] using allocatedLt
  have headerCapacity : header.allocationBytes.toNat = layout.allocationBytes := by
    simpa [header, layout, Header.forAllocation] using
      UInt32.toNat_ofNat_of_lt' layoutLt
  have objectExtent := MemoryState.allocateObject_extent objectAllocation
  have newExtent :
      address.value + header.allocationBytes.toNat ≤ result.heapCursor := by
    rw [headerCapacity, cursorEq, objectExtent, allocationEq]
    exact Nat.le_refl _
  have newRegion : ∃ newHeader,
      Header.read result.memory address = .ok newHeader ∧
      headerBytes ≤ newHeader.allocationBytes.toNat ∧
      newHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + newHeader.allocationBytes.toNat ≤ result.heapCursor :=
    ⟨header, rawHeaderRead, headerMinimum, headerAligned, newExtent⟩
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial heapExtension address freshAddress
      (fun other different =>
        witness.lookup_bindClosure_descriptor_other runtime.nextLocation address
          other function arity captureKinds different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindClosure runtime.nextLocation address function arity captureKinds)
      address (semanticClosureCell function arity semantic) :=
    .closure (by simpa [semanticClosureCell] using closureRelated)
  refine ⟨?_, ?_, ?_⟩
  · refine {
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
        exact Nat.lt_succ_self runtime.nextLocation
      · have oldFound : findCell? runtime.heap location = some cell := by
          simpa [semanticClosureResult, findCell?, isNew, Ne.symm isNew] using found
        exact Nat.lt_trans (related.locationsBeforeNext location cell oldFound)
          (Nat.lt_succ_self runtime.nextLocation)
    · have cursorGrowth : state.heapCursor + headerBytes ≤ result.heapCursor := by
        rw [← freshAddress]
        exact closureRelated.headerOwned
      have oldFuel := related.releaseFuelBound
      simp [semanticClosureResult, headerBytes] at oldFuel cursorGrowth ⊢
      omega
    · intro other descriptor found
      by_cases isNew : address.value = other.value
      · rw [← isNew]
        exact closureRelated.headerOwned
      · rw [witness.lookup_bindClosure_descriptor_other runtime.nextLocation
          address other function arity captureKinds isNew] at found
        exact Nat.le_trans (related.descriptorsOwned other descriptor found)
          heapExtension.cursor
    · intro location cell found
      by_cases isNew : location = runtime.nextLocation
      · subst location
        have cellEq : cell = semanticClosureCell function arity semantic := by
          simpa [semanticClosureResult, findCell?] using found.symm
        subst cell
        exact ⟨address,
          RefinementWitness.lookup_bindClosure_location witness runtime.nextLocation
            address function arity captureKinds,
          .live newCellRelated⟩
      · have oldFound : findCell? runtime.heap location = some cell := by
          simpa [semanticClosureResult, findCell?, isNew, Ne.symm isNew] using found
        obtain ⟨oldAddress, mapped, cellRelated⟩ :=
          related.semanticToConcrete location cell oldFound
        exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
          (cellRelated.prefixExtension heapExtension).witnessExtension witnessExtension⟩
    · intro location concreteAddress mapped
      by_cases isNew : location = runtime.nextLocation
      · subst location
        simp [RefinementWitness.bindClosure, LocationMap.lookup?] at mapped
        subst concreteAddress
        exact ⟨semanticClosureCell function arity semantic,
          by simp [semanticClosureResult, findCell?], .live newCellRelated⟩
      · rw [witness.lookup_bindClosure_location_other runtime.nextLocation location
          address function arity captureKinds isNew] at mapped
        obtain ⟨cell, oldFound, cellRelated⟩ :=
          related.concreteToSemantic location concreteAddress mapped
        exact ⟨cell, by
            simpa [semanticClosureResult, findCell?, isNew, Ne.symm isNew],
          (cellRelated.prefixExtension heapExtension).witnessExtension witnessExtension⟩
    · intro payload concreteAddress mapped
      exact ((related.promoted payload concreteAddress mapped).prefixExtension heapExtension)
        |>.witnessExtension witnessExtension
  · exact .object (.mapped
      (RefinementWitness.lookup_bindClosure_location witness runtime.nextLocation
        address function arity captureKinds))
  · exact .tobject (.heap (.mapped
      (RefinementWitness.lookup_bindClosure_location witness runtime.nextLocation
        address function arity captureKinds)))

/-- Allocation-producing Talos clients need the explicit witness-extension
fact in addition to the complete closure heap relation. -/
theorem allocateClosure_liveHeapRel_extends
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState)
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (function : Lean.Name) (arity : Nat)
    (captureKinds : Array AbiKind) (captures : Array LaneValue)
    (semantic : Array Value) (address : Word32)
    (targetId descriptorId : UInt32)
    (related : LiveHeapRel state witness runtime)
    (count : captureKinds.size = captures.size)
    (semanticCount : semantic.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (targetLookup : dispatch.lookup? targetId = some function)
    (descriptorIdEq : closureDescriptorId descriptors captureKinds =
      .ok descriptorId)
    (descriptorLookup : descriptors.lookup? descriptorId = some captureKinds)
    (dispatchEq : witness.closureDispatch = dispatch)
    (descriptorsEq : witness.closureDescriptors = descriptors)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.size < UInt32.size)
    (captureTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      captureKinds[index]? = some kind →
      captures[index]? = some lane →
      lane.valueType = kind.valueType)
    (captureRelated : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue)
        (value : Value),
      captureKinds[index]? = some kind →
      captures[index]? = some lane →
      semantic[index]? = some value →
      ValueRel witness kind lane value)
    (allocated : allocateClosure state dispatch descriptors function arity
      captureKinds captures = .ok (result, address)) :
    let nextWitness := witness.bindClosure runtime.nextLocation address function
      arity captureKinds
    witness.Extends nextWitness ∧
      LiveHeapRel result nextWitness
        (semanticClosureResult runtime function arity semantic) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      ValueRel nextWitness .tobject (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨_, objectAllocation, _, _⟩ :=
    allocateClosure_decompose state result dispatch descriptors function arity
      captureKinds captures address targetId descriptorId count capturesLtArity
      targetIdEq descriptorIdEq arityFits fixedFits allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
    cases found : witness.locations.lookup? runtime.nextLocation with
    | none => rfl
    | some oldAddress =>
        exfalso
        obtain ⟨cell, semanticFound, _⟩ :=
          related.concreteToSemantic runtime.nextLocation oldAddress found
        exact (Nat.lt_irrefl runtime.nextLocation)
          (related.locationsBeforeNext runtime.nextLocation cell semanticFound)
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    omega
  have extension := witness.bindClosure_extends runtime.nextLocation address
    function arity captureKinds locationFresh descriptorFresh
  have refined := allocateClosure_liveHeapRel state result witness runtime dispatch
    descriptors function arity captureKinds captures semantic address targetId
    descriptorId related count semanticCount capturesLtArity targetIdEq
    targetLookup descriptorIdEq descriptorLookup dispatchEq descriptorsEq arityFits
    fixedFits captureTyped captureRelated allocated
  exact ⟨extension, refined.1, refined.2.1, refined.2.2⟩

end Fir.Wasm.Concrete
