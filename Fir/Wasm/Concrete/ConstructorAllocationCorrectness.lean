import Fir.Wasm.Concrete.HeapRefinement
import Fir.Wasm.Concrete.FreshAllocationCorrectness
import Fir.Wasm.Concrete.NaturalAllocationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/--
Exact address-space reservation for constructor allocation across both
physical representations. Nonempty layouts allocate their constructor extent;
empty layouts reuse the tagged-value encoder and may allocate one promoted
tag object when the constructor index does not fit the wasm32 immediate lane.
-/
def constructorAllocationBytes (info : LCNF.CtorInfo) : Nat :=
  if (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0 then
    naturalAllocationBytes info.cidx
  else
    (ConstructorLayout.ofInfo info).allocationBytes

@[simp] theorem uint32Field_eq_ok (field : String) (value : Nat)
    (fits : value < UInt32.size) :
    uint32Field field value = .ok (UInt32.ofNat value) := by
  simp [uint32Field, fits]

/-- A successful allocated (non-immediate) constructor call is exactly one
checked object allocation followed by the verified object-slot writer. -/
theorem allocateConstructor_nonempty_decompose
    (state result : MemoryState) (info : LCNF.CtorInfo)
    (fields : Array Word32) (address : Word32)
    (arity : fields.size = info.size)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (allocated : allocateConstructor state info fields = .ok (result, address)) :
    ∃ middle,
      state.allocateObject .constructor
        ((ConstructorLayout.ofInfo info).allocationBytes - headerBytes) false
        (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
        (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize) =
          .ok (middle, address) ∧
      writeObjectFields middle.memory address.value 0 fields.toList =
        .ok result.memory ∧
      result.heapCursor = middle.heapCursor := by
  unfold allocateConstructor at allocated
  simp [arity, uint32Field, tagFits, objectFieldsFit, usizeFieldsFit,
    scalarBytesFit] at allocated
  simp [nonempty] at allocated
  change (do
    let (middle, actualAddress) ← liftMemory <|
      state.allocateObject .constructor
        ((ConstructorLayout.ofInfo info).allocationBytes - headerBytes) false
        (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
        (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize)
    let memory ← liftMemory <|
      writeObjectFields middle.memory actualAddress.value 0 fields.toList
    return ({ middle with memory }, actualAddress)) =
      .ok (result, address) at allocated
  cases objectAllocation : state.allocateObject .constructor
      ((ConstructorLayout.ofInfo info).allocationBytes - headerBytes) false
      (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
      (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize) with
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
          writeObjectFields middle.memory actualAddress.value 0 fields.toList
        return ({ middle with memory }, actualAddress)) =
          .ok (result, address) at allocated
      cases fieldWrite : writeObjectFields middle.memory actualAddress.value 0
          fields.toList with
      | error failure =>
          rw [fieldWrite] at allocated
          change Except.error (ConcreteError.ofMemory failure) =
            Except.ok (result, address) at allocated
          contradiction
      | ok finalMemory =>
          rw [fieldWrite] at allocated
          change Except.ok ({ middle with memory := finalMemory }, actualAddress) =
            Except.ok (result, address) at allocated
          have pairEq : ({ middle with memory := finalMemory }, actualAddress) =
              (result, address) := Except.ok.inj allocated
          have resultEq : { middle with memory := finalMemory } = result :=
            congrArg Prod.fst pairEq
          have addressEq : actualAddress = address := congrArg Prod.snd pairEq
          subst result
          subst address
          exact ⟨middle, rfl, fieldWrite, rfl⟩

/--
A nonempty constructor allocation is constructive from the exact static
`ConstructorLayout` address-space capacity. Header metadata and every object
slot write are then in-bounds inside that allocated extent.
-/
theorem MemoryState.FrontierInvariant.allocateConstructor_nonempty_eq_ok_of_capacity
    {state : MemoryState} (valid : state.FrontierInvariant)
    (info : LCNF.CtorInfo) (fields : Array Word32)
    (arity : fields.size = info.size)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (capacity :
      state.AllocationCapacity (ConstructorLayout.ofInfo info).allocationBytes) :
    ∃ result address,
      allocateConstructor state info fields = .ok (result, address) := by
  let layout := ConstructorLayout.ofInfo info
  have layoutMinimum : headerBytes ≤ layout.allocationBytes := by
    dsimp only [layout]
    simp only [ConstructorLayout.ofInfo]
    exact Nat.le_trans (by omega) (align8_ge _)
  have layoutAligned : align8 layout.allocationBytes = layout.allocationBytes := by
    apply align8_eq_of_mod_eq_zero
    simpa [target, layout] using ConstructorLayout.ofInfo_allocation_aligned info
  have allocationEq :
      align8 (headerBytes + (layout.allocationBytes - headerBytes)) =
        layout.allocationBytes := by
    rw [Nat.add_sub_of_le layoutMinimum, layoutAligned]
  obtain ⟨middle, address, objectAllocation⟩ :=
    state.allocateObject_eq_ok_of_capacity .constructor
      (layout.allocationBytes - headerBytes) false
      (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
      (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize)
      valid.cursorAligned (by simpa [layout, allocationEq] using capacity)
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have fieldsEnd :
      objectFieldAddress address.value fields.toList.length ≤
        middle.heapCursor := by
    rw [middleExtent, allocationEq]
    simp [objectFieldAddress, target, layout, ConstructorLayout.ofInfo, arity]
    have aligned := align8_ge
      (headerBytes +
        target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [target] at aligned
    omega
  obtain ⟨memory, fieldWrite, _⟩ :=
    writeObjectFields_spec middle.memory address.value 0 fields.toList
      (Nat.le_trans (by simpa using fieldsEnd) middleValid.cursorInBounds)
  refine ⟨{ middle with memory }, address, ?_⟩
  unfold allocateConstructor
  simp [arity, uint32Field, tagFits, objectFieldsFit, usizeFieldsFit,
    scalarBytesFit, nonempty]
  change
    (do
      let (middle, address) ← liftMemory <|
        state.allocateObject .constructor
          (layout.allocationBytes - headerBytes) false
          (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
          (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize)
      let memory ← liftMemory <|
        Fir.Wasm.Concrete.writeObjectFields middle.memory address.value 0
          fields.toList
      return ({ middle with memory }, address)) =
        .ok ({ middle with memory }, address)
  rw [objectAllocation]
  simp only [liftMemory, Bind.bind, Except.bind]
  rw [fieldWrite]
  rfl

/--
A source-path budget makes one nonempty constructor allocation constructive
and transports the residual budget through header and field installation.
-/
theorem MemoryState.FrontierInvariant.allocateConstructor_nonempty_eq_ok_of_budget
    {state : MemoryState} (valid : state.FrontierInvariant)
    (info : LCNF.CtorInfo) (fields : Array Word32)
    (arity : fields.size = info.size)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    {remainingBytes : Nat}
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits :
      (ConstructorLayout.ofInfo info).allocationBytes ≤ remainingBytes) :
    ∃ result address,
      allocateConstructor state info fields = .ok (result, address) ∧
        result.AddressSpaceBudget
          (remainingBytes -
            (ConstructorLayout.ofInfo info).allocationBytes) := by
  let layout := ConstructorLayout.ofInfo info
  have layoutMinimum : headerBytes ≤ layout.allocationBytes := by
    dsimp only [layout]
    simp only [ConstructorLayout.ofInfo]
    exact Nat.le_trans (by omega) (align8_ge _)
  have layoutAligned : align8 layout.allocationBytes = layout.allocationBytes := by
    apply align8_eq_of_mod_eq_zero
    simpa [target, layout] using ConstructorLayout.ofInfo_allocation_aligned info
  have allocationEq :
      align8 (headerBytes + (layout.allocationBytes - headerBytes)) =
        layout.allocationBytes := by
    rw [Nat.add_sub_of_le layoutMinimum, layoutAligned]
  obtain ⟨result, address, allocated⟩ :=
    valid.allocateConstructor_nonempty_eq_ok_of_capacity info fields arity
      nonempty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit
      (budget.allocationCapacity (by simpa [layout, layoutAligned] using fits))
  obtain ⟨middle, objectAllocation, _, cursorEq⟩ :=
    allocateConstructor_nonempty_decompose state result info fields address arity
      nonempty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have middleBudget :=
    budget.allocateObject valid.cursorAligned
      (by simpa [layout, allocationEq] using fits) objectAllocation
  refine ⟨result, address, allocated, {
    cursorPositive := ?_
    endWithinAddressSpace := ?_ }⟩
  · rw [cursorEq]
    exact middleBudget.cursorPositive
  · rw [cursorEq]
    simpa [layout, allocationEq] using middleBudget.endWithinAddressSpace

/--
One representation-sensitive source-path budget makes arbitrary constructor
allocation constructive. This is the common fresh-allocation boundary for
ordinary constructor declarations and zero-token reuse.
-/
theorem MemoryState.FrontierInvariant.allocateConstructor_eq_ok_of_budget
    {state : MemoryState} (valid : state.FrontierInvariant)
    (info : LCNF.CtorInfo) (fields : Array Word32)
    (arity : fields.size = info.size)
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    {remainingBytes : Nat}
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : constructorAllocationBytes info ≤ remainingBytes) :
    ∃ result address,
      allocateConstructor state info fields = .ok (result, address) ∧
        result.AddressSpaceBudget
          (remainingBytes - constructorAllocationBytes info) := by
  by_cases empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0
  · have sourceTagged : info.cidx ≤ maxTaggedPayload := by
      exact Nat.le_trans (Nat.le_of_lt tagFits) (by decide)
    have naturalFits :
        naturalAllocationBytes info.cidx ≤ remainingBytes := by
      simpa [constructorAllocationBytes, empty] using fits
    obtain ⟨result, address, allocated, remaining⟩ :=
      valid.allocateNatural_eq_ok_of_budget info.cidx budget naturalFits
    have encoded :
        encodeTagged state (UInt64.ofNat info.cidx) =
          .ok (result, address) := by
      unfold allocateNatural at allocated
      rw [if_pos sourceTagged] at allocated
      exact allocated
    refine ⟨result, address, ?_, ?_⟩
    · unfold allocateConstructor
      rw [if_pos arity]
      rw [uint32Field_eq_ok "constructor tag" info.cidx tagFits]
      simp only [Bind.bind, Except.bind]
      rw [if_pos (by simp [empty.1.1, empty.1.2, empty.2])]
      simpa [UInt32.toNat_ofNat_of_lt' tagFits] using encoded
    · simpa [constructorAllocationBytes, empty] using remaining
  · have layoutFits :
        (ConstructorLayout.ofInfo info).allocationBytes ≤ remainingBytes := by
      simpa [constructorAllocationBytes, empty] using fits
    obtain ⟨result, address, allocated, remaining⟩ :=
      valid.allocateConstructor_nonempty_eq_ok_of_budget info fields arity
        empty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit budget
        layoutFits
    exact ⟨result, address, allocated, by
      simpa [constructorAllocationBytes, empty] using remaining⟩

/-- A public nonempty constructor allocation preserves every byte owned below
the old frontier, so all previously decoded heap cells can be framed. -/
theorem allocateConstructor_nonempty_prefixExtension
    (state result : MemoryState) (info : LCNF.CtorInfo)
    (fields : Array Word32) (address : Word32)
    (valid : state.FrontierInvariant)
    (arity : fields.size = info.size)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (allocated : allocateConstructor state info fields = .ok (result, address)) :
    state.PrefixExtension result := by
  let layout := ConstructorLayout.ofInfo info
  have layoutMinimum : headerBytes ≤ layout.allocationBytes := by
    dsimp only [layout]
    simp only [ConstructorLayout.ofInfo]
    exact Nat.le_trans (by omega) (align8_ge _)
  have layoutAligned : align8 layout.allocationBytes = layout.allocationBytes := by
    apply align8_eq_of_mod_eq_zero
    simpa [target, layout] using ConstructorLayout.ofInfo_allocation_aligned info
  have allocationEq :
      align8 (headerBytes + (layout.allocationBytes - headerBytes)) =
        layout.allocationBytes := by
    rw [Nat.add_sub_of_le layoutMinimum, layoutAligned]
  have fieldsEnd : objectFieldAddress address.value fields.toList.length ≤
      address.value + align8
        (headerBytes + (layout.allocationBytes - headerBytes)) := by
    rw [allocationEq]
    simp [objectFieldAddress, target, layout, ConstructorLayout.ofInfo, arity]
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [target] at aligned
    omega
  obtain ⟨middle, objectAllocation, fieldWrite, cursorEq⟩ :=
    allocateConstructor_nonempty_decompose state result info fields address arity
      nonempty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have extension := valid.allocateObject_prefixExtension objectAllocation
  have completed := valid.allocateObject_writeObjectFields objectAllocation
    fieldsEnd fieldWrite
  dsimp only at completed
  rcases completed with ⟨_, _, payloadPost, _⟩
  have freshAddress := valid.allocateObject_address objectAllocation
  refine {
    cursor := by simpa [cursorEq] using extension.cursor
    memorySize := by
      calc
        state.memory.size ≤ middle.memory.size := extension.memorySize
        _ = result.memory.size := payloadPost.size.symm
    readByte := ?_ }
  intro byte beforeCursor
  calc
    result.memory.readByte byte = middle.memory.readByte byte :=
      payloadPost.byteFrame byte (.inl (by
        simp [objectFieldAddress, target, freshAddress]
        omega))
    _ = state.memory.readByte byte := extension.readByte byte beforeCursor

theorem LinearMemory.readUInt64_of_zero_bytes (memory : LinearMemory)
    (address : Nat)
    (zero : ∀ offset, offset < 8 → memory[address + offset]? = some 0) :
    memory.readUInt64 address = .ok 0 := by
  have h0 : memory[address]? = some 0 := by simpa using zero 0 (by decide)
  have h1 : memory[address + 1]? = some 0 := zero 1 (by decide)
  have h2 : memory[address + 2]? = some 0 := zero 2 (by decide)
  have h3 : memory[address + 3]? = some 0 := zero 3 (by decide)
  have h4 : memory[address + 4]? = some 0 := zero 4 (by decide)
  have h5 : memory[address + 5]? = some 0 := zero 5 (by decide)
  have h6 : memory[address + 6]? = some 0 := zero 6 (by decide)
  have h7 : memory[address + 7]? = some 0 := zero 7 (by decide)
  have low : memory.readUInt32 address = .ok 0 := by
    unfold LinearMemory.readUInt32 LinearMemory.readByte
    rw [h0, h1, h2, h3]
    rfl
  have high : memory.readUInt32 (address + 4) = .ok 0 := by
    unfold LinearMemory.readUInt32 LinearMemory.readByte
    rw [h4]
    have h5' : memory[address + 4 + 1]? = some 0 := by simpa using h5
    have h6' : memory[address + 4 + 2]? = some 0 := by simpa using h6
    have h7' : memory[address + 4 + 3]? = some 0 := by simpa using h7
    rw [h5', h6', h7']
    rfl
  unfold LinearMemory.readUInt64
  rw [low, high]
  rfl

/-- The non-empty concrete constructor allocator establishes the decoded
constructor relation for the semantic object allocated by W2. -/
theorem allocateConstructor_nonempty_objectRel
    (state result : MemoryState) (witness : RefinementWitness)
    (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (fields : Array Word32) (semanticFields : Array Value) (address : Word32)
    (valid : state.FrontierInvariant)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (allocated : allocateConstructor state info fields = .ok (result, address)) :
    result.FrontierInvariant ∧
    ConstructorObjectRel result witness address info fieldKinds {
      tag := info.cidx
      objectFields := semanticFields
      usizeFields := Array.replicate info.usize 0
      scalarFields := [] } ∧
    result.readLiveHeader address = .ok
      (Header.forAllocation .constructor (ConstructorLayout.ofInfo info).allocationBytes
        false (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
        (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize)) := by
  let layout := ConstructorLayout.ofInfo info
  have layoutMinimum : headerBytes ≤ layout.allocationBytes := by
    dsimp only [layout]
    simp only [ConstructorLayout.ofInfo]
    exact Nat.le_trans (by omega) (align8_ge _)
  have layoutAligned : align8 layout.allocationBytes = layout.allocationBytes := by
    apply align8_eq_of_mod_eq_zero
    simpa [target, layout] using ConstructorLayout.ofInfo_allocation_aligned info
  have allocationEq :
      align8 (headerBytes + (layout.allocationBytes - headerBytes)) =
        layout.allocationBytes := by
    rw [Nat.add_sub_of_le layoutMinimum, layoutAligned]
  have fieldsEnd : objectFieldAddress address.value fields.toList.length ≤
      address.value + align8
        (headerBytes + (layout.allocationBytes - headerBytes)) := by
    rw [allocationEq]
    simp [objectFieldAddress, target, layout, ConstructorLayout.ofInfo, arity]
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [target] at aligned
    omega
  obtain ⟨middle, objectAllocation, fieldWrite, cursorEq⟩ :=
    allocateConstructor_nonempty_decompose state result info fields address arity
      nonempty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have completed := valid.allocateObject_writeObjectFields objectAllocation
    fieldsEnd fieldWrite
  dsimp only at completed
  rcases completed with ⟨finalValid, headerRead, payloadPost, remainingZero⟩
  have stateEq : ({ middle with memory := result.memory } : MemoryState) = result := by
    cases middle
    cases result
    simp_all
  have finalValidResult : result.FrontierInvariant := by
    simpa [stateEq] using finalValid
  have tagToNat : (UInt32.ofNat info.cidx).toNat = info.cidx :=
    UInt32.toNat_ofNat_of_lt' tagFits
  have objectFieldsToNat : (UInt32.ofNat info.size).toNat = info.size :=
    UInt32.toNat_ofNat_of_lt' objectFieldsFit
  have usizeFieldsToNat : (UInt32.ofNat info.usize).toNat = info.usize :=
    UInt32.toNat_ofNat_of_lt' usizeFieldsFit
  have scalarBytesToNat : (UInt32.ofNat info.ssize).toNat = info.ssize :=
    UInt32.toNat_ofNat_of_lt' scalarBytesFit
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state middle .constructor
      (layout.allocationBytes - headerBytes) false
      (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
      (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize) address objectAllocation
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
          wordModulus := by
      omega
    rw [allocatedBytesEq] at allocatedLt
    simpa [wordModulus] using allocatedLt
  have allocationBytesToNat :
      (UInt32.ofNat layout.allocationBytes).toNat = layout.allocationBytes :=
    UInt32.toNat_ofNat_of_lt' layoutLt
  have exactHeader : result.readLiveHeader address = .ok
      (Header.forAllocation .constructor layout.allocationBytes false
        (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
        (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize)) := by
    rw [← stateEq]
    simpa [layout, allocationEq] using headerRead
  have objectExtent := MemoryState.allocateObject_extent objectAllocation
  have resultExtent : address.value + layout.allocationBytes ≤ result.heapCursor := by
    rw [cursorEq, objectExtent, allocationEq]
    exact Nat.le_refl _
  have addressHeap : address.classify = .heap := by
    have checked := exactHeader
    unfold MemoryState.readLiveHeader at checked
    split at checked
    next heap => exact heap
    next => contradiction
  have constructorHeader : readConstructorHeader result address = Except.ok
      (Header.forAllocation .constructor layout.allocationBytes false
        (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
        (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize)) := by
    unfold readConstructorHeader
    simp [addressHeap, exactHeader, Header.forAllocation, liftMemory]
    rfl
  refine ⟨finalValidResult, ?_, by simpa [layout] using exactHeader⟩
  refine {
    header := ?_
    headerOwned := Nat.le_trans
      (Nat.add_le_add_left layoutMinimum address.value) resultExtent
    extent := resultExtent
    semanticObjectFields := semanticArity
    semanticUSizeFields := by simp
    semanticScalarFields := by simp
    fieldKindsSize
    fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · exact ⟨Header.forAllocation .constructor layout.allocationBytes false
      (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
      (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize), exactHeader,
      rfl, (by simpa [layout, Header.forAllocation] using
        Nat.le_of_eq allocationBytesToNat.symm), tagToNat, objectFieldsToNat,
      usizeFieldsToNat,
      scalarBytesToNat⟩
  · intro index kind value kindAt valueAt
    obtain ⟨word, wordAt, related⟩ := fieldRelated index kind value kindAt valueAt
    have indexLt : index < info.size := by
      obtain ⟨indexLtFields, _⟩ := Array.getElem?_eq_some_iff.mp wordAt
      omega
    have listAt : fields.toList[index]? = some word := by simpa using wordAt
    have fieldRead := payloadPost.fieldAt index word listAt
    have paddingRead := payloadPost.paddingAt index word listAt
    have concreteRead : readObjectField result address index = .ok word := by
      have exactField : result.memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * index) =
          .ok word := by
        simpa [objectFieldAddress] using fieldRead
      have exactPadding : result.memory.readUInt32
          (address.value + headerBytes + target.semanticSlotBytes * index + 4) =
          .ok 0 := by
        simpa [objectFieldAddress] using paddingRead
      unfold readObjectField
      rw [constructorHeader]
      simp only [Bind.bind, Except.bind]
      simp [Header.forAllocation, objectFieldsToNat, indexLt, exactField,
        exactPadding, liftMemory]
      rfl
    exact ⟨word, concreteRead, related⟩
  · intro index value valueAt
    change (Array.replicate info.usize (0 : UInt64))[index]? = some value at valueAt
    rw [Array.getElem?_replicate] at valueAt
    have indexLt : index < info.usize := by
      by_cases inBounds : index < info.usize
      · exact inBounds
      · rw [if_neg inBounds] at valueAt
        contradiction
    rw [if_pos indexLt] at valueAt
    have valueZero : value = 0 := Option.some.inj valueAt.symm
    subst value
    let offset := address.value + headerBytes +
      target.semanticSlotBytes * (info.size + index)
    have zeroBytes : ∀ byteOffset, byteOffset < 8 →
        result.memory[offset + byteOffset]? = some 0 := by
      intro byteOffset byteOffsetLt
      apply remainingZero (offset + byteOffset)
      · simp [offset, objectFieldAddress, target, arity]
        omega
      · rw [allocationEq]
        simp [offset, layout, ConstructorLayout.ofInfo, target]
        have aligned := align8_ge
          (headerBytes + 8 * (info.size + info.usize) + info.ssize)
        omega
    have usizeRead : result.memory.readUInt64 offset = .ok 0 :=
      LinearMemory.readUInt64_of_zero_bytes result.memory offset zeroBytes
    unfold readUSizeField
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    simp [Header.forAllocation, objectFieldsToNat, usizeFieldsToNat, indexLt,
      offset, usizeRead, liftMemory]

end Fir.Wasm.Concrete
