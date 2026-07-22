import Fir.Wasm.Concrete.PayloadMutationFrameCorrectness
import Fir.Wasm.Concrete.ScalarMutationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Exact 64-bit payload transaction behind a successful checked `USize`
slot update, packaged with the reusable whole-allocation frame. -/
theorem ConstructorObjectRel.writeUSizeField_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (valid : state.FrontierInvariant)
    (index : Nat) (value : UInt64) (indexValid : index < info.usize) :
    ∃ result header,
      Fir.Wasm.Concrete.writeUSizeField state address index value = .ok result ∧
      Header.read state.memory address = .ok header ∧
      state.TargetMutationFrame result address header.allocationBytes.toNat ∧
      result.FrontierInvariant := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, rawRead, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeader : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * (header.aux1.toNat + index)
  have offsetEq : offset = address.value + headerBytes +
      target.semanticSlotBytes * (info.size + index) := by
    simp [offset, objectCount]
  have insideLayout :
      offset + 8 ≤ address.value + (ConstructorLayout.ofInfo info).allocationBytes := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    rw [offsetEq]
    simp [ConstructorLayout.ofInfo, target] at layoutBound ⊢
    omega
  have insideAllocation :
      offset + 8 ≤ address.value + header.allocationBytes.toNat :=
    Nat.le_trans insideLayout (Nat.add_le_add_left allocationBytes address.value)
  have writeInBounds : offset + 7 < state.memory.size := by
    have allocationInMemory :
        address.value + header.allocationBytes.toNat ≤ state.memory.size :=
      extentInMemory
    omega
  obtain ⟨middle, lowWrite, middleSize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec state.memory offset value.toUInt32 (by omega)
  obtain ⟨memory, highWrite, memorySize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec middle (offset + 4)
      (value >>> (32 : UInt64)).toUInt32 (by omega)
  have fieldWrite : state.memory.writeUInt64 offset value = .ok memory := by
    unfold LinearMemory.writeUInt64
    rw [lowWrite]
    change middle.writeUInt32 (offset + 4)
      (value >>> (32 : UInt64)).toUInt32 = .ok memory
    exact highWrite
  let result : MemoryState := { state with memory }
  have operation : Fir.Wasm.Concrete.writeUSizeField state address index value =
      .ok result := by
    unfold Fir.Wasm.Concrete.writeUSizeField
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    simp [indexValid, usizeCount, objectCount]
    rw [← offsetEq]
    change (do
      let memory ← liftMemory (state.memory.writeUInt64 offset value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [fieldWrite]
    rfl
  have targetFrame : state.TargetMutationFrame result address
      header.allocationBytes.toNat :=
    MemoryState.TargetMutationFrame.ofWriteUInt64 (by rfl) writeInBounds
      fieldWrite (by simp [offset]) insideAllocation
  have beforeFrontier : offset + 8 ≤ state.heapCursor :=
    Nat.le_trans insideLayout related.extent
  exact ⟨result, header, operation, rawRead, targetFrame,
    valid.writeUInt64 beforeFrontier fieldWrite⟩

/-- Exact 64-bit payload transaction behind a successful packed scalar
update, packaged with the reusable whole-allocation frame. -/
theorem ConstructorObjectRel.writeScalarUInt64Field_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (valid : state.FrontierInvariant)
    (slotIndex byteOffset : Nat) (value : UInt64)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 8 ≤ info.ssize) :
    ∃ result header,
      Fir.Wasm.Concrete.writeScalarUInt64Field state address slotIndex byteOffset
        value = .ok result ∧
      Header.read state.memory address = .ok header ∧
      state.TargetMutationFrame result address header.allocationBytes.toNat ∧
      result.FrontierInvariant := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, rawRead, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeader : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * slotIndex + byteOffset
  have insideLayout :
      offset + 8 ≤ address.value + (ConstructorLayout.ofInfo info).allocationBytes := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [offset, slotIndexEq, ConstructorLayout.ofInfo, target] at layoutBound ⊢
    omega
  have insideAllocation :
      offset + 8 ≤ address.value + header.allocationBytes.toNat :=
    Nat.le_trans insideLayout (Nat.add_le_add_left allocationBytes address.value)
  have writeInBounds : offset + 7 < state.memory.size := by
    omega
  obtain ⟨middle, lowWrite, middleSize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec state.memory offset value.toUInt32 (by omega)
  obtain ⟨memory, highWrite, memorySize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec middle (offset + 4)
      (value >>> (32 : UInt64)).toUInt32 (by omega)
  have fieldWrite : state.memory.writeUInt64 offset value = .ok memory := by
    unfold LinearMemory.writeUInt64
    rw [lowWrite]
    change middle.writeUInt32 (offset + 4)
      (value >>> (32 : UInt64)).toUInt32 = .ok memory
    exact highWrite
  let result : MemoryState := { state with memory }
  have scalarAddress : scalarFieldAddress address header slotIndex byteOffset 8 =
      .ok offset := by
    unfold scalarFieldAddress
    simp [slotIndexEq, objectCount, usizeCount, fieldFits, scalarCount, offset]
    rfl
  have operation : Fir.Wasm.Concrete.writeScalarUInt64Field state address slotIndex
      byteOffset value = .ok result := by
    unfold Fir.Wasm.Concrete.writeScalarUInt64Field
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    rw [scalarAddress]
    change (do
      let memory ← liftMemory (state.memory.writeUInt64 offset value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [fieldWrite]
    rfl
  have targetFrame : state.TargetMutationFrame result address
      header.allocationBytes.toNat :=
    MemoryState.TargetMutationFrame.ofWriteUInt64 (by rfl) writeInBounds
      fieldWrite (by simp [offset]; omega) insideAllocation
  have beforeFrontier : offset + 8 ≤ state.heapCursor :=
    Nat.le_trans insideLayout related.extent
  exact ⟨result, header, operation, rawRead, targetFrame,
    valid.writeUInt64 beforeFrontier fieldWrite⟩

/-- Exact 32-bit payload transaction behind a successful packed scalar
update, packaged with the reusable whole-allocation frame. -/
theorem ConstructorObjectRel.writeScalarUInt32Field_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (valid : state.FrontierInvariant)
    (slotIndex byteOffset : Nat) (value : UInt32)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 4 ≤ info.ssize) :
    ∃ result header,
      Fir.Wasm.Concrete.writeScalarUInt32Field state address slotIndex byteOffset
        value = .ok result ∧
      Header.read state.memory address = .ok header ∧
      state.TargetMutationFrame result address header.allocationBytes.toNat ∧
      result.FrontierInvariant := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, rawRead, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeader : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * slotIndex + byteOffset
  have insideLayout :
      offset + 4 ≤ address.value + (ConstructorLayout.ofInfo info).allocationBytes := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [offset, slotIndexEq, ConstructorLayout.ofInfo, target] at layoutBound ⊢
    omega
  have insideAllocation :
      offset + 4 ≤ address.value + header.allocationBytes.toNat :=
    Nat.le_trans insideLayout (Nat.add_le_add_left allocationBytes address.value)
  have writeInBounds : offset + 3 < state.memory.size := by
    omega
  obtain ⟨memory, fieldWrite, memorySize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec state.memory offset value writeInBounds
  let result : MemoryState := { state with memory }
  have scalarAddress : scalarFieldAddress address header slotIndex byteOffset 4 =
      .ok offset := by
    unfold scalarFieldAddress
    simp [slotIndexEq, objectCount, usizeCount, fieldFits, scalarCount, offset]
    rfl
  have operation : Fir.Wasm.Concrete.writeScalarUInt32Field state address slotIndex
      byteOffset value = .ok result := by
    unfold Fir.Wasm.Concrete.writeScalarUInt32Field
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    rw [scalarAddress]
    change (do
      let memory ← liftMemory (state.memory.writeUInt32 offset value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [fieldWrite]
    rfl
  have targetFrame : state.TargetMutationFrame result address
      header.allocationBytes.toNat :=
    MemoryState.TargetMutationFrame.ofWriteUInt32 (by rfl) writeInBounds
      fieldWrite (by simp [offset]; omega) insideAllocation
  have beforeFrontier : offset + 4 ≤ state.heapCursor :=
    Nat.le_trans insideLayout related.extent
  exact ⟨result, header, operation, rawRead, targetFrame,
    valid.writeUInt32 beforeFrontier fieldWrite⟩

/-- Exact 16-bit payload transaction behind a successful packed scalar
update, packaged with the reusable whole-allocation frame. -/
theorem ConstructorObjectRel.writeScalarUInt16Field_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (valid : state.FrontierInvariant)
    (slotIndex byteOffset : Nat) (value : UInt16)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 2 ≤ info.ssize) :
    ∃ result header,
      Fir.Wasm.Concrete.writeScalarUInt16Field state address slotIndex byteOffset
        value = .ok result ∧
      Header.read state.memory address = .ok header ∧
      state.TargetMutationFrame result address header.allocationBytes.toNat ∧
      result.FrontierInvariant := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, rawRead, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeader : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * slotIndex + byteOffset
  have insideLayout :
      offset + 2 ≤ address.value + (ConstructorLayout.ofInfo info).allocationBytes := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [offset, slotIndexEq, ConstructorLayout.ofInfo, target] at layoutBound ⊢
    omega
  have insideAllocation :
      offset + 2 ≤ address.value + header.allocationBytes.toNat :=
    Nat.le_trans insideLayout (Nat.add_le_add_left allocationBytes address.value)
  have writeInBounds : offset + 1 < state.memory.size := by
    omega
  obtain ⟨memory, fieldWrite, memorySize, _, _, _⟩ :=
    LinearMemory.writeUInt16_spec state.memory offset value writeInBounds
  let result : MemoryState := { state with memory }
  have scalarAddress : scalarFieldAddress address header slotIndex byteOffset 2 =
      .ok offset := by
    unfold scalarFieldAddress
    simp [slotIndexEq, objectCount, usizeCount, fieldFits, scalarCount, offset]
    rfl
  have operation : Fir.Wasm.Concrete.writeScalarUInt16Field state address slotIndex
      byteOffset value = .ok result := by
    unfold Fir.Wasm.Concrete.writeScalarUInt16Field
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    rw [scalarAddress]
    change (do
      let memory ← liftMemory (state.memory.writeUInt16 offset value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [fieldWrite]
    rfl
  have targetFrame : state.TargetMutationFrame result address
      header.allocationBytes.toNat :=
    MemoryState.TargetMutationFrame.ofWriteUInt16 (by rfl) writeInBounds
      fieldWrite (by simp [offset]; omega) insideAllocation
  have beforeFrontier : offset + 2 ≤ state.heapCursor :=
    Nat.le_trans insideLayout related.extent
  exact ⟨result, header, operation, rawRead, targetFrame,
    valid.writeUInt16 beforeFrontier fieldWrite⟩

/-- Exact byte payload transaction behind a successful packed scalar update,
packaged with the reusable whole-allocation frame. -/
theorem ConstructorObjectRel.writeScalarUInt8Field_targetFrame
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (valid : state.FrontierInvariant)
    (slotIndex byteOffset : Nat) (value : UInt8)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 1 ≤ info.ssize) :
    ∃ result header,
      Fir.Wasm.Concrete.writeScalarUInt8Field state address slotIndex byteOffset
        value = .ok result ∧
      Header.read state.memory address = .ok header ∧
      state.TargetMutationFrame result address header.allocationBytes.toNat ∧
      result.FrontierInvariant := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  obtain ⟨heap, rawRead, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have constructorHeader : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let offset := address.value + headerBytes +
    target.semanticSlotBytes * slotIndex + byteOffset
  have insideLayout :
      offset + 1 ≤ address.value + (ConstructorLayout.ofInfo info).allocationBytes := by
    have layoutBound := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [offset, slotIndexEq, ConstructorLayout.ofInfo, target] at layoutBound ⊢
    omega
  have insideAllocation :
      offset + 1 ≤ address.value + header.allocationBytes.toNat :=
    Nat.le_trans insideLayout (Nat.add_le_add_left allocationBytes address.value)
  have writeInBounds : offset < state.memory.size := by
    omega
  let memory : LinearMemory := state.memory.set offset value writeInBounds
  have fieldWrite : state.memory.writeByte offset value = .ok memory := by
    simp [LinearMemory.writeByte, writeInBounds, memory]
  let result : MemoryState := { state with memory }
  have scalarAddress : scalarFieldAddress address header slotIndex byteOffset 1 =
      .ok offset := by
    unfold scalarFieldAddress
    simp [slotIndexEq, objectCount, usizeCount, fieldFits, scalarCount, offset]
    rfl
  have operation : Fir.Wasm.Concrete.writeScalarUInt8Field state address slotIndex
      byteOffset value = .ok result := by
    unfold Fir.Wasm.Concrete.writeScalarUInt8Field
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    rw [scalarAddress]
    change (do
      let memory ← liftMemory (state.memory.writeByte offset value)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [fieldWrite]
    rfl
  have targetFrame : state.TargetMutationFrame result address
      header.allocationBytes.toNat :=
    MemoryState.TargetMutationFrame.ofWriteByte (by rfl) writeInBounds
      fieldWrite (by simp [offset]; omega) insideAllocation
  have beforeFrontier : offset + 1 ≤ state.heapCursor :=
    Nat.le_trans insideLayout related.extent
  exact ⟨result, header, operation, rawRead, targetFrame,
    valid.writeByte beforeFrontier fieldWrite⟩

/-- Exact common-header transaction behind a successful concrete constructor
tag update. Exposing the write lets the generic whole-heap frame theorem carry
every non-target allocation. -/
theorem writeTag_header
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (tag : Nat) (tagFits : tag < UInt32.size) :
    ∃ result updatedHeader memory,
      writeTag state address tag = .ok result ∧
      updatedHeader = { header with aux0 := UInt32.ofNat tag } ∧
      result = { state with memory } ∧
      updatedHeader.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  have constructorHeader : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let updatedHeader : Header := { header with aux0 := UInt32.ofNat tag }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : writeTag state address tag = .ok result := by
    unfold writeTag
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    rw [uint32Field_eq_ok "constructor tag" tag tagFits]
    change (do
      let memory ← liftMemory (updatedHeader.write state.memory address)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decoded : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decoded]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  exact ⟨result, updatedHeader, memory, operation, rfl, rfl, headerWrite,
    valid.writeHeader headerOwned headerWrite, headerAfter⟩

/-- Whole-heap refinement for the successful constructor tag mutation. -/
theorem LiveHeapRel.writeTag_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (tag : Nat) (tagFits : tag < UInt32.size) :
    ∃ result nextRuntime,
      writeTag state address tag = .ok result ∧
      Fir.LeanIR.Impure.setTag runtime (.object (.heap location)) tag =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let replacement : HeapCell := {
    cell with object := .ctor { semantic with tag := tag } }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
          headerWrite, finalValid, headerAfter⟩ :=
        writeTag_header related.frontier headerRead headerKind
          objectRelated.headerOwned tag tagFits
      obtain ⟨localResult, localOperation, objectAfter⟩ :=
        objectRelated.writeTag tag tagFits
      rw [operation] at localOperation
      have resultMatch := Except.ok.inj localOperation
      subst localResult
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.constructor descriptor (by rfl) objectAfter headerAfter
        · simpa [updatedEq] using headerKind
        · simpa [replacement, updatedEq] using refCount
        · simpa [replacement, updatedEq] using persistent
        · simpa [replacement] using cellLive
      have oldRawRead :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state address _
          headerRead).2.1
      have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
        Nat.le_trans objectRelated.headerOwned related.frontier.cursorInBounds
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_headerWrite mapped found descriptor oldRawRead resultEq
          headerInBounds headerWrite (by simp [updatedEq]) finalValid targetAfter
      have sourceOperation :
          Fir.LeanIR.Impure.setTag runtime (.object (.heap location)) tag =
            .ok nextRuntime := by
        simp [Fir.LeanIR.Impure.setTag, modifyConstructor, getConstructor,
          getLiveCell, Bind.bind, Except.bind, found, live, objectEq]
        change setCell runtime location replacement = .ok nextRuntime
        exact semanticSet
      exact ⟨result, nextRuntime, operation, sourceOperation, heapRelated⟩
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- Whole-heap refinement for a successful constructor `USize` mutation. -/
theorem LiveHeapRel.writeUSizeField_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (index : Nat) (value : UInt64)
    (indexValid : index < semantic.usizeFields.size) :
    ∃ result nextRuntime,
      Fir.Wasm.Concrete.writeUSizeField state address index value = .ok result ∧
      Fir.LeanIR.Impure.setUSizeField runtime (.object (.heap location)) index
        (.usize value) = .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let updatedSemantic : ConstructorObject := {
    semantic with usizeFields := semantic.usizeFields.set index value indexValid }
  let replacement : HeapCell := { cell with object := .ctor updatedSemantic }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      obtain ⟨result, targetHeader, operation, targetRawRead, targetFrame,
          finalValid⟩ :=
        objectRelated.writeUSizeField_targetFrame related.frontier index value
          (by rw [← objectRelated.semanticUSizeFields]; exact indexValid)
      obtain ⟨localResult, localOperation, objectAfter⟩ :=
        objectRelated.writeUSizeField index value
          (by rw [← objectRelated.semanticUSizeFields]; exact indexValid)
      rw [operation] at localOperation
      have resultMatch := Except.ok.inj localOperation
      subst localResult
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.constructor descriptor (by rfl)
          (by simpa [updatedSemantic] using objectAfter)
          (by rw [targetFrame.targetLiveHeader]; exact headerRead) headerKind
        · simpa [replacement] using refCount
        · simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          targetFrame finalValid targetAfter
      have sourceOperation :
          Fir.LeanIR.Impure.setUSizeField runtime (.object (.heap location)) index
            (.usize value) = .ok nextRuntime := by
        simp [Fir.LeanIR.Impure.setUSizeField, modifyConstructor, getConstructor,
          getLiveCell, Bind.bind, Except.bind, found, live, objectEq]
        simp only [pure, Except.pure]
        rw [dif_pos indexValid]
        change setCell runtime location replacement = .ok nextRuntime
        exact semanticSet
      exact ⟨result, nextRuntime, operation, sourceOperation, heapRelated⟩
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- Whole-heap refinement for a successful packed `UInt64` mutation. The
static descriptor premise keeps scalar-capacity facts at the ABI boundary
rather than adding them to semantic constructor values. -/
theorem LiveHeapRel.writeScalarUInt64Field_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (slotIndex byteOffset : Nat) (value : UInt64)
    (retainedDisjoint : ∀ field ∈ semantic.scalarFields,
      field.width ≠ slotIndex ∨ field.offset ≠ byteOffset →
      field.offset + scalarValueByteSize field.value ≤ byteOffset ∨
        byteOffset + 8 ≤ field.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 8 ≤ info.ssize) :
    ∃ result nextRuntime,
      Fir.Wasm.Concrete.writeScalarUInt64Field state address slotIndex byteOffset
        value = .ok result ∧
      Fir.LeanIR.Impure.setScalarField runtime (.object (.heap location))
        slotIndex byteOffset (.scalar (.uint64 value)) = .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let updatedSemantic : ConstructorObject := {
    semantic with
      scalarFields := {
        width := slotIndex
        offset := byteOffset
        value := .uint64 value } :: semantic.scalarFields.filter fun old =>
          old.width != slotIndex || old.offset != byteOffset }
  let replacement : HeapCell := { cell with object := .ctor updatedSemantic }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      obtain ⟨result, targetHeader, operation, targetRawRead, targetFrame,
          finalValid⟩ :=
        objectRelated.writeScalarUInt64Field_targetFrame related.frontier
          slotIndex byteOffset value slotIndexEq fieldFits
      obtain ⟨localResult, localOperation, _, _, _, _, objectAfter⟩ :=
        objectRelated.writeScalarUInt64Field slotIndex byteOffset value
          retainedDisjoint slotIndexEq fieldFits
      rw [operation] at localOperation
      have resultMatch := Except.ok.inj localOperation
      subst localResult
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.constructor descriptor (by rfl)
          (by simpa [updatedSemantic] using objectAfter)
          (by rw [targetFrame.targetLiveHeader]; exact headerRead) headerKind
        · simpa [replacement] using refCount
        · simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          targetFrame finalValid targetAfter
      have sourceOperation :
          Fir.LeanIR.Impure.setScalarField runtime (.object (.heap location))
            slotIndex byteOffset (.scalar (.uint64 value)) = .ok nextRuntime := by
        simp [Fir.LeanIR.Impure.setScalarField, modifyConstructor, getConstructor,
          getLiveCell, Bind.bind, Except.bind, found, live, objectEq]
        simp only [pure, Except.pure]
        change setCell runtime location replacement = .ok nextRuntime
        exact semanticSet
      exact ⟨result, nextRuntime, operation, sourceOperation, heapRelated⟩
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- Whole-heap refinement for a successful packed `UInt32` mutation. -/
theorem LiveHeapRel.writeScalarUInt32Field_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (slotIndex byteOffset : Nat) (value : UInt32)
    (retainedDisjoint : ∀ field ∈ semantic.scalarFields,
      field.width ≠ slotIndex ∨ field.offset ≠ byteOffset →
      field.offset + scalarValueByteSize field.value ≤ byteOffset ∨
        byteOffset + 4 ≤ field.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 4 ≤ info.ssize) :
    ∃ result nextRuntime,
      Fir.Wasm.Concrete.writeScalarUInt32Field state address slotIndex byteOffset
        value = .ok result ∧
      Fir.LeanIR.Impure.setScalarField runtime (.object (.heap location))
        slotIndex byteOffset (.scalar (.uint32 value)) = .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let updatedSemantic : ConstructorObject := {
    semantic with
      scalarFields := {
        width := slotIndex
        offset := byteOffset
        value := .uint32 value } :: semantic.scalarFields.filter fun old =>
          old.width != slotIndex || old.offset != byteOffset }
  let replacement : HeapCell := { cell with object := .ctor updatedSemantic }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      obtain ⟨result, targetHeader, operation, targetRawRead, targetFrame,
          finalValid⟩ :=
        objectRelated.writeScalarUInt32Field_targetFrame related.frontier
          slotIndex byteOffset value slotIndexEq fieldFits
      obtain ⟨localResult, localOperation, _, _, _, _, objectAfter⟩ :=
        objectRelated.writeScalarUInt32Field slotIndex byteOffset value
          retainedDisjoint slotIndexEq fieldFits
      rw [operation] at localOperation
      have resultMatch := Except.ok.inj localOperation
      subst localResult
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.constructor descriptor (by rfl)
          (by simpa [updatedSemantic] using objectAfter)
          (by rw [targetFrame.targetLiveHeader]; exact headerRead) headerKind
        · simpa [replacement] using refCount
        · simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          targetFrame finalValid targetAfter
      have sourceOperation :
          Fir.LeanIR.Impure.setScalarField runtime (.object (.heap location))
            slotIndex byteOffset (.scalar (.uint32 value)) = .ok nextRuntime := by
        simp [Fir.LeanIR.Impure.setScalarField, modifyConstructor, getConstructor,
          getLiveCell, Bind.bind, Except.bind, found, live, objectEq]
        simp only [pure, Except.pure]
        change setCell runtime location replacement = .ok nextRuntime
        exact semanticSet
      exact ⟨result, nextRuntime, operation, sourceOperation, heapRelated⟩
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- Whole-heap refinement for a successful packed `UInt16` mutation. -/
theorem LiveHeapRel.writeScalarUInt16Field_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (slotIndex byteOffset : Nat) (value : UInt16)
    (retainedDisjoint : ∀ field ∈ semantic.scalarFields,
      field.width ≠ slotIndex ∨ field.offset ≠ byteOffset →
      field.offset + scalarValueByteSize field.value ≤ byteOffset ∨
        byteOffset + 2 ≤ field.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 2 ≤ info.ssize) :
    ∃ result nextRuntime,
      Fir.Wasm.Concrete.writeScalarUInt16Field state address slotIndex byteOffset
        value = .ok result ∧
      Fir.LeanIR.Impure.setScalarField runtime (.object (.heap location))
        slotIndex byteOffset (.scalar (.uint16 value)) = .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let updatedSemantic : ConstructorObject := {
    semantic with
      scalarFields := {
        width := slotIndex
        offset := byteOffset
        value := .uint16 value } :: semantic.scalarFields.filter fun old =>
          old.width != slotIndex || old.offset != byteOffset }
  let replacement : HeapCell := { cell with object := .ctor updatedSemantic }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      obtain ⟨result, targetHeader, operation, targetRawRead, targetFrame,
          finalValid⟩ :=
        objectRelated.writeScalarUInt16Field_targetFrame related.frontier
          slotIndex byteOffset value slotIndexEq fieldFits
      obtain ⟨localResult, localOperation, objectAfter⟩ :=
        objectRelated.writeScalarUInt16Field slotIndex byteOffset value
          retainedDisjoint slotIndexEq fieldFits
      rw [operation] at localOperation
      have resultMatch := Except.ok.inj localOperation
      subst localResult
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.constructor descriptor (by rfl)
          (by simpa [updatedSemantic] using objectAfter)
          (by rw [targetFrame.targetLiveHeader]; exact headerRead) headerKind
        · simpa [replacement] using refCount
        · simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          targetFrame finalValid targetAfter
      have sourceOperation :
          Fir.LeanIR.Impure.setScalarField runtime (.object (.heap location))
            slotIndex byteOffset (.scalar (.uint16 value)) = .ok nextRuntime := by
        simp [Fir.LeanIR.Impure.setScalarField, modifyConstructor, getConstructor,
          getLiveCell, Bind.bind, Except.bind, found, live, objectEq]
        simp only [pure, Except.pure]
        change setCell runtime location replacement = .ok nextRuntime
        exact semanticSet
      exact ⟨result, nextRuntime, operation, sourceOperation, heapRelated⟩
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- Whole-heap refinement for a successful packed `UInt8` mutation. -/
theorem LiveHeapRel.writeScalarUInt8Field_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (slotIndex byteOffset : Nat) (value : UInt8)
    (replaced : semantic.scalarFields.filter (fun old =>
      old.width != slotIndex || old.offset != byteOffset) = [])
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 1 ≤ info.ssize) :
    ∃ result nextRuntime,
      Fir.Wasm.Concrete.writeScalarUInt8Field state address slotIndex byteOffset
        value = .ok result ∧
      Fir.LeanIR.Impure.setScalarField runtime (.object (.heap location))
        slotIndex byteOffset (.scalar (.uint8 value)) = .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let updatedSemantic : ConstructorObject := {
    semantic with
      scalarFields := {
        width := slotIndex
        offset := byteOffset
        value := .uint8 value } :: semantic.scalarFields.filter fun old =>
          old.width != slotIndex || old.offset != byteOffset }
  let replacement : HeapCell := { cell with object := .ctor updatedSemantic }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      obtain ⟨result, targetHeader, operation, targetRawRead, targetFrame,
          finalValid⟩ :=
        objectRelated.writeScalarUInt8Field_targetFrame related.frontier
          slotIndex byteOffset value slotIndexEq fieldFits
      obtain ⟨localResult, localOperation, objectAfter⟩ :=
        objectRelated.writeScalarUInt8Field slotIndex byteOffset value replaced
          slotIndexEq fieldFits
      rw [operation] at localOperation
      have resultMatch := Except.ok.inj localOperation
      subst localResult
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.constructor descriptor (by rfl)
          (by simpa [updatedSemantic] using objectAfter)
          (by rw [targetFrame.targetLiveHeader]; exact headerRead) headerKind
        · simpa [replacement] using refCount
        · simpa [replacement] using persistent
        · simpa [replacement] using cellLive
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_targetMutation mapped found descriptor targetRawRead
          targetFrame finalValid targetAfter
      have sourceOperation :
          Fir.LeanIR.Impure.setScalarField runtime (.object (.heap location))
            slotIndex byteOffset (.scalar (.uint8 value)) = .ok nextRuntime := by
        simp [Fir.LeanIR.Impure.setScalarField, modifyConstructor, getConstructor,
          getLiveCell, Bind.bind, Except.bind, found, live, objectEq]
        simp only [pure, Except.pure]
        change setCell runtime location replacement = .ok nextRuntime
        exact semanticSet
      exact ⟨result, nextRuntime, operation, sourceOperation, heapRelated⟩
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

end Fir.Wasm.Concrete
