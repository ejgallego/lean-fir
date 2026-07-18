import Fir.Wasm.Concrete.SharingCorrectness
import Fir.Wasm.Concrete.HeaderCorrectness
import Fir.Wasm.Concrete.ConstructorAllocationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Ownership checks see both physical encodings of a semantic tagged value
as tagged: checked increments are no-ops and unchecked increments fail with
the source `expectedHeapReference` fault. -/
theorem LiveHeapRel.incrementReference_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload)
    (amount : Nat) (check : Bool) :
    incrementReference state word amount check =
      if check then .ok state else .error (.source .expectedHeapReference) := by
  cases tagged with
  | immediate actualPayload fits =>
      unfold incrementReference
      simp [Word32.classify_encodeImmediate]
      cases check <;> rfl
  | promoted found =>
      have promoted := related.promoted payload word found
      obtain ⟨header, headerRead, headerKind, persistent, _, marker, _, _⟩ :=
        promoted.header
      have addressHeap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state word header
          headerRead).1
      have isPromoted : header.isPromotedTag = true := by
        unfold Header.isPromotedTag
        rw [headerKind, persistent, marker]
        decide
      unfold incrementReference
      rw [addressHeap]
      simp only
      rw [headerRead]
      simp only [Bind.bind, Except.bind, liftMemory]
      rw [if_pos isPromoted]
      cases check <;> rfl

/-- Checked decrements retain the same tagged-value split as increments. -/
theorem LiveHeapRel.decrementReferenceOnce_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload)
    (check : Bool) :
    decrementReferenceOnce state word check =
      if check then .ok state else .error (.source .expectedHeapReference) := by
  cases tagged with
  | immediate actualPayload fits =>
      simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
      simp [Word32.classify_encodeImmediate]
      cases check <;> rfl
  | promoted found =>
      have promoted := related.promoted payload word found
      obtain ⟨header, headerRead, headerKind, persistent, _, marker, _, _⟩ :=
        promoted.header
      have addressHeap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state word header
          headerRead).1
      have isPromoted : header.isPromotedTag = true := by
        unfold Header.isPromotedTag
        rw [headerKind, persistent, marker]
        decide
      simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
      rw [addressHeap]
      simp only
      rw [headerRead]
      simp only [Bind.bind, Except.bind, liftMemory]
      rw [if_pos isPromoted]
      cases check <;> rfl

/-- Shared header-level postcondition for ordinary successful increments. It
separates the common-header write from object-kind-specific payload framing. -/
theorem incrementReference_header
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (notPromoted : header.isPromotedTag = false)
    (ordinary : header.persistent = false)
    (oldCount amount : Nat)
    (refCount : header.refCount.toNat = oldCount)
    (fits : oldCount + amount < UInt32.size)
    (check : Bool) :
    ∃ result updatedHeader memory,
      incrementReference state address amount check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount + amount) } ∧
      result = { state with memory } ∧
      updatedHeader.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  let updatedHeader : Header :=
    { header with refCount := UInt32.ofNat (oldCount + amount) }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : incrementReference state address amount check = .ok result := by
    unfold incrementReference
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [ordinary])]
    rw [refCount]
    rw [uint32Field_eq_ok "reference count" (oldCount + amount) fits]
    unfold writeLiveHeader
    change (do
      let nextMemory ← liftMemory (updatedHeader.write state.memory address)
      return ({ state with memory := nextMemory } : MemoryState)) = .ok result
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have finalValid : result.FrontierInvariant :=
    valid.writeHeader headerOwned headerWrite
  exact ⟨result, updatedHeader, memory, operation, rfl, rfl, headerWrite,
    finalValid, headerReadAfter⟩

/-- Object-independent count replacement at the common-header boundary. It
exposes the exact header write so each payload decoder can prove its own frame
once and share that proof between increment and decrement. -/
theorem writeReferenceCount_header
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (nextCount : UInt32) :
    ∃ result updatedHeader memory,
      writeLiveHeader state address updatedHeader = .ok result ∧
      updatedHeader = { header with refCount := nextCount } ∧
      result = { state with memory } ∧
      updatedHeader.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  let updatedHeader : Header := { header with refCount := nextCount }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : writeLiveHeader state address updatedHeader = .ok result := by
    unfold writeLiveHeader
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have finalValid : result.FrontierInvariant :=
    valid.writeHeader headerOwned headerWrite
  exact ⟨result, updatedHeader, memory, operation, rfl, rfl, headerWrite,
    finalValid, headerReadAfter⟩

/-- A common-header rewrite leaves the recursive natural payload decoder
unchanged because every limb starts after the 32-byte header. -/
theorem Header.readNaturalLimbs_of_write_eq_ok
    (before after : LinearMemory) (address : Word32) (updatedHeader : Header)
    (index count : Nat)
    (headerInBounds : address.value + headerBytes ≤ before.size)
    (written : updatedHeader.write before address = .ok after) :
    readNaturalLimbs after address.value index count =
      readNaturalLimbs before address.value index count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      unfold readNaturalLimbs LinearMemory.readUInt64
      rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader
        (address.value + headerBytes + target.semanticSlotBytes * index)
        headerInBounds written (.inr (by omega))]
      rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader
        (address.value + headerBytes + target.semanticSlotBytes * index + 4)
        headerInBounds written (.inr (by omega))]
      rw [ih (index + 1)]

theorem Header.readUInt16_of_write_eq_ok_payload
    (before after : LinearMemory) (address : Word32) (updatedHeader : Header)
    (other : Nat)
    (headerInBounds : address.value + headerBytes ≤ before.size)
    (written : updatedHeader.write before address = .ok after)
    (payload : address.value + headerBytes ≤ other) :
    after.readUInt16 other = before.readUInt16 other := by
  unfold LinearMemory.readUInt16
  rw [Header.readByte_of_write_eq_ok_other before after address updatedHeader other
    headerInBounds written (.inr payload)]
  rw [Header.readByte_of_write_eq_ok_other before after address updatedHeader (other + 1)
    headerInBounds written (.inr (by omega))]

theorem Header.readUInt64_of_write_eq_ok_payload
    (before after : LinearMemory) (address : Word32) (updatedHeader : Header)
    (other : Nat)
    (headerInBounds : address.value + headerBytes ≤ before.size)
    (written : updatedHeader.write before address = .ok after)
    (payload : address.value + headerBytes ≤ other) :
    after.readUInt64 other = before.readUInt64 other := by
  unfold LinearMemory.readUInt64
  rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader other
    headerInBounds written (.inr payload)]
  rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader (other + 4)
    headerInBounds written (.inr (by omega))]

theorem Header.readWord32_of_write_eq_ok_payload
    (before after : LinearMemory) (address : Word32) (updatedHeader : Header)
    (other : Nat)
    (headerInBounds : address.value + headerBytes ≤ before.size)
    (written : updatedHeader.write before address = .ok after)
    (payload : address.value + headerBytes ≤ other) :
    after.readWord32 other = before.readWord32 other := by
  unfold LinearMemory.readWord32
  rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader other
    headerInBounds written (.inr payload)]

/-- Rewriting only a constructor's reference count frames every representation
region described by its immutable allocation metadata. -/
theorem ConstructorObjectRel.writeReferenceCount
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject} {header : Header}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (headerRead : state.readLiveHeader address = .ok header)
    (valid : state.FrontierInvariant)
    (nextCount : UInt32) :
    ∃ result updatedHeader,
      writeLiveHeader state address updatedHeader = .ok result ∧
      updatedHeader = { header with refCount := nextCount } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      ConstructorObjectRel result witness address info fieldKinds semantic := by
  obtain ⟨objectHeader, objectHeaderRead, headerKind, allocationBytes, ordinary,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header
  rw [headerRead] at objectHeaderRead
  cases objectHeaderRead
  obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
      headerWrite, finalValid, headerReadAfter⟩ :=
    writeReferenceCount_header valid headerRead related.headerOwned nextCount
  subst updatedHeader
  subst result
  let updatedHeader : Header :=
    { header with refCount := nextCount }
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans related.headerOwned valid.cursorInBounds
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead).1
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap]
    rw [headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have constructorHeaderAfter :
      readConstructorHeader ({ state with memory } : MemoryState) address =
        .ok updatedHeader := by
    unfold readConstructorHeader
    simp [heap]
    rw [headerReadAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, updatedHeader, headerKind]
    rfl
  have scalarFieldsAfter : ∀ field, field ∈ semantic.scalarFields →
      match field.value with
      | .uint8 value =>
          field.width = info.size + info.usize ∧
          field.offset + 1 ≤ info.ssize ∧
          readScalarUInt8Field ({ state with memory } : MemoryState) address
            field.width field.offset = .ok value
      | .uint16 value =>
          field.width = info.size + info.usize ∧
          field.offset + 2 ≤ info.ssize ∧
          readScalarUInt16Field ({ state with memory } : MemoryState) address
            field.width field.offset = .ok value
      | .uint32 value =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field ({ state with memory } : MemoryState) address
            field.width field.offset = .ok value
      | .uint64 value =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field ({ state with memory } : MemoryState) address
            field.width field.offset = .ok value := by
    intro field member
    have beforeField := related.semanticScalarFields field member
    cases valueEq : field.value with
    | uint8 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have operationEq :
            readScalarUInt8Field ({ state with memory } : MemoryState) address
                field.width field.offset =
              readScalarUInt8Field state address field.width field.offset := by
          unfold readScalarUInt8Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddressBefore : scalarFieldAddress address header field.width
              field.offset 1 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          have scalarAddressAfter : scalarFieldAddress address updatedHeader field.width
              field.offset 1 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [updatedHeader, widthEq, objectCount, usizeCount, fieldFits,
              scalarCount]
            rfl
          rw [scalarAddressAfter, scalarAddressBefore]
          change liftMemory (memory.readByte (address.value + headerBytes +
            target.semanticSlotBytes * field.width + field.offset)) =
              liftMemory (state.memory.readByte (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset))
          rw [Header.readByte_of_write_eq_ok_other state.memory memory address
            { header with refCount := nextCount }
            (address.value + headerBytes + target.semanticSlotBytes * field.width +
              field.offset) headerInBounds headerWrite (.inr (by omega))]
        rw [operationEq]
        exact readBefore
    | uint16 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have operationEq :
            readScalarUInt16Field ({ state with memory } : MemoryState) address
                field.width field.offset =
              readScalarUInt16Field state address field.width field.offset := by
          unfold readScalarUInt16Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddressBefore : scalarFieldAddress address header field.width
              field.offset 2 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          have scalarAddressAfter : scalarFieldAddress address updatedHeader field.width
              field.offset 2 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [updatedHeader, widthEq, objectCount, usizeCount, fieldFits,
              scalarCount]
            rfl
          rw [scalarAddressAfter, scalarAddressBefore]
          change liftMemory (memory.readUInt16 (address.value + headerBytes +
            target.semanticSlotBytes * field.width + field.offset)) =
              liftMemory (state.memory.readUInt16 (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset))
          rw [Header.readUInt16_of_write_eq_ok_payload state.memory memory address
            { header with refCount := nextCount }
            (address.value + headerBytes + target.semanticSlotBytes * field.width +
              field.offset) headerInBounds headerWrite (by omega)]
        rw [operationEq]
        exact readBefore
    | uint32 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have operationEq :
            readScalarUInt32Field ({ state with memory } : MemoryState) address
                field.width field.offset =
              readScalarUInt32Field state address field.width field.offset := by
          unfold readScalarUInt32Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddressBefore : scalarFieldAddress address header field.width
              field.offset 4 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          have scalarAddressAfter : scalarFieldAddress address updatedHeader field.width
              field.offset 4 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [updatedHeader, widthEq, objectCount, usizeCount, fieldFits,
              scalarCount]
            rfl
          rw [scalarAddressAfter, scalarAddressBefore]
          change liftMemory (memory.readUInt32 (address.value + headerBytes +
            target.semanticSlotBytes * field.width + field.offset)) =
              liftMemory (state.memory.readUInt32 (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset))
          rw [Header.readUInt32_of_write_eq_ok_other state.memory memory address
            { header with refCount := nextCount }
            (address.value + headerBytes + target.semanticSlotBytes * field.width +
              field.offset) headerInBounds headerWrite (.inr (by omega))]
        rw [operationEq]
        exact readBefore
    | uint64 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have operationEq :
            readScalarUInt64Field ({ state with memory } : MemoryState) address
                field.width field.offset =
              readScalarUInt64Field state address field.width field.offset := by
          unfold readScalarUInt64Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddressBefore : scalarFieldAddress address header field.width
              field.offset 8 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          have scalarAddressAfter : scalarFieldAddress address updatedHeader field.width
              field.offset 8 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [updatedHeader, widthEq, objectCount, usizeCount, fieldFits,
              scalarCount]
            rfl
          rw [scalarAddressAfter, scalarAddressBefore]
          change liftMemory (memory.readUInt64 (address.value + headerBytes +
            target.semanticSlotBytes * field.width + field.offset)) =
              liftMemory (state.memory.readUInt64 (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset))
          rw [Header.readUInt64_of_write_eq_ok_payload state.memory memory address
            { header with refCount := nextCount }
            (address.value + headerBytes + target.semanticSlotBytes * field.width +
              field.offset) headerInBounds headerWrite (by omega)]
        rw [operationEq]
        exact readBefore
  refine ⟨{ state with memory }, updatedHeader, operation, rfl, finalValid,
    headerReadAfter, ?_⟩
  refine {
    header := ⟨updatedHeader, headerReadAfter,
      by simpa [updatedHeader] using headerKind,
      by simpa [updatedHeader] using allocationBytes,
      by simpa [updatedHeader] using ordinary,
      by simpa [updatedHeader] using tag,
      by simpa [updatedHeader] using objectCount,
      by simpa [updatedHeader] using usizeCount,
      by simpa [updatedHeader] using scalarCount⟩
    headerOwned := related.headerOwned
    extent := by simpa [updatedHeader] using related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := scalarFieldsAfter
    fieldKindsSize := related.fieldKindsSize
    objectFields := ?_
    usizeFields := ?_ }
  · intro index kind value kindAt valueAt
    obtain ⟨word, readBefore, valueRelated⟩ :=
      related.objectFields index kind value kindAt valueAt
    have operationEq :
        readObjectField ({ state with memory } : MemoryState) address index =
          readObjectField state address index := by
      unfold readObjectField
      rw [constructorHeaderAfter, constructorHeaderBefore]
      simp only [Bind.bind, Except.bind, updatedHeader]
      rw [Header.readWord32_of_write_eq_ok_payload state.memory memory address
        { header with refCount := nextCount }
        (address.value + headerBytes + target.semanticSlotBytes * index)
        headerInBounds headerWrite (by omega)]
      rw [Header.readUInt32_of_write_eq_ok_other state.memory memory address
        { header with refCount := nextCount }
        (address.value + headerBytes + target.semanticSlotBytes * index + 4)
        headerInBounds headerWrite (.inr (by omega))]
    exact ⟨word, by rw [operationEq]; exact readBefore, valueRelated⟩
  · intro index value valueAt
    have operationEq :
        readUSizeField ({ state with memory } : MemoryState) address index =
          readUSizeField state address index := by
      unfold readUSizeField
      rw [constructorHeaderAfter, constructorHeaderBefore]
      simp only [Bind.bind, Except.bind, updatedHeader]
      rw [Header.readUInt64_of_write_eq_ok_payload state.memory memory address
        { header with refCount := nextCount }
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + index)) headerInBounds headerWrite (by omega)]
    rw [operationEq]
    exact related.usizeFields index value valueAt

/-- Constructor increment is the ordinary runtime branch followed by the
shared constructor header-frame theorem. -/
theorem ConstructorObjectRel.incrementReference
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject} {header : Header}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (headerRead : state.readLiveHeader address = .ok header)
    (valid : state.FrontierInvariant)
    (oldCount amount : Nat)
    (refCount : header.refCount.toNat = oldCount)
    (fits : oldCount + amount < UInt32.size)
    (check : Bool) :
    ∃ result updatedHeader,
      Fir.Wasm.Concrete.incrementReference state address amount check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount + amount) } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      ConstructorObjectRel result witness address info fieldKinds semantic := by
  obtain ⟨result, updatedHeader, write, updatedEq, finalValid, headerReadAfter,
      objectAfter⟩ :=
    related.writeReferenceCount headerRead valid
      (UInt32.ofNat (oldCount + amount))
  obtain ⟨objectHeader, objectHeaderRead, headerKind, _, ordinary, _, _, _, _⟩ :=
    related.header
  rw [headerRead] at objectHeaderRead
  cases objectHeaderRead
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead).1
  have notPromoted : header.isPromotedTag = false := by
    have different : (ObjectKind.constructor == ObjectKind.natural) = false := by decide
    simp [Header.isPromotedTag, headerKind, different]
  have operation : Fir.Wasm.Concrete.incrementReference state address amount check =
      .ok result := by
    unfold Fir.Wasm.Concrete.incrementReference
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [ordinary])]
    rw [refCount]
    rw [uint32Field_eq_ok "reference count" (oldCount + amount) fits]
    simpa [updatedEq] using write
  exact ⟨result, updatedHeader, operation, updatedEq, finalValid,
    headerReadAfter, objectAfter⟩

/-- Above one, constructor decrement uses the same payload-frame theorem as
increment while selecting the decrement engine's nonrecursive branch. -/
theorem ConstructorObjectRel.decrementReferenceOnce_above_one
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject} {header : Header}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (headerRead : state.readLiveHeader address = .ok header)
    (valid : state.FrontierInvariant)
    (oldCount : Nat) (refCount : header.refCount.toNat = oldCount)
    (oneLt : 1 < oldCount) (check : Bool) :
    ∃ result updatedHeader,
      decrementReferenceOnce state address check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount - 1) } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      ConstructorObjectRel result witness address info fieldKinds semantic := by
  obtain ⟨result, updatedHeader, write, updatedEq, finalValid, headerReadAfter,
      objectAfter⟩ :=
    related.writeReferenceCount headerRead valid (UInt32.ofNat (oldCount - 1))
  obtain ⟨objectHeader, objectHeaderRead, headerKind, _, ordinary, _, _, _, _⟩ :=
    related.header
  rw [headerRead] at objectHeaderRead
  cases objectHeaderRead
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead).1
  have notPromoted : header.isPromotedTag = false := by
    have different : (ObjectKind.constructor == ObjectKind.natural) = false := by decide
    simp [Header.isPromotedTag, headerKind, different]
  have refCountNe : header.refCount ≠ 0 := by
    intro zero
    rw [zero] at refCount
    simp at refCount
    omega
  have operation : decrementReferenceOnce state address check = .ok result := by
    simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [ordinary])]
    rw [if_neg (by simpa using refCountNe)]
    rw [refCount, if_pos oneLt]
    simpa [updatedEq] using write
  exact ⟨result, updatedHeader, operation, updatedEq, finalValid,
    headerReadAfter, objectAfter⟩

/-- Incrementing one ordinary boxed object's header preserves its canonical
payload decoder while changing exactly the mutable reference count. -/
theorem BoxedObjectRel.incrementReference
    {state : MemoryState} {address : Word32} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {header : Header}
    (related : BoxedObjectRel state address kind scalar header)
    (valid : state.FrontierInvariant)
    (oldCount amount : Nat)
    (refCount : header.refCount.toNat = oldCount)
    (fits : oldCount + amount < UInt32.size)
    (check : Bool) :
    ∃ result updatedHeader,
      Fir.Wasm.Concrete.incrementReference state address amount check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount + amount) } ∧
      result.FrontierInvariant ∧
      BoxedObjectRel result address kind scalar updatedHeader := by
  obtain ⟨heap, decodedBefore, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      related.headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size := by
    omega
  let updatedHeader : Header :=
    { header with refCount := UInt32.ofNat (oldCount + amount) }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have notPromoted : header.isPromotedTag = false := by
    have different : (ObjectKind.boxed == ObjectKind.natural) = false := by decide
    simp [Header.isPromotedTag, related.headerKind, different]
  have operation : Fir.Wasm.Concrete.incrementReference state address amount check =
      .ok result := by
    unfold Fir.Wasm.Concrete.incrementReference
    rw [heap]
    simp only
    rw [related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [related.ordinary])]
    rw [refCount]
    rw [uint32Field_eq_ok "reference count" (oldCount + amount) fits]
    unfold writeLiveHeader
    change (do
      let nextMemory ← liftMemory (updatedHeader.write state.memory address)
      return ({ state with memory := nextMemory } : MemoryState)) = .ok result
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have finalValid : result.FrontierInvariant := by
    exact valid.writeHeader related.headerOwned headerWrite
  have payloadRead : memory.readUInt64 (address.value + headerBytes) =
      state.memory.readUInt64 (address.value + headerBytes) := by
    unfold LinearMemory.readUInt64
    rw [Header.readUInt32_of_write_eq_ok_other state.memory memory address
      updatedHeader (address.value + headerBytes) headerInBounds headerWrite (by omega)]
    rw [Header.readUInt32_of_write_eq_ok_other state.memory memory address
      updatedHeader (address.value + headerBytes + 4) headerInBounds headerWrite
        (by omega)]
  have decoderEq :
      readBoxedScalar result kind address = readBoxedScalar state kind address := by
    unfold readBoxedScalar
    rw [heap]
    simp only
    rw [headerReadAfter, related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    have boxed : (header.kind == ObjectKind.boxed) = true := by
      rw [related.headerKind]
      decide
    have boxedAfter : (updatedHeader.kind == ObjectKind.boxed) = true := by
      simpa [updatedHeader] using boxed
    rw [boxedAfter]
    simp
    unfold readHeapBoxedScalar
    simp only [updatedHeader]
    rw [payloadRead]
  refine ⟨result, updatedHeader, operation, rfl, finalValid, ?_⟩
  exact {
    scalarKind := related.scalarKind
    headerRead := headerReadAfter
    headerKind := by simpa [updatedHeader] using related.headerKind
    ordinary := by simpa [updatedHeader] using related.ordinary
    allocationBytes := by simpa [updatedHeader] using related.allocationBytes
    kindCode := by simpa [updatedHeader] using related.kindCode
    payloadBytes := by simpa [updatedHeader] using related.payloadBytes
    reserved2 := by simpa [updatedHeader] using related.reserved2
    reserved3 := by simpa [updatedHeader] using related.reserved3
    headerOwned := related.headerOwned
    extent := related.extent
    decoded := by rw [decoderEq]; exact related.decoded }

/-- Object-independent common-header count replacement, specialized here to
the canonical boxed payload decoder. -/
theorem BoxedObjectRel.writeReferenceCount
    {state : MemoryState} {address : Word32} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {header : Header}
    (related : BoxedObjectRel state address kind scalar header)
    (valid : state.FrontierInvariant) (nextCount : UInt32) :
    ∃ result updatedHeader,
      writeLiveHeader state address updatedHeader = .ok result ∧
      updatedHeader = { header with refCount := nextCount } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      BoxedObjectRel result address kind scalar updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      related.headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans related.headerOwned valid.cursorInBounds
  let updatedHeader : Header := { header with refCount := nextCount }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : writeLiveHeader state address updatedHeader = .ok result := by
    unfold writeLiveHeader
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have finalValid : result.FrontierInvariant :=
    valid.writeHeader related.headerOwned headerWrite
  have payloadRead : memory.readUInt64 (address.value + headerBytes) =
      state.memory.readUInt64 (address.value + headerBytes) :=
    Header.readUInt64_of_write_eq_ok_payload state.memory memory address updatedHeader
      (address.value + headerBytes) headerInBounds headerWrite (by omega)
  have decoderEq :
      readBoxedScalar result kind address = readBoxedScalar state kind address := by
    unfold readBoxedScalar
    rw [heap]
    simp only
    rw [headerReadAfter, related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    have boxed : (header.kind == ObjectKind.boxed) = true := by
      rw [related.headerKind]
      decide
    have boxedAfter : (updatedHeader.kind == ObjectKind.boxed) = true := by
      simpa [updatedHeader] using boxed
    rw [boxedAfter]
    simp
    unfold readHeapBoxedScalar
    simp only [updatedHeader]
    rw [payloadRead]
  refine ⟨result, updatedHeader, operation, rfl, finalValid, headerReadAfter, ?_⟩
  exact {
    scalarKind := related.scalarKind
    headerRead := headerReadAfter
    headerKind := by simpa [updatedHeader] using related.headerKind
    ordinary := by simpa [updatedHeader] using related.ordinary
    allocationBytes := by simpa [updatedHeader] using related.allocationBytes
    kindCode := by simpa [updatedHeader] using related.kindCode
    payloadBytes := by simpa [updatedHeader] using related.payloadBytes
    reserved2 := by simpa [updatedHeader] using related.reserved2
    reserved3 := by simpa [updatedHeader] using related.reserved3
    headerOwned := related.headerOwned
    extent := related.extent
    decoded := by rw [decoderEq]; exact related.decoded }

/-- Above one, decrement is precisely a live common-header rewrite. -/
theorem BoxedObjectRel.decrementReferenceOnce_above_one
    {state : MemoryState} {address : Word32} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {header : Header}
    (related : BoxedObjectRel state address kind scalar header)
    (valid : state.FrontierInvariant) (oldCount : Nat)
    (refCount : header.refCount.toNat = oldCount) (oneLt : 1 < oldCount)
    (check : Bool) :
    ∃ result updatedHeader,
      decrementReferenceOnce state address check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount - 1) } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      BoxedObjectRel result address kind scalar updatedHeader := by
  obtain ⟨result, updatedHeader, write, updatedEq, finalValid, headerReadAfter,
      objectAfter⟩ := related.writeReferenceCount valid (UInt32.ofNat (oldCount - 1))
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      related.headerRead).1
  have notPromoted : header.isPromotedTag = false := by
    have different : (ObjectKind.boxed == ObjectKind.natural) = false := by decide
    simp [Header.isPromotedTag, related.headerKind, different]
  have refCountNe : header.refCount ≠ 0 := by
    intro zero
    rw [zero] at refCount
    simp at refCount
    omega
  have operation : decrementReferenceOnce state address check = .ok result := by
    simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
    rw [heap]
    simp only
    rw [related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [related.ordinary])]
    rw [if_neg (by simpa using refCountNe)]
    rw [refCount, if_pos oneLt]
    simpa [updatedEq] using write
  exact ⟨result, updatedHeader, operation, updatedEq, finalValid, headerReadAfter,
    objectAfter⟩

/-- First successful decrement refinement: a live box above one remains live,
retains its scalar payload, and lowers the semantic/concrete count together. -/
theorem LiveCellRel.decrementReferenceOnce_boxed_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (boxedCell : ∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
      cell.object = .boxed kind.semanticType scalar.semanticValue)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
      rw [objectEq] at boxedEq
      contradiction
  | @boxed kind scalar header _ descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨result, updatedHeader, operation, updatedEq, finalValid,
          headerReadAfter, objectAfter⟩ :=
        objectRelated.decrementReferenceOnce_above_one valid cell.rc refCount oneLt check
      subst updatedHeader
      have nextFits : cell.rc - 1 < UInt32.size := by
        have oldFits := UInt32.toNat_lt_size header.refCount
        rw [refCount] at oldFits
        omega
      refine ⟨result, operation, finalValid, ?_⟩
      apply LiveCellRel.boxed descriptor (by simpa using objectEq) objectAfter
      · simp only
        exact UInt32.toNat_ofNat_of_lt' nextFits
      · simpa using persistent
      · simpa using live
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
      rw [objectEq] at boxedEq
      contradiction

/-- Local live-cell refinement for the first W6.3 ownership case. -/
theorem LiveCellRel.incrementReference_boxed
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (boxedCell : ∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
      cell.object = .boxed kind.semanticType scalar.semanticValue)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc + amount } := by
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
      rw [objectEq] at boxedEq
      contradiction
  | boxed descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨result, updatedHeader, operation, updatedEq, finalValid,
        objectAfter⟩ := objectRelated.incrementReference valid cell.rc amount
          refCount fits check
      subst updatedHeader
      refine ⟨result, operation, finalValid, ?_⟩
      apply LiveCellRel.boxed descriptor (by simpa using objectEq) objectAfter
      · simp only
        exact UInt32.toNat_ofNat_of_lt' fits
      · simpa using persistent
      · simpa using live
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
      rw [objectEq] at boxedEq
      contradiction

/-- Constructor increments preserve every decoded payload region and update
the enclosing live-cell ownership equality. -/
theorem LiveCellRel.incrementReference_constructor
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (constructorCell : ∃ semantic : ConstructorObject, cell.object = .ctor semantic)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc + amount } := by
  cases related with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
        persistent live =>
      obtain ⟨result, updatedHeader, operation, updatedEq, finalValid,
          headerReadAfter, objectAfter⟩ :=
        objectRelated.incrementReference headerRead valid cell.rc amount refCount fits check
      subst updatedHeader
      refine ⟨result, operation, finalValid, ?_⟩
      apply LiveCellRel.constructor descriptor (by simpa using objectEq) objectAfter
        headerReadAfter
      · simpa using headerKind
      · simp only
        exact UInt32.toNat_ofNat_of_lt' fits
      · simpa using persistent
      · simpa using live
  | boxed _ objectEq _ _ _ _ =>
      obtain ⟨semantic, constructorEq⟩ := constructorCell
      rw [objectEq] at constructorEq
      contradiction
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨semantic, constructorEq⟩ := constructorCell
      rw [objectEq] at constructorEq
      contradiction

/-- Constructor cells above one remain live and preserve every decoded field
while source and concrete ownership counts both decrease by one. -/
theorem LiveCellRel.decrementReferenceOnce_constructor_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (constructorCell : ∃ semantic : ConstructorObject, cell.object = .ctor semantic)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  cases related with
  | @constructor info fieldKinds semantic header _ descriptor objectEq objectRelated
        headerRead headerKind refCount persistent live =>
      obtain ⟨result, updatedHeader, operation, updatedEq, finalValid,
          headerReadAfter, objectAfter⟩ :=
        objectRelated.decrementReferenceOnce_above_one headerRead valid cell.rc refCount
          oneLt check
      subst updatedHeader
      have nextFits : cell.rc - 1 < UInt32.size := by
        have oldFits := UInt32.toNat_lt_size header.refCount
        rw [refCount] at oldFits
        omega
      refine ⟨result, operation, finalValid, ?_⟩
      apply LiveCellRel.constructor descriptor (by simpa using objectEq) objectAfter
        headerReadAfter
      · simpa using headerKind
      · simp only
        exact UInt32.toNat_ofNat_of_lt' nextFits
      · simpa using persistent
      · simpa using live
  | boxed _ objectEq _ _ _ _ =>
      obtain ⟨semantic, constructorEq⟩ := constructorCell
      rw [objectEq] at constructorEq
      contradiction
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨semantic, constructorEq⟩ := constructorCell
      rw [objectEq] at constructorEq
      contradiction

/-- Natural limbs frame across a common-header increment, yielding the same
decoded semantic natural at the incremented live-cell count. -/
theorem LiveCellRel.incrementReference_natural
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (naturalCell : ∃ value : Nat, cell.object = .natural value)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc + amount } := by
  have headerOwned := related.headerOwned
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      obtain ⟨value, naturalEq⟩ := naturalCell
      rw [objectEq] at naturalEq
      contradiction
  | boxed _ objectEq _ _ _ _ =>
      obtain ⟨value, naturalEq⟩ := naturalCell
      rw [objectEq] at naturalEq
      contradiction
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      have notPromoted : Header.isPromotedTag header = false := by
        simp [Header.isPromotedTag, headerKind, ordinary]
      obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
          headerWrite, finalValid, headerReadAfter⟩ :=
        incrementReference_header valid headerRead headerOwned notPromoted ordinary
          cell.rc amount refCount fits check
      subst updatedHeader
      subst result
      have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
        Nat.le_trans headerOwned valid.cursorInBounds
      have decoderEq :
          readNatural ({ state with memory } : MemoryState) address =
            readNatural state address := by
        obtain ⟨heap, _, _, _, _, _⟩ :=
          MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead
        unfold readNatural
        rw [heap]
        simp only
        rw [headerReadAfter, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        simp [headerKind, ordinary, marker]
        rw [Header.readNaturalLimbs_of_write_eq_ok state.memory memory address
          { header with refCount := UInt32.ofNat (cell.rc + amount) }
          0 _ headerInBounds headerWrite]
      refine ⟨{ state with memory }, operation, finalValid, ?_⟩
      apply LiveCellRel.natural descriptor (by simpa using objectEq) headerReadAfter
      · simpa using headerKind
      · simpa using ordinary
      · simpa using marker
      · simpa using extent
      · simpa using limbsFit
      · rw [decoderEq]
        exact decoded
      · simp only
        exact UInt32.toNat_ofNat_of_lt' fits
      · simpa using persistent
      · simpa using live

/-- Natural cells above one retain their complete limb decoder while the
common header and semantic cell counts decrease together. -/
theorem LiveCellRel.decrementReferenceOnce_natural_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (naturalCell : ∃ value : Nat, cell.object = .natural value)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  have headerOwned := related.headerOwned
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      obtain ⟨value, naturalEq⟩ := naturalCell
      rw [objectEq] at naturalEq
      contradiction
  | boxed _ objectEq _ _ _ _ =>
      obtain ⟨value, naturalEq⟩ := naturalCell
      rw [objectEq] at naturalEq
      contradiction
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      have notPromoted : Header.isPromotedTag header = false := by
        simp [Header.isPromotedTag, headerKind, ordinary]
      obtain ⟨result, updatedHeader, memory, write, updatedEq, resultEq,
          headerWrite, finalValid, headerReadAfter⟩ :=
        writeReferenceCount_header valid headerRead headerOwned
          (UInt32.ofNat (cell.rc - 1))
      subst updatedHeader
      subst result
      obtain ⟨heap, _, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
      have refCountNe : header.refCount ≠ 0 := by
        intro zero
        rw [zero] at refCount
        simp at refCount
        omega
      have operation :
          decrementReferenceOnce state address check = .ok { state with memory } := by
        simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
        rw [heap]
        simp only
        rw [headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        rw [if_neg (by simp [notPromoted])]
        rw [if_neg (by simp [ordinary])]
        rw [if_neg (by simpa using refCountNe)]
        rw [refCount, if_pos oneLt]
        exact write
      have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
        Nat.le_trans headerOwned valid.cursorInBounds
      have decoderEq :
          readNatural ({ state with memory } : MemoryState) address =
            readNatural state address := by
        unfold readNatural
        rw [heap]
        simp only
        rw [headerReadAfter, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        simp [headerKind, ordinary, marker]
        rw [Header.readNaturalLimbs_of_write_eq_ok state.memory memory address
          { header with refCount := UInt32.ofNat (cell.rc - 1) }
          0 _ headerInBounds headerWrite]
      have nextFits : cell.rc - 1 < UInt32.size := by
        have oldFits := UInt32.toNat_lt_size header.refCount
        rw [refCount] at oldFits
        omega
      refine ⟨{ state with memory }, operation, finalValid, ?_⟩
      apply LiveCellRel.natural descriptor (by simpa using objectEq) headerReadAfter
      · simpa using headerKind
      · simpa using ordinary
      · simpa using marker
      · simpa using extent
      · simpa using limbsFit
      · rw [decoderEq]
        exact decoded
      · simp only
        exact UInt32.toNat_ofNat_of_lt' nextFits
      · simpa using persistent
      · simpa using live

/-- Complete local increment theorem for every live-cell representation in
the current W6 heap relation. -/
theorem LiveCellRel.incrementReference
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      Fir.Wasm.Concrete.incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc + amount } := by
  cases related with
  | @constructor info fieldKinds semantic header _ descriptor objectEq objectRelated
        headerRead headerKind refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .constructor descriptor objectEq objectRelated headerRead headerKind refCount
          persistent live
      exact localRelated.incrementReference_constructor ⟨semantic, objectEq⟩ valid
        amount fits check
  | @boxed kind scalar header _ descriptor objectEq objectRelated refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .boxed descriptor objectEq objectRelated refCount persistent live
      exact localRelated.incrementReference_boxed ⟨kind, scalar, objectEq⟩ valid
        amount fits check
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
          decoded refCount persistent live
      exact localRelated.incrementReference_natural ⟨value, objectEq⟩ valid
        amount fits check

/-- Complete local above-one decrement theorem for every live-cell
representation in the current W6 heap relation. -/
theorem LiveCellRel.decrementReferenceOnce_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      Fir.Wasm.Concrete.decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  cases related with
  | @constructor info fieldKinds semantic header _ descriptor objectEq objectRelated
        headerRead headerKind refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .constructor descriptor objectEq objectRelated headerRead headerKind refCount
          persistent live
      exact localRelated.decrementReferenceOnce_constructor_above_one
        ⟨semantic, objectEq⟩ valid oneLt check
  | @boxed kind scalar header _ descriptor objectEq objectRelated refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .boxed descriptor objectEq objectRelated refCount persistent live
      exact localRelated.decrementReferenceOnce_boxed_above_one
        ⟨kind, scalar, objectEq⟩ valid oneLt check
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
          decoded refCount persistent live
      exact localRelated.decrementReferenceOnce_natural_above_one
        ⟨value, objectEq⟩ valid oneLt check

theorem LiveCellRel.live_eq_true
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) : cell.live = true := by
  cases related <;> assumption

theorem LiveCellRel.persistent_eq_false
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) : cell.persistent = false := by
  cases related with
  | constructor _ _ objectRelated headerRead _ _ persistent _ =>
      obtain ⟨objectHeader, objectHeaderRead, _, _, objectOrdinary, _, _, _, _⟩ :=
        objectRelated.header
      rw [headerRead] at objectHeaderRead
      cases objectHeaderRead
      rw [← persistent]
      exact objectOrdinary
  | boxed _ _ objectRelated _ persistent _ =>
      rw [← persistent]
      exact objectRelated.ordinary
  | natural _ _ _ _ ordinary _ _ _ _ _ persistent _ =>
      rw [← persistent]
      exact ordinary

/-- Above one, the source ownership operation takes the same nonrecursive
count-rewrite step for every ordinary cell in the concrete heap relation. -/
theorem LiveCellRel.decValueOnce_above_one_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (oneLt : 1 < cell.rc) (check : Bool) :
    Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
      setCell runtime location { cell with rc := cell.rc - 1 } := by
  unfold Fir.LeanIR.Impure.decValueOnce
  exact Fir.LeanIR.Impure.decLocation_above_one runtime location cell found
    related.live_eq_true related.persistent_eq_false oneLt

/-- The boxed above-one decrement crosses the complete local refinement
boundary: concrete and source execution perform the same count update, and
the resulting concrete cell still decodes as that updated semantic cell. -/
theorem LiveCellRel.decrementReferenceOnce_boxed_refines_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (boxedCell : ∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
      cell.object = .boxed kind.semanticType scalar.semanticValue)
    (valid : state.FrontierInvariant)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        setCell runtime location { cell with rc := cell.rc - 1 } ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  obtain ⟨result, operation, finalValid, relatedAfter⟩ :=
    related.decrementReferenceOnce_boxed_above_one boxedCell valid oneLt check
  exact ⟨result, operation,
    related.decValueOnce_above_one_eq runtime location found oneLt check,
    finalValid, relatedAfter⟩

/-- Complete local source/concrete composition for the nonrecursive decrement
branch across constructors, boxes, and heap naturals. -/
theorem LiveCellRel.decrementReferenceOnce_refines_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (valid : state.FrontierInvariant)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      Fir.Wasm.Concrete.decrementReferenceOnce state address check = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        setCell runtime location { cell with rc := cell.rc - 1 } ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  obtain ⟨result, operation, finalValid, relatedAfter⟩ :=
    related.decrementReferenceOnce_above_one valid oneLt check
  exact ⟨result, operation,
    related.decValueOnce_above_one_eq runtime location found oneLt check,
    finalValid, relatedAfter⟩

/-- Every currently represented ordinary live cell takes the same semantic
increment step; the object-specific concrete theorem only has to frame its
payload decoder. -/
theorem LiveCellRel.incValue_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (amount : Nat) (check : Bool) :
    Fir.LeanIR.Impure.incValue runtime (.object (.heap location)) amount check =
      setCell runtime location { cell with rc := cell.rc + amount } := by
  unfold Fir.LeanIR.Impure.incValue Fir.LeanIR.Impure.incLocation
  simp only [getLiveCell, found, related.live_eq_true, related.persistent_eq_false,
    ↓reduceIte, Bind.bind, Except.bind]
  congr 2

/-- The corresponding semantic boxed increment reaches exactly the mutable
`setCell` boundary with the incremented count. -/
theorem LiveCellRel.incValue_boxed_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (boxedCell : ∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
      cell.object = .boxed kind.semanticType scalar.semanticValue)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (amount : Nat) (check : Bool) :
    Fir.LeanIR.Impure.incValue runtime (.object (.heap location)) amount check =
      setCell runtime location { cell with rc := cell.rc + amount } := by
  have cellLive : cell.live = true := by
    cases related with
    | constructor _ objectEq _ _ _ _ _ live =>
        obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
    | boxed _ _ _ _ _ live => exact live
    | natural _ objectEq _ _ _ _ _ _ _ _ _ live =>
        obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
  have notPersistent : cell.persistent = false := by
    cases related with
    | constructor _ objectEq _ _ _ _ _ _ =>
        obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
    | boxed _ _ objectRelated _ persistent _ =>
        rw [← persistent]
        exact objectRelated.ordinary
    | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
        obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
  unfold Fir.LeanIR.Impure.incValue Fir.LeanIR.Impure.incLocation
  simp only [getLiveCell, found, cellLive, notPersistent, ↓reduceIte,
    Bind.bind, Except.bind]
  congr 2

end Fir.Wasm.Concrete
