import Fir.Wasm.Concrete.Runtime
import Fir.Wasm.Concrete.FreshAllocationCorrectness
import Fir.Wasm.Concrete.ClosureHeapCorrectness
import Fir.Wasm.Concrete.StringAllocationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- A concrete heap transition preserves the physical allocation extent of
every semantic heap location already mapped by the refinement witness.
Payload, liveness, and ownership metadata may change. -/
def MappedHeaderCapacityTransport
    (before after : MemoryState) (witness : RefinementWitness) : Prop :=
  ∀ address location header,
    witness.locations.lookup? location = some address →
    Header.read before.memory address = .ok header →
    address.value + headerBytes ≤ before.heapCursor →
    ∃ nextHeader,
      Header.read after.memory address = .ok nextHeader ∧
      nextHeader.allocationBytes = header.allocationBytes ∧
      address.value + headerBytes ≤ after.heapCursor

theorem MappedHeaderCapacityTransport.refl
    (state : MemoryState) (witness : RefinementWitness) :
    MappedHeaderCapacityTransport state state witness := by
  intro address location header mapped headerRead owned
  exact ⟨header, headerRead, rfl, owned⟩

theorem MappedHeaderCapacityTransport.trans
    {first second third : MemoryState} {witness : RefinementWitness}
    (firstSecond : MappedHeaderCapacityTransport first second witness)
    (secondThird : MappedHeaderCapacityTransport second third witness) :
    MappedHeaderCapacityTransport first third witness := by
  intro address location header mapped headerRead owned
  obtain ⟨middleHeader, middleRead, middleExtent, middleOwned⟩ :=
    firstSecond address location header mapped headerRead owned
  obtain ⟨finalHeader, finalRead, finalExtent, finalOwned⟩ :=
    secondThird address location middleHeader mapped middleRead middleOwned
  exact ⟨finalHeader, finalRead, finalExtent.trans middleExtent, finalOwned⟩

/-- Extending concrete memory above the old heap frontier preserves every
header already represented by the refinement witness. -/
theorem MappedHeaderCapacityTransport.ofPrefixExtension
    {before after : MemoryState} (witness : RefinementWitness)
    (extension : before.PrefixExtension after) :
    MappedHeaderCapacityTransport before after witness := by
  intro address location header mapped headerRead owned
  refine ⟨header, ?_, rfl, Nat.le_trans owned extension.cursor⟩
  rw [extension.readHeader address owned]
  exact headerRead

/-- A decoded concrete constructor represents one semantic constructor. The
field clauses are indexed by the allocation-time ABI descriptor, which is the
same metadata used by the W2 `allocCtor` host contract. -/
structure ConstructorObjectRel (state : MemoryState) (witness : RefinementWitness)
    (address : Word32) (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (semantic : ConstructorObject) : Prop where
  header : ∃ header,
    state.readLiveHeader address = .ok header ∧
    header.kind = .constructor ∧
    (ConstructorLayout.ofInfo info).allocationBytes ≤
      header.allocationBytes.toNat ∧
    header.aux0.toNat = semantic.tag ∧
    header.aux1.toNat = info.size ∧
    header.aux2.toNat = info.usize ∧
    header.aux3.toNat = info.ssize
  headerOwned : address.value + headerBytes ≤ state.heapCursor
  extent : address.value + (ConstructorLayout.ofInfo info).allocationBytes ≤
    state.heapCursor
  semanticObjectFields : semantic.objectFields.size = info.size
  semanticUSizeFields : semantic.usizeFields.size = info.usize
  /-- W6.2 packages the compiler's verified packed scalar fields. Floating
  fields use the same physical widths as `UInt32`/`UInt64` and retain their
  exact IEEE-754 bit patterns. Every represented field carries the
  compiler-shaped scalar base, stays within the declared packed region, and
  reads back from concrete memory. -/
  semanticScalarFields : ∀ field, field ∈ semantic.scalarFields →
    match field.value with
    | .uint8 value =>
        field.width = info.size + info.usize ∧
        field.offset + 1 ≤ info.ssize ∧
        readScalarUInt8Field state address field.width field.offset = .ok value
    | .uint16 value =>
        field.width = info.size + info.usize ∧
        field.offset + 2 ≤ info.ssize ∧
        readScalarUInt16Field state address field.width field.offset = .ok value
    | .uint32 value =>
        field.width = info.size + info.usize ∧
        field.offset + 4 ≤ info.ssize ∧
        readScalarUInt32Field state address field.width field.offset = .ok value
    | .uint64 value =>
        field.width = info.size + info.usize ∧
        field.offset + 8 ≤ info.ssize ∧
        readScalarUInt64Field state address field.width field.offset = .ok value
    | .float32Bits bits =>
        field.width = info.size + info.usize ∧
        field.offset + 4 ≤ info.ssize ∧
        readScalarUInt32Field state address field.width field.offset = .ok bits
    | .float64Bits bits =>
        field.width = info.size + info.usize ∧
        field.offset + 8 ≤ info.ssize ∧
        readScalarUInt64Field state address field.width field.offset = .ok bits
  fieldKindsSize : fieldKinds.size = info.size
  fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true
  objectFields : ∀ index kind value,
    fieldKinds[index]? = some kind →
    semantic.objectFields[index]? = some value →
    ∃ word, readObjectField state address index = .ok word ∧
      ValueRel witness kind (.word32 word) value
  usizeFields : ∀ index value,
    semantic.usizeFields[index]? = some value →
    readUSizeField state address index = .ok value

/-- Every declared constructor object slot carries an ABI kind whose concrete
word may participate in ownership traversal. -/
theorem ConstructorObjectRel.fieldKind
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    {index : Nat} (indexLt : index < info.size) :
    ∃ kind, fieldKinds[index]? = some kind ∧ kind.isObjectField = true := by
  have kindLt : index < fieldKinds.size := by
    rw [related.fieldKindsSize]
    exact indexLt
  refine ⟨fieldKinds[index], Array.getElem?_eq_getElem kindLt, ?_⟩
  exact Array.all_eq_true.mp related.fieldKindsValid index kindLt

/-- Constructor decoding and typed projections are stable through a fresh
prefix extension whenever the constructor's declared extent is owned by the
old state. -/
theorem ConstructorObjectRel.prefixExtension
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel before witness address info fieldKinds semantic)
    (extension : before.PrefixExtension after) :
    ConstructorObjectRel after witness address info fieldKinds semantic := by
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes, tag, objectCount,
      usizeCount, scalarCount⟩ := related.header.choose_spec
  change before.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
  have headerAfter := extension.readLiveHeader_eq_ok address header
    related.headerOwned headerRead
  have heap := (MemoryState.PrefixExtension.readLiveHeader_facts
    before address header headerRead).1
  have constructorHeaderBefore : readConstructorHeader before address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have constructorHeaderAfter : readConstructorHeader after address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have scalarFieldsAfter : ∀ field, field ∈ semantic.scalarFields →
      match field.value with
      | .uint8 value =>
          field.width = info.size + info.usize ∧
          field.offset + 1 ≤ info.ssize ∧
          readScalarUInt8Field after address field.width field.offset = .ok value
      | .uint16 value =>
          field.width = info.size + info.usize ∧
          field.offset + 2 ≤ info.ssize ∧
          readScalarUInt16Field after address field.width field.offset = .ok value
      | .uint32 value =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field after address field.width field.offset = .ok value
      | .uint64 value =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field after address field.width field.offset = .ok value
      | .float32Bits bits =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field after address field.width field.offset = .ok bits
      | .float64Bits bits =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field after address field.width field.offset = .ok bits
      := by
    intro field member
    have beforeField := related.semanticScalarFields field member
    cases valueEq : field.value with
    | uint8 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset <
              before.heapCursor := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          have extent := related.extent
          simp [ConstructorLayout.ofInfo, target] at extent layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt8Field after address field.width field.offset =
              readScalarUInt8Field before address field.width field.offset := by
          unfold readScalarUInt8Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 1 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          change liftMemory (after.memory.readByte _) =
            liftMemory (before.memory.readByte _)
          rw [extension.readByte _ fieldOwned]
        rw [operationEq]
        exact readBefore
    | uint16 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset + 2 ≤
              before.heapCursor := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          have extent := related.extent
          simp [ConstructorLayout.ofInfo, target] at extent layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt16Field after address field.width field.offset =
              readScalarUInt16Field before address field.width field.offset := by
          unfold readScalarUInt16Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 2 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          change liftMemory (after.memory.readUInt16 _) =
            liftMemory (before.memory.readUInt16 _)
          rw [extension.readUInt16 _ fieldOwned]
        rw [operationEq]
        exact readBefore
    | uint32 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset + 4 ≤
              before.heapCursor := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          have extent := related.extent
          simp [ConstructorLayout.ofInfo, target] at extent layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt32Field after address field.width field.offset =
              readScalarUInt32Field before address field.width field.offset := by
          unfold readScalarUInt32Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 4 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          change liftMemory (after.memory.readUInt32 _) =
            liftMemory (before.memory.readUInt32 _)
          rw [extension.readUInt32 _ fieldOwned]
        rw [operationEq]
        exact readBefore
    | uint64 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset + 8 ≤
              before.heapCursor := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          have extent := related.extent
          simp [ConstructorLayout.ofInfo, target] at extent layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt64Field after address field.width field.offset =
              readScalarUInt64Field before address field.width field.offset := by
          unfold readScalarUInt64Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 8 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          change liftMemory (after.memory.readUInt64 _) =
            liftMemory (before.memory.readUInt64 _)
          rw [extension.readUInt64 _ fieldOwned]
        rw [operationEq]
        exact readBefore
    | float32Bits bits =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset + 4 ≤
              before.heapCursor := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          have extent := related.extent
          simp [ConstructorLayout.ofInfo, target] at extent layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt32Field after address field.width field.offset =
              readScalarUInt32Field before address field.width field.offset := by
          unfold readScalarUInt32Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 4 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          change liftMemory (after.memory.readUInt32 _) =
            liftMemory (before.memory.readUInt32 _)
          rw [extension.readUInt32 _ fieldOwned]
        rw [operationEq]
        exact readBefore
    | float64Bits bits =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have fieldOwned :
            address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset + 8 ≤
              before.heapCursor := by
          have layoutBound := align8_ge
            (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
              info.ssize)
          have extent := related.extent
          simp [ConstructorLayout.ofInfo, target] at extent layoutBound ⊢
          rw [widthEq]
          omega
        have operationEq :
            readScalarUInt64Field after address field.width field.offset =
              readScalarUInt64Field before address field.width field.offset := by
          unfold readScalarUInt64Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddress : scalarFieldAddress address header field.width
              field.offset 8 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          rw [scalarAddress]
          change liftMemory (after.memory.readUInt64 _) =
            liftMemory (before.memory.readUInt64 _)
          rw [extension.readUInt64 _ fieldOwned]
        rw [operationEq]
        exact readBefore
  refine {
    header := ⟨header, headerAfter, headerKind, allocationBytes, tag,
      objectCount, usizeCount, scalarCount⟩
    headerOwned := Nat.le_trans related.headerOwned extension.cursor
    extent := Nat.le_trans related.extent extension.cursor
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := scalarFieldsAfter
    fieldKindsSize := related.fieldKindsSize
    fieldKindsValid := related.fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · intro index kind value kindAt valueAt
    obtain ⟨word, fieldBefore, valueRelated⟩ :=
      related.objectFields index kind value kindAt valueAt
    have indexLt : index < info.size := by
      obtain ⟨semanticIndex, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
      have semanticSize := related.semanticObjectFields
      omega
    have fieldOwned :
        address.value + headerBytes + target.semanticSlotBytes * index + 8 ≤
          before.heapCursor := by
      have aligned := align8_ge
        (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
      have extent := related.extent
      simp [ConstructorLayout.ofInfo, target] at extent aligned ⊢
      omega
    have fieldAfter : readObjectField after address index = .ok word := by
      have operationEq : readObjectField after address index =
          readObjectField before address index := by
        unfold readObjectField
        rw [constructorHeaderAfter, constructorHeaderBefore]
        simp only [Bind.bind, Except.bind]
        rw [extension.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * index) (by omega)]
        rw [extension.readUInt32
          (address.value + headerBytes + target.semanticSlotBytes * index + 4) (by omega)]
      rw [operationEq]
      exact fieldBefore
    exact ⟨word, fieldAfter, valueRelated⟩
  · intro index value valueAt
    have indexLt : index < info.usize := by
      obtain ⟨semanticIndex, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
      have semanticSize := related.semanticUSizeFields
      omega
    have fieldOwned :
        address.value + headerBytes +
            target.semanticSlotBytes * (info.size + index) + 8 ≤
          before.heapCursor := by
      have aligned := align8_ge
        (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
      have extent := related.extent
      simp [ConstructorLayout.ofInfo, target] at extent aligned ⊢
      omega
    have operationEq : readUSizeField after address index =
        readUSizeField before address index := by
      unfold readUSizeField
      rw [constructorHeaderAfter, constructorHeaderBefore]
      simp only [Bind.bind, Except.bind]
      rw [objectCount]
      rw [extension.readUInt64
        (address.value + headerBytes + target.semanticSlotBytes * (info.size + index))
        (by omega)]
    rw [operationEq]
    exact related.usizeFields index value valueAt

/-- Constructor relations are monotone in proof-only witness metadata. -/
theorem ConstructorObjectRel.witnessExtension
    {state : MemoryState} {before after : RefinementWitness}
    {address : Word32} {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state before address info fieldKinds semantic)
    (extension : before.Extends after) :
    ConstructorObjectRel state after address info fieldKinds semantic := by
  refine {
    header := related.header
    headerOwned := related.headerOwned
    extent := related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := related.semanticScalarFields
    fieldKindsSize := related.fieldKindsSize
    fieldKindsValid := related.fieldKindsValid
    objectFields := ?_
    usizeFields := related.usizeFields }
  intro index kind value kindAt valueAt
  obtain ⟨word, read, valueRelated⟩ :=
    related.objectFields index kind value kindAt valueAt
  exact ⟨word, read, valueRelated.witnessExtension extension⟩

/-- Exact W6 relation for the canonical resident generic Array layout.
`elements` is the semantic live prefix; `capacity` records the retained
physical extent. The pointwise clause deliberately covers only live slots,
so uninitialized spare capacity cannot become semantic ownership. -/
structure ResidentArrayObjectRel (state : MemoryState)
    (witness : RefinementWitness) (address : Word32) (elements : Array Value)
    (capacity : Nat) (header : Header) : Prop where
  headerRead : state.readLiveHeader address = .ok header
  headerKind : header.kind = .opaque
  marker : header.aux0 = residentArrayMarker
  logicalSize : header.aux1.toNat = elements.size
  physicalCapacity : header.aux2.toNat = capacity
  reserved : header.aux3 = 0
  sizeCapacity : elements.size ≤ capacity
  allocationBytes : header.allocationBytes.toNat =
    residentArrayAllocationBytes capacity
  headerOwned : address.value + headerBytes ≤ state.heapCursor
  extent : address.value + residentArrayAllocationBytes capacity ≤
    state.heapCursor
  liveElements : ∀ index value,
    elements[index]? = some value →
    ∃ word,
      state.memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * index) =
        .ok word ∧
      ValueRel witness .tobject (.word32 word) value

/-- A resident Array decoder is stable when fresh allocation extends memory
above its complete retained capacity. -/
theorem ResidentArrayObjectRel.prefixExtension
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header}
    (related : ResidentArrayObjectRel before witness address elements capacity header)
    (extension : before.PrefixExtension after) :
    ResidentArrayObjectRel after witness address elements capacity header := by
  refine {
    headerRead := extension.readLiveHeader_eq_ok address header
      related.headerOwned related.headerRead
    headerKind := related.headerKind
    marker := related.marker
    logicalSize := related.logicalSize
    physicalCapacity := related.physicalCapacity
    reserved := related.reserved
    sizeCapacity := related.sizeCapacity
    allocationBytes := related.allocationBytes
    headerOwned := Nat.le_trans related.headerOwned extension.cursor
    extent := Nat.le_trans related.extent extension.cursor
    liveElements := ?_ }
  intro index value valueAt
  obtain ⟨word, readBefore, valueRelated⟩ :=
    related.liveElements index value valueAt
  have indexLt : index < elements.size :=
    (Array.getElem?_eq_some_iff.mp valueAt).1
  have fieldOwned :
      address.value + headerBytes + target.semanticSlotBytes * index + 4 ≤
        before.heapCursor := by
    have sizeCapacity := related.sizeCapacity
    have minimum := align8_ge
      (headerBytes + target.semanticSlotBytes * capacity)
    have extent := related.extent
    simp [residentArrayAllocationBytes, target] at minimum extent ⊢
    omega
  refine ⟨word, ?_, valueRelated⟩
  rw [extension.readWord32 _ fieldOwned]
  exact readBefore

/-- Resident Array element relations are monotone in proof-only witness
metadata, just like constructor and closure fields. -/
theorem ResidentArrayObjectRel.witnessExtension
    {state : MemoryState} {before after : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header}
    (related : ResidentArrayObjectRel state before address elements capacity header)
    (extension : before.Extends after) :
    ResidentArrayObjectRel state after address elements capacity header := by
  refine {
    headerRead := related.headerRead
    headerKind := related.headerKind
    marker := related.marker
    logicalSize := related.logicalSize
    physicalCapacity := related.physicalCapacity
    reserved := related.reserved
    sizeCapacity := related.sizeCapacity
    allocationBytes := related.allocationBytes
    headerOwned := related.headerOwned
    extent := related.extent
    liveElements := ?_ }
  intro index value valueAt
  obtain ⟨word, read, valueRelated⟩ :=
    related.liveElements index value valueAt
  exact ⟨word, read, valueRelated.witnessExtension extension⟩

/-- The shared checked Array decoder recovers the exact related header. -/
theorem ResidentArrayObjectRel.readHeader
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header) :
    readResidentArrayHeader state address = .ok header := by
  obtain ⟨heap, _, _, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      related.headerRead
  have valid :
      header.kind == ObjectKind.opaque &&
        header.aux0 == residentArrayMarker && header.aux3 == 0 &&
        header.aux1.toNat ≤ header.aux2.toNat &&
        header.allocationBytes.toNat ==
          residentArrayAllocationBytes header.aux2.toNat := by
    have opaqueEq : (ObjectKind.opaque == ObjectKind.opaque) = true := by decide
    simpa [opaqueEq, related.headerKind, related.marker, related.reserved,
      related.logicalSize, related.physicalCapacity, related.sizeCapacity,
      related.allocationBytes] using related.sizeCapacity
  unfold readResidentArrayHeader
  rw [heap]
  simp only [Bind.bind, Except.bind, liftMemory]
  rw [related.headerRead]
  simp only
  rw [if_pos valid]
  rfl

/-- The resident size projection observes semantic live length, not capacity. -/
theorem ResidentArrayObjectRel.readSize
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header) :
    readResidentArraySize state address = .ok elements.size := by
  unfold readResidentArraySize
  rw [related.readHeader]
  change (Except.ok header.aux1.toNat : Except ConcreteError Nat) =
    Except.ok elements.size
  rw [related.logicalSize]

/-- A successful borrowed read returns the exact related semantic element and
does not perform any ownership transition. -/
theorem ResidentArrayObjectRel.readElementBorrowed
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header} {index : Nat} {value : Value}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (valueAt : elements[index]? = some value) :
    ∃ word,
      readResidentArrayElementBorrowed state address index = .ok word ∧
      ValueRel witness .tobject (.word32 word) value := by
  obtain ⟨word, read, valueRelated⟩ :=
    related.liveElements index value valueAt
  have indexLt : index < elements.size :=
    (Array.getElem?_eq_some_iff.mp valueAt).1
  unfold readResidentArrayElementBorrowed
  rw [related.readHeader]
  simp only [Bind.bind, Except.bind]
  rw [if_pos (by simpa [related.logicalSize] using indexLt)]
  refine ⟨word, ?_, valueRelated⟩
  rw [read]
  rfl

/-- Borrowed reads beyond the semantic live prefix fail at the shared source
bounds boundary; spare physical capacity is never readable as a live value. -/
theorem ResidentArrayObjectRel.readElementBorrowed_outOfBounds
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header} {index : Nat}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header)
    (outOfBounds : elements.size ≤ index) :
    readResidentArrayElementBorrowed state address index =
      .error (.source (.objectFieldOutOfBounds index elements.size)) := by
  unfold readResidentArrayElementBorrowed
  rw [related.readHeader]
  simp only [Bind.bind, Except.bind]
  have notLt : ¬index < header.aux1.toNat := by
    rw [related.logicalSize]
    omega
  rw [if_neg notLt]
  change (Except.error
      (.source (.objectFieldOutOfBounds index header.aux1.toNat)) :
      Except ConcreteError Word32) =
    Except.error (.source (.objectFieldOutOfBounds index elements.size))
  rw [related.logicalSize]

/-- Cell-level resident Array relation. This keeps the semantic identity,
capacity, reference count, persistence flag, and liveness together without
admitting ordinary opaque objects. -/
inductive ResidentArrayCellRel (state : MemoryState)
    (witness : RefinementWitness) (address : Word32) : HeapCell → Prop where
  | array {elements : Array Value} {capacity : Nat} {header : Header} {cell : HeapCell}
      (objectEq : cell.object = .array elements capacity)
      (objectRelated :
        ResidentArrayObjectRel state witness address elements capacity header)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      ResidentArrayCellRel state witness address cell

/-- Exact decoded relation for one canonical heap-backed scalar box. The
semantic type/value pair is recovered from `kind` and `scalar`; no source
location identity is stored in linear memory. -/
structure BoxedObjectRel (state : MemoryState) (address : Word32)
    (kind : BoxedScalarKind) (scalar : BoxedScalar) (header : Header) : Prop where
  scalarKind : scalar.kind = kind
  headerRead : state.readLiveHeader address = .ok header
  headerKind : header.kind = .boxed
  allocationBytes : header.allocationBytes.toNat =
    align8 (headerBytes + target.semanticSlotBytes)
  kindCode : header.aux0 = kind.code
  payloadBytes : header.aux1 = UInt32.ofNat kind.payloadBytes
  reserved2 : header.aux2 = 0
  reserved3 : header.aux3 = 0
  headerOwned : address.value + headerBytes ≤ state.heapCursor
  extent : address.value + header.allocationBytes.toNat ≤ state.heapCursor
  decoded : readBoxedScalar state kind address = .ok scalar

/-- Decoded relation for the current experimental arbitrary-precision heap
integer layout. Clients depend on the checked value boundary; the auxiliary
header lanes remain free to evolve with the backend. -/
structure IntegerObjectRel (state : MemoryState) (address : Word32)
    (value : Int) (header : Header) : Prop where
  headerRead : state.readLiveHeader address = .ok header
  headerKind : header.kind = .integer
  marker : header.aux0 = integerSignMagnitudeMarker
  limbCount : header.aux1.toNat =
    (naturalLimbs (integerMagnitude value)).length
  sign : header.aux2 = integerSign value
  reserved : header.aux3 = 0
  allocationBytes : header.allocationBytes.toNat =
    align8 (headerBytes + target.semanticSlotBytes *
      (naturalLimbs (integerMagnitude value)).length)
  extent : address.value + header.allocationBytes.toNat ≤ state.heapCursor
  decoded : readInteger state address = .ok value

theorem IntegerObjectRel.headerOwned
    {state : MemoryState} {address : Word32} {value : Int} {header : Header}
    (related : IntegerObjectRel state address value header) :
    address.value + headerBytes ≤ state.heapCursor := by
  have extent := related.extent
  rw [related.allocationBytes] at extent
  have minimum := align8_ge
    (headerBytes + target.semanticSlotBytes *
      (naturalLimbs (integerMagnitude value)).length)
  omega

/-- Relation for live semantic cells implemented by the current W6 runtime.
Dead cells and future heap objects receive cases in their own implementation
slices rather than being hidden behind a permissive catch-all. -/
inductive LiveCellRel (state : MemoryState) (witness : RefinementWitness)
    (address : Word32) : HeapCell → Prop where
  | constructor {info fieldKinds semantic header cell}
      (descriptor : witness.descriptors.lookup? address =
        some (.constructor info fieldKinds))
      (objectEq : cell.object = .ctor semantic)
      (related : ConstructorObjectRel state witness address info fieldKinds semantic)
      (headerRead : state.readLiveHeader address = .ok header)
      (headerKind : header.kind = .constructor)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      LiveCellRel state witness address cell

  | boxed {kind scalar header cell}
      (descriptor : witness.descriptors.lookup? address = some (.boxed kind))
      (objectEq : cell.object = .boxed kind.semanticType scalar.semanticValue)
      (related : BoxedObjectRel state address kind scalar header)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      LiveCellRel state witness address cell
  | natural {value header cell}
      (descriptor : witness.descriptors.lookup? address = some (.natural value))
      (objectEq : cell.object = .natural value)
      (headerRead : state.readLiveHeader address = .ok header)
      (headerKind : header.kind = .natural)
      (marker : header.aux0 = bigNaturalMarker)
      (extent : address.value + header.allocationBytes.toNat ≤ state.heapCursor)
      (limbsFit : headerBytes +
        target.semanticSlotBytes * header.aux1.toNat ≤
          header.allocationBytes.toNat)
      (decoded : readNatural state address = .ok value)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      LiveCellRel state witness address cell

  | integer {value header cell}
      (descriptor : witness.descriptors.lookup? address = some (.integer value))
      (objectEq : cell.object = .integer value)
      (related : IntegerObjectRel state address value header)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      LiveCellRel state witness address cell

  | string {value header cell}
      (descriptor : witness.descriptors.lookup? address = some (.string value))
      (objectEq : cell.object = .string value)
      (related : StringObjectRel state address value header)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      LiveCellRel state witness address cell

  | array {elements capacity header cell}
      (descriptor : witness.descriptors.lookup? address = some (.array capacity))
      (objectEq : cell.object = .array elements capacity)
      (related :
        ResidentArrayObjectRel state witness address elements capacity header)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      LiveCellRel state witness address cell

  | closure {cell}
      (related : ClosureCellRel state witness address cell) :
      LiveCellRel state witness address cell

/-- Canonical concrete representation of a released semantic cell. The old
payload is intentionally not decoded: only the retained allocation extent and
the frozen freed-header metadata remain observable. -/
structure DeadCellRel (state : MemoryState) (address : Word32) : Prop where
  header : ∃ header,
    Header.read state.memory address = .ok header ∧
    address.classify = .heap ∧
    header.kind = .freed ∧
    header.persistent = false ∧
    header.live = false ∧
    header.refCount = 0 ∧
    header.aux0 = 0 ∧ header.aux1 = 0 ∧ header.aux2 = 0 ∧ header.aux3 = 0 ∧
    headerBytes ≤ header.allocationBytes.toNat ∧
    header.allocationBytes.toNat % target.heapAlignment = 0 ∧
    address.value + header.allocationBytes.toNat ≤ state.memory.size
  headerOwned : address.value + headerBytes ≤ state.heapCursor

/-- Every canonical released cell is rejected by the common live-header
decoder with its exact physical address.  Operation-specific stale-reference
proofs should start from this fact rather than reopening the freed layout. -/
theorem DeadCellRel.readLiveHeader_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) :
    state.readLiveHeader address = .error (.deadObject address) := by
  obtain ⟨header, headerRead, addressHeap, _, _, dead, _, _, _, _, _, _, _, _⟩ :=
    related.header
  unfold MemoryState.readLiveHeader
  rw [addressHeap]
  simp only [headerRead, Bind.bind, Except.bind]
  rw [dead]
  rfl

/-- The recursive natural-limb decoder reads identically when all requested
slots lie below the preserved prefix. -/
theorem MemoryState.PrefixExtension.readNaturalLimbs
    {before after : MemoryState} (extension : before.PrefixExtension after)
    (base index count : Nat)
    (owned : base + headerBytes +
      target.semanticSlotBytes * (index + count) ≤ before.heapCursor) :
    readNaturalLimbs after.memory base index count =
      readNaturalLimbs before.memory base index count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      unfold Fir.Wasm.Concrete.readNaturalLimbs
      rw [extension.readUInt64
        (base + headerBytes + target.semanticSlotBytes * index) (by
          simp [target] at owned ⊢
          omega)]
      rw [ih (index + 1) (by
        simp [target] at owned ⊢
        omega)]

/-- Canonical boxed headers and payloads decode identically through a fresh
prefix extension. -/
theorem BoxedObjectRel.prefixExtension
    {before after : MemoryState} {address : Word32} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {header : Header}
    (related : BoxedObjectRel before address kind scalar header)
    (extension : before.PrefixExtension after) :
    BoxedObjectRel after address kind scalar header := by
  have headerAfter := extension.readLiveHeader_eq_ok address header
    related.headerOwned related.headerRead
  have payloadOwned :
      address.value + headerBytes + target.semanticSlotBytes ≤ before.heapCursor := by
    have extent := related.extent
    rw [related.allocationBytes] at extent
    simp [target, headerBytes, align8] at extent ⊢
    omega
  have payloadEq := extension.readUInt64
    (address.value + headerBytes) (by simpa [target] using payloadOwned)
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts before address header
      related.headerRead).1
  have decoderEq :
      readBoxedScalar after kind address = readBoxedScalar before kind address := by
    unfold readBoxedScalar
    rw [heap]
    simp only
    rw [headerAfter, related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    have boxedBeq : (header.kind == ObjectKind.boxed) = true := by
      rw [related.headerKind]
      decide
    rw [boxedBeq]
    simp only [if_true]
    unfold readHeapBoxedScalar
    rw [payloadEq]
  exact {
    scalarKind := related.scalarKind
    headerRead := headerAfter
    headerKind := related.headerKind
    allocationBytes := related.allocationBytes
    kindCode := related.kindCode
    payloadBytes := related.payloadBytes
    reserved2 := related.reserved2
    reserved3 := related.reserved3
    headerOwned := Nat.le_trans related.headerOwned extension.cursor
    extent := Nat.le_trans related.extent extension.cursor
    decoded := by rw [decoderEq]; exact related.decoded }

/-- Checked heap-integer decoding is stable through an allocation that only
extends the old concrete prefix. -/
theorem IntegerObjectRel.prefixExtension
    {before after : MemoryState} {address : Word32} {value : Int}
    {header : Header}
    (related : IntegerObjectRel before address value header)
    (extension : before.PrefixExtension after) :
    IntegerObjectRel after address value header := by
  have headerAfter := extension.readLiveHeader_eq_ok address header
    (by
      have extent := related.extent
      rw [related.allocationBytes] at extent
      have minimum := align8_ge
        (headerBytes + target.semanticSlotBytes *
          (naturalLimbs (integerMagnitude value)).length)
      omega)
    related.headerRead
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts before address header
      related.headerRead).1
  have payloadOwned : address.value + headerBytes +
      target.semanticSlotBytes * header.aux1.toNat ≤ before.heapCursor := by
    rw [related.limbCount]
    have extent := related.extent
    rw [related.allocationBytes] at extent
    have minimum := align8_ge
      (headerBytes + target.semanticSlotBytes *
        (naturalLimbs (integerMagnitude value)).length)
    omega
  have decoderEq : readInteger after address = readInteger before address := by
    unfold readInteger
    simp [heap]
    rw [headerAfter, related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [extension.readNaturalLimbs address.value 0 header.aux1.toNat (by
      simpa using payloadOwned)]
  exact {
    headerRead := headerAfter
    headerKind := related.headerKind
    marker := related.marker
    limbCount := related.limbCount
    sign := related.sign
    reserved := related.reserved
    allocationBytes := related.allocationBytes
    extent := Nat.le_trans related.extent extension.cursor
    decoded := by rw [decoderEq]; exact related.decoded }

/-- Every currently implemented live-cell relation is stable through fresh
allocation when the relation records its complete read extent. -/
theorem LiveCellRel.prefixExtension
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel before witness address cell)
    (extension : before.PrefixExtension after) :
    LiveCellRel after witness address cell := by
  cases related with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
        persistent live =>
      have objectAfter := objectRelated.prefixExtension extension
      have headerAfter := extension.readLiveHeader_eq_ok address _
        objectRelated.headerOwned headerRead
      exact .constructor descriptor objectEq objectAfter headerAfter headerKind refCount
        persistent live
  | boxed descriptor objectEq objectRelated refCount persistent live =>
      exact .boxed descriptor objectEq (objectRelated.prefixExtension extension)
        refCount persistent live
  | natural descriptor objectEq headerRead headerKind marker extent limbsFit
        decoded refCount persistent live =>
      obtain ⟨heap, _, _, minimum, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts before address _ headerRead
      have headerOwned : address.value + headerBytes ≤ before.heapCursor := by
        omega
      have headerAfter := extension.readLiveHeader_eq_ok address _ headerOwned headerRead
      have decoderEq : readNatural after address = readNatural before address := by
        unfold readNatural
        simp [heap]
        rw [headerAfter, headerRead]
        simp only [Bind.bind, Except.bind]
        simp [liftMemory, headerKind, marker]
        rw [extension.readNaturalLimbs address.value 0 _ (by
          simp [target] at limbsFit extent ⊢
          omega)]
      apply LiveCellRel.natural descriptor objectEq headerAfter headerKind marker
        (Nat.le_trans extent extension.cursor) limbsFit
      · rw [decoderEq]
        exact decoded
      · exact refCount
      · exact persistent
      · exact live
  | integer descriptor objectEq objectRelated refCount persistent live =>
      exact .integer descriptor objectEq
        (objectRelated.prefixExtension extension) refCount persistent live
  | string descriptor objectEq objectRelated refCount persistent live =>
      exact .string descriptor objectEq (objectRelated.prefixExtension extension)
        refCount persistent live
  | array descriptor objectEq objectRelated refCount persistent live =>
      exact .array descriptor objectEq (objectRelated.prefixExtension extension)
        refCount persistent live
  | closure closureRelated =>
      exact .closure (closureRelated.prefixExtension extension)

/-- Live-cell relations are monotone in proof-only witness metadata. -/
theorem LiveCellRel.witnessExtension
    {state : MemoryState} {before after : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state before address cell)
    (extension : before.Extends after) :
    LiveCellRel state after address cell := by
  cases related with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
        persistent live =>
      exact .constructor (extension.descriptors _ _ descriptor) objectEq
        (objectRelated.witnessExtension extension) headerRead headerKind refCount
        persistent live
  | boxed descriptor objectEq objectRelated refCount persistent live =>
      exact .boxed (extension.descriptors _ _ descriptor) objectEq objectRelated
        refCount persistent live
  | natural descriptor objectEq headerRead headerKind marker extent limbsFit
        decoded refCount persistent live =>
      exact .natural (extension.descriptors _ _ descriptor) objectEq headerRead
        headerKind marker extent limbsFit decoded refCount persistent live
  | integer descriptor objectEq objectRelated refCount persistent live =>
      exact .integer (extension.descriptors _ _ descriptor) objectEq objectRelated
        refCount persistent live
  | string descriptor objectEq objectRelated refCount persistent live =>
      exact .string (extension.descriptors _ _ descriptor) objectEq objectRelated
        refCount persistent live
  | array descriptor objectEq objectRelated refCount persistent live =>
      exact .array (extension.descriptors _ _ descriptor) objectEq
        (objectRelated.witnessExtension extension) refCount persistent live
  | closure closureRelated =>
      exact .closure (closureRelated.witnessExtension extension)

/-- Released headers remain canonical through fresh allocation beyond their
owned prefix. -/
theorem DeadCellRel.prefixExtension
    {before after : MemoryState} {address : Word32}
    (related : DeadCellRel before address)
    (extension : before.PrefixExtension after) :
    DeadCellRel after address := by
  obtain ⟨header, headerRead, addressHeap, headerKind, ordinary, dead, refCount,
      aux0, aux1, aux2, aux3, minimum, aligned, extentInMemory⟩ := related.header
  have headerAfter : Header.read after.memory address = .ok header := by
    rw [extension.readHeader address related.headerOwned]
    exact headerRead
  exact {
    header := ⟨header, headerAfter, addressHeap, headerKind, ordinary, dead, refCount,
      aux0, aux1, aux2, aux3, minimum, aligned,
      Nat.le_trans extentInMemory extension.memorySize⟩
    headerOwned := Nat.le_trans related.headerOwned extension.cursor }

theorem LiveCellRel.headerOwned
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) :
    address.value + headerBytes ≤ state.heapCursor := by
  cases related with
  | constructor _ _ objectRelated _ _ _ _ _ => exact objectRelated.headerOwned
  | boxed _ _ objectRelated _ _ _ => exact objectRelated.headerOwned
  | natural _ _ headerRead _ _ extent _ _ _ _ _ =>
      have minimum :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead).2.2.2.1
      omega
  | @integer value _ _ _ _ objectRelated _ _ _ =>
      have extent := objectRelated.extent
      rw [objectRelated.allocationBytes] at extent
      have minimum := align8_ge
        (headerBytes + target.semanticSlotBytes *
          (naturalLimbs (integerMagnitude value)).length)
      omega
  | string _ _ objectRelated _ _ _ => exact objectRelated.headerOwned
  | array _ _ objectRelated _ _ _ => exact objectRelated.headerOwned
  | closure closureRelated => exact closureRelated.headerOwned

/-- Whole-cell relation used once ownership can make semantic cells dead.
Live cells retain their complete payload decoder; dead cells retain only the
canonical freed allocation and the semantic zero-count/dead flags. -/
inductive CellRel (state : MemoryState) (witness : RefinementWitness)
    (address : Word32) : HeapCell → Prop where
  | live (related : LiveCellRel state witness address cell) :
      CellRel state witness address cell
  | dead (semanticCount : cell.rc = 0) (semanticDead : cell.live = false)
      (descriptor : ∃ allocation,
        witness.descriptors.lookup? address = some allocation)
      (related : DeadCellRel state address) :
      CellRel state witness address cell

theorem CellRel.headerOwned
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : CellRel state witness address cell) :
    address.value + headerBytes ≤ state.heapCursor := by
  cases related with
  | live liveRelated => exact liveRelated.headerOwned
  | dead _ _ _ deadRelated => exact deadRelated.headerOwned

theorem LiveCellRel.descriptor
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) :
    ∃ descriptor, witness.descriptors.lookup? address = some descriptor := by
  cases related with
  | constructor descriptor _ _ _ _ _ _ _ => exact ⟨_, descriptor⟩
  | boxed descriptor _ _ _ _ _ => exact ⟨_, descriptor⟩
  | natural descriptor _ _ _ _ _ _ _ _ _ _ => exact ⟨_, descriptor⟩
  | integer descriptor _ _ _ _ _ => exact ⟨_, descriptor⟩
  | string descriptor _ _ _ _ _ => exact ⟨_, descriptor⟩
  | array descriptor _ _ _ _ _ => exact ⟨_, descriptor⟩
  | closure closureRelated =>
      cases closureRelated with
      | closure _ objectRelated _ _ _ _ _ _ _ _ =>
          exact ⟨_, objectRelated.descriptor⟩

theorem CellRel.descriptor
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : CellRel state witness address cell) :
    ∃ descriptor, witness.descriptors.lookup? address = some descriptor := by
  cases related with
  | live liveRelated => exact liveRelated.descriptor
  | dead _ _ descriptor _ => exact descriptor

theorem CellRel.prefixExtension
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : CellRel before witness address cell)
    (extension : before.PrefixExtension after) :
    CellRel after witness address cell := by
  cases related with
  | live liveRelated => exact .live (liveRelated.prefixExtension extension)
  | dead count dead descriptor deadRelated =>
      exact .dead count dead descriptor (deadRelated.prefixExtension extension)

theorem CellRel.witnessExtension
    {state : MemoryState} {before after : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : CellRel state before address cell)
    (extension : before.Extends after) :
    CellRel state after address cell := by
  cases related with
  | live liveRelated => exact .live (liveRelated.witnessExtension extension)
  | dead count dead descriptor deadRelated =>
      exact .dead count dead
        ⟨descriptor.choose, extension.descriptors _ _ descriptor.choose_spec⟩
        deadRelated

/-- A whole-cell relation known semantically live exposes its complete live
payload relation. -/
theorem CellRel.live_of_eq_true
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : CellRel state witness address cell) (live : cell.live = true) :
    LiveCellRel state witness address cell := by
  cases related with
  | live liveRelated => exact liveRelated
  | dead _ dead _ _ => simp_all

/-- A promoted tag is a concrete allocation without a semantic heap location.
It must decode to the original tagged payload and retain persistent/no-RC
behavior. -/
structure PromotedTagRel (state : MemoryState) (witness : RefinementWitness)
    (payload : UInt64) (address : Word32) : Prop where
  mapped : witness.promotedTags.Contains payload address
  descriptor : witness.descriptors.lookup? address = some (.promotedTag payload)
  header : ∃ header,
    state.readLiveHeader address = .ok header ∧
    header.kind = .natural ∧ header.persistent = true ∧ header.refCount = 0 ∧
    header.aux0 = promotedTagMarker ∧
    address.value + header.allocationBytes.toNat ≤ state.heapCursor ∧
    headerBytes + 8 ≤ header.allocationBytes.toNat
  decoded : readTag state address = .ok payload

/-- Concrete-only promoted tags remain decoded and accounted for across a
fresh prefix extension. -/
theorem PromotedTagRel.prefixExtension
    {before after : MemoryState} {witness : RefinementWitness}
    {payload : UInt64} {address : Word32}
    (related : PromotedTagRel before witness payload address)
    (extension : before.PrefixExtension after) :
    PromotedTagRel after witness payload address := by
  obtain ⟨header, headerRead, headerKind, persistent, refCount, marker, extent,
      payloadFits⟩ := related.header
  obtain ⟨heap, _, _, minimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header headerRead
  have headerOwned : address.value + headerBytes ≤ before.heapCursor := by
    omega
  have headerAfter := extension.readLiveHeader_eq_ok address header headerOwned headerRead
  have payloadOwned : address.value + headerBytes + 8 ≤ before.heapCursor := by
    omega
  have operationEq : readTag after address = readTag before address := by
    unfold readTag
    simp [heap]
    rw [headerAfter, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind, persistent, marker]
    rw [extension.readUInt64 (address.value + headerBytes) payloadOwned]
  refine {
    mapped := related.mapped
    descriptor := related.descriptor
    header := ⟨header, headerAfter, headerKind, persistent, refCount, marker,
      Nat.le_trans extent extension.cursor, payloadFits⟩
    decoded := ?_ }
  rw [operationEq]
  exact related.decoded

/-- Promoted-tag relations are monotone in proof-only witness metadata. -/
theorem PromotedTagRel.witnessExtension
    {state : MemoryState} {before after : RefinementWitness}
    {payload : UInt64} {address : Word32}
    (related : PromotedTagRel state before payload address)
    (extension : before.Extends after) :
    PromotedTagRel state after payload address := {
  mapped := extension.promotedTags _ _ related.mapped
  descriptor := extension.descriptors _ _ related.descriptor
  header := related.header
  decoded := related.decoded }

/-- Heap-only state refinement. It is bidirectional over every mapped semantic
cell, distinguishes live payload decoding from canonical dead allocations,
and separately accounts for concrete promoted tags. Globals and world/trace
join it in their W6 slices. -/
structure LiveHeapRel (state : MemoryState) (witness : RefinementWitness)
    (semantic : RuntimeState) : Prop where
  frontier : state.FrontierInvariant
  witnessWellFormed : witness.WellFormed
  locationsBeforeNext : ∀ location cell,
    findCell? semantic.heap location = some cell → location < semantic.nextLocation
  /-- Semantic release depth fits in the concrete header capacity. This is
  preserved by every semantic allocation and concrete-only prefix extension. -/
  releaseFuelBound : semantic.heap.length * headerBytes ≤ state.heapCursor
  descriptorsOwned : ∀ address descriptor,
    witness.descriptors.lookup? address = some descriptor →
    address.value + headerBytes ≤ state.heapCursor
  /-- Every proof descriptor names a readable, complete allocation below the
  current cursor. Keeping the full retained extent here is what lets ownership
  writes frame all other decoded cells. -/
  descriptorRegion : ∀ address descriptor,
    witness.descriptors.lookup? address = some descriptor →
    ∃ header,
      Header.read state.memory address = .ok header ∧
      headerBytes ≤ header.allocationBytes.toNat ∧
      header.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + header.allocationBytes.toNat ≤ state.heapCursor
  /-- Descriptor allocations occupy pairwise disjoint intervals. -/
  descriptorDisjoint : ∀ left right leftDescriptor rightDescriptor,
    witness.descriptors.lookup? left = some leftDescriptor →
    witness.descriptors.lookup? right = some rightDescriptor →
    left.value ≠ right.value →
    ∀ leftHeader rightHeader,
      Header.read state.memory left = .ok leftHeader →
      Header.read state.memory right = .ok rightHeader →
      left.value + leftHeader.allocationBytes.toNat ≤ right.value ∨
        right.value + rightHeader.allocationBytes.toNat ≤ left.value
  semanticToConcrete : ∀ location cell,
    findCell? semantic.heap location = some cell →
    ∃ address, witness.locations.lookup? location = some address ∧
      CellRel state witness address cell
  concreteToSemantic : ∀ location address,
    witness.locations.lookup? location = some address →
    ∃ cell, findCell? semantic.heap location = some cell ∧
      CellRel state witness address cell
  promoted : ∀ payload address,
    witness.promotedTags.Contains payload address →
    PromotedTagRel state witness payload address

/-- A witness-mapped semantic cell known to be dead has the canonical
released concrete representation.  This packages the recurring contradiction
against every live-cell constructor for operation-specific fault proofs. -/
theorem LiveHeapRel.deadCellRel
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    DeadCellRel state address := by
  cases mapped with
  | mapped mappedFound =>
      obtain ⟨mappedCell, semanticFound, cellRelation⟩ :=
        related.concreteToSemantic location address mappedFound
      rw [found] at semanticFound
      have cellEq := Option.some.inj semanticFound
      subst mappedCell
      cases cellRelation with
      | live liveRelated =>
          cases liveRelated with
          | constructor _ _ _ _ _ _ _ live => simp_all
          | boxed _ _ _ _ _ live => simp_all
          | natural _ _ _ _ _ _ _ _ _ _ live => simp_all
          | integer _ _ _ _ _ live => simp_all
          | string _ _ _ _ _ live => simp_all
          | array _ _ _ _ _ live => simp_all
          | closure closureRelated =>
              cases closureRelated with
              | closure _ _ _ _ _ _ _ _ _ live => simp_all
      | dead _ _ _ deadRelated => exact deadRelated

/-- Initial proof witness for one generated module. Runtime identity maps are
empty, while the immutable closure dispatch and capture-descriptor tables are
installed before execution begins. -/
def initialWitness (dispatch : ClosureDispatchTable)
    (descriptors : ClosureDescriptorTable) : RefinementWitness :=
  ({} : RefinementWitness).withClosureTables dispatch descriptors

theorem initialWitness_wellFormed (dispatch : ClosureDispatchTable)
    (descriptors : ClosureDescriptorTable) :
    (initialWitness dispatch descriptors).WellFormed := by
  refine {
    locationHeap := ?_
    locationInjective := ?_
    promotedHeap := ?_
    promotedInjective := ?_
    locationPromotionDisjoint := ?_ }
  · intro location address found
    simp [initialWitness, RefinementWitness.withClosureTables,
      LocationMap.lookup?] at found
  · intro left right address leftFound
    simp [initialWitness, RefinementWitness.withClosureTables,
      LocationMap.lookup?] at leftFound
  · intro payload address found
    simp [initialWitness, RefinementWitness.withClosureTables,
      PromotedTags.Contains] at found
  · intro left right address leftFound
    simp [initialWitness, RefinementWitness.withClosureTables,
      PromotedTags.Contains] at leftFound
  · intro location payload left right locationFound
    simp [initialWitness, RefinementWitness.withClosureTables,
      LocationMap.lookup?] at locationFound

/-- Empty semantic and concrete heaps satisfy the complete relation with the
module's closure tables already frozen. This is the W6 execution entry point. -/
theorem LiveHeapRel.initial (dispatch : ClosureDispatchTable)
    (descriptors : ClosureDescriptorTable) :
    LiveHeapRel MemoryState.initial (initialWitness dispatch descriptors)
      ({} : RuntimeState) := by
  refine {
    frontier := MemoryState.initial_frontierInvariant
    witnessWellFormed := initialWitness_wellFormed dispatch descriptors
    locationsBeforeNext := ?_
    releaseFuelBound := ?_
    descriptorsOwned := ?_
    descriptorRegion := ?_
    descriptorDisjoint := ?_
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
  · intro location cell found
    simp [findCell?] at found
  · simp [MemoryState.initial, headerBytes]
  · intro address descriptor found
    simp [initialWitness, RefinementWitness.withClosureTables,
      DescriptorMap.lookup?] at found
  · intro address descriptor found
    simp [initialWitness, RefinementWitness.withClosureTables,
      DescriptorMap.lookup?] at found
  · intro left right leftDescriptor rightDescriptor leftFound
    simp [initialWitness, RefinementWitness.withClosureTables,
      DescriptorMap.lookup?] at leftFound
  · intro location cell found
    simp [findCell?] at found
  · intro location address found
    simp [initialWitness, RefinementWitness.withClosureTables,
      LocationMap.lookup?] at found
  · intro payload address found
    simp [initialWitness, RefinementWitness.withClosureTables,
      PromotedTags.Contains] at found

/-- The public semantic recursive-release fuel always fits within the public
concrete cursor-derived fuel for related heaps. -/
theorem LiveHeapRel.semanticFuel_le_concreteFuel
    {state : MemoryState} {witness : RefinementWitness}
    {semantic : RuntimeState} (related : LiveHeapRel state witness semantic) :
    semantic.heap.length + 1 ≤ state.heapCursor / headerBytes + 1 := by
  have capacity : semantic.heap.length ≤ state.heapCursor / headerBytes :=
    (Nat.le_div_iff_mul_le (by simp [headerBytes])).2 related.releaseFuelBound
  omega

/-- The complete decoded W6.1 heap relation is stable under a fresh concrete
allocation before the ghost witness or semantic heap is extended. -/
theorem LiveHeapRel.prefixExtension
    {before after : MemoryState} {witness : RefinementWitness}
    {semantic : RuntimeState}
    (related : LiveHeapRel before witness semantic)
    (extension : before.PrefixExtension after)
    (frontier : after.FrontierInvariant) :
    LiveHeapRel after witness semantic := by
  refine {
    frontier
    witnessWellFormed := related.witnessWellFormed
    locationsBeforeNext := related.locationsBeforeNext
    releaseFuelBound := Nat.le_trans related.releaseFuelBound extension.cursor
    descriptorsOwned := ?_
    descriptorRegion := ?_
    descriptorDisjoint := ?_
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
  · intro address descriptor found
    exact Nat.le_trans (related.descriptorsOwned address descriptor found)
      extension.cursor
  · intro address descriptor found
    obtain ⟨header, headerRead, minimum, aligned, extent⟩ :=
      related.descriptorRegion address descriptor found
    have headerOwned : address.value + headerBytes ≤ before.heapCursor := by
      omega
    exact ⟨header, by
        rw [extension.readHeader address headerOwned]
        exact headerRead,
      minimum, aligned, Nat.le_trans extent extension.cursor⟩
  · intro left right leftDescriptor rightDescriptor leftFound rightFound
      different leftHeader rightHeader leftRead rightRead
    obtain ⟨oldLeftHeader, _, leftMinimum, _, leftExtent⟩ :=
      related.descriptorRegion left leftDescriptor leftFound
    obtain ⟨oldRightHeader, _, rightMinimum, _, rightExtent⟩ :=
      related.descriptorRegion right rightDescriptor rightFound
    have leftOwned : left.value + headerBytes ≤ before.heapCursor := by omega
    have rightOwned : right.value + headerBytes ≤ before.heapCursor := by omega
    rw [extension.readHeader left leftOwned] at leftRead
    rw [extension.readHeader right rightOwned] at rightRead
    exact related.descriptorDisjoint left right leftDescriptor rightDescriptor
      leftFound rightFound different leftHeader rightHeader leftRead rightRead
  · intro location cell found
    obtain ⟨address, mapped, cellRelated⟩ :=
      related.semanticToConcrete location cell found
    exact ⟨address, mapped, cellRelated.prefixExtension extension⟩
  · intro location address mapped
    obtain ⟨cell, found, cellRelated⟩ :=
      related.concreteToSemantic location address mapped
    exact ⟨cell, found, cellRelated.prefixExtension extension⟩
  · intro payload address mapped
    exact (related.promoted payload address mapped).prefixExtension extension

/-- Adding one descriptor at the old frontier preserves complete descriptor
regions and pairwise disjointness. Allocation-specific proofs provide only
the new region and the lookup equation away from its fresh address. -/
theorem LiveHeapRel.extendDescriptorSpatial
    {before after : MemoryState} {witness nextWitness : RefinementWitness}
    {semantic : RuntimeState} (related : LiveHeapRel before witness semantic)
    (extension : before.PrefixExtension after)
    (newAddress : Word32)
    (freshAddress : newAddress.value = before.heapCursor)
    (lookupOther : ∀ other,
      newAddress.value ≠ other.value →
      nextWitness.descriptors.lookup? other = witness.descriptors.lookup? other)
    (newRegion : ∃ header,
      Header.read after.memory newAddress = .ok header ∧
      headerBytes ≤ header.allocationBytes.toNat ∧
      header.allocationBytes.toNat % target.heapAlignment = 0 ∧
      newAddress.value + header.allocationBytes.toNat ≤ after.heapCursor) :
    (∀ address descriptor,
      nextWitness.descriptors.lookup? address = some descriptor →
      ∃ header,
        Header.read after.memory address = .ok header ∧
        headerBytes ≤ header.allocationBytes.toNat ∧
        header.allocationBytes.toNat % target.heapAlignment = 0 ∧
        address.value + header.allocationBytes.toNat ≤ after.heapCursor) ∧
    (∀ left right leftDescriptor rightDescriptor,
      nextWitness.descriptors.lookup? left = some leftDescriptor →
      nextWitness.descriptors.lookup? right = some rightDescriptor →
      left.value ≠ right.value →
      ∀ leftHeader rightHeader,
        Header.read after.memory left = .ok leftHeader →
      Header.read after.memory right = .ok rightHeader →
      left.value + leftHeader.allocationBytes.toNat ≤ right.value ∨
          right.value + rightHeader.allocationBytes.toNat ≤ left.value) := by
  have wordEq : ∀ left right : Word32, left.value = right.value → left = right := by
    intro left right equal
    cases left
    cases right
    simp_all
  have oldRegion : ∀ address descriptor,
      witness.descriptors.lookup? address = some descriptor →
      ∃ header,
        Header.read after.memory address = .ok header ∧
        headerBytes ≤ header.allocationBytes.toNat ∧
        header.allocationBytes.toNat % target.heapAlignment = 0 ∧
        address.value + header.allocationBytes.toNat ≤ after.heapCursor := by
    intro address descriptor found
    obtain ⟨header, headerRead, minimum, aligned, extent⟩ :=
      related.descriptorRegion address descriptor found
    have headerOwned : address.value + headerBytes ≤ before.heapCursor := by omega
    exact ⟨header, by
        rw [extension.readHeader address headerOwned]
        exact headerRead,
      minimum, aligned, Nat.le_trans extent extension.cursor⟩
  refine ⟨?_, ?_⟩
  · intro address descriptor found
    by_cases isNew : newAddress.value = address.value
    · have addressEq : address = newAddress := wordEq address newAddress isNew.symm
      subst address
      exact newRegion
    · rw [lookupOther address isNew] at found
      exact oldRegion address descriptor found
  · intro left right leftDescriptor rightDescriptor leftFound rightFound different
      leftHeader rightHeader leftRead rightRead
    by_cases leftNew : newAddress.value = left.value
    · by_cases rightNew : newAddress.value = right.value
      · exact False.elim (different (leftNew.symm.trans rightNew))
      · rw [lookupOther right rightNew] at rightFound
        obtain ⟨oldHeader, oldRead, minimum, _, extent⟩ :=
          related.descriptorRegion right rightDescriptor rightFound
        have headerOwned : right.value + headerBytes ≤ before.heapCursor := by omega
        rw [extension.readHeader right headerOwned] at rightRead
        rw [oldRead] at rightRead
        have headerEq := Except.ok.inj rightRead
        subst rightHeader
        right
        rw [← leftNew, freshAddress]
        exact extent
    · by_cases rightNew : newAddress.value = right.value
      · rw [lookupOther left leftNew] at leftFound
        obtain ⟨oldHeader, oldRead, minimum, _, extent⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        have headerOwned : left.value + headerBytes ≤ before.heapCursor := by omega
        rw [extension.readHeader left headerOwned] at leftRead
        rw [oldRead] at leftRead
        have headerEq := Except.ok.inj leftRead
        subst leftHeader
        left
        rw [← rightNew, freshAddress]
        exact extent
      · rw [lookupOther left leftNew] at leftFound
        rw [lookupOther right rightNew] at rightFound
        obtain ⟨oldLeftHeader, _, leftMinimum, _, leftExtent⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        obtain ⟨oldRightHeader, _, rightMinimum, _, rightExtent⟩ :=
          related.descriptorRegion right rightDescriptor rightFound
        have leftOwned : left.value + headerBytes ≤ before.heapCursor := by omega
        have rightOwned : right.value + headerBytes ≤ before.heapCursor := by omega
        rw [extension.readHeader left leftOwned] at leftRead
        rw [extension.readHeader right rightOwned] at rightRead
        exact related.descriptorDisjoint left right leftDescriptor rightDescriptor
          leftFound rightFound different leftHeader rightHeader leftRead rightRead

theorem ConstructorObjectRel.readObjectField_refines
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    {index : Nat} {kind : AbiKind} {value : Value}
    (kindAt : fieldKinds[index]? = some kind)
    (valueAt : semantic.objectFields[index]? = some value) :
    ∃ word, readObjectField state address index = .ok word ∧
      ValueRel witness kind (.word32 word) value :=
  related.objectFields index kind value kindAt valueAt

theorem ConstructorObjectRel.readUSizeField_refines
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    {index : Nat} {value : UInt64}
    (valueAt : semantic.usizeFields[index]? = some value) :
    readUSizeField state address index = .ok value ∧
      ValueRel witness .usize (.word64 value) (.usize value) := by
  exact ⟨related.usizeFields index value valueAt, .usize⟩

/-- The absolute fixed-slot reader agrees with the type-local `USize` relation
after translating through the constructor's object-field prefix. -/
theorem ConstructorObjectRel.readUSizeSlot_refines
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    {slot : Nat} {value : UInt64}
    (slotStart : semantic.objectFields.size ≤ slot)
    (valueAt : semantic.usizeFields[slot - semantic.objectFields.size]? =
      some value) :
    readUSizeSlot state address slot = .ok value ∧
      ValueRel witness .usize (.word64 value) (.usize value) := by
  obtain ⟨header, headerRead, headerKind, _, _, objectCount, usizeCount, _⟩ :=
    related.header
  have constructorHeader := readConstructorHeader_eq_ok_of_readLiveHeader
    state address header headerRead headerKind
  have objectCountEq : header.aux1.toNat = semantic.objectFields.size := by
    rw [objectCount, related.semanticObjectFields]
  have usizeCountEq : header.aux2.toNat = semantic.usizeFields.size := by
    rw [usizeCount, related.semanticUSizeFields]
  have localLt : slot - semantic.objectFields.size <
      semantic.usizeFields.size :=
    (Array.getElem?_eq_some_iff.mp valueAt).1
  have slotEnd : slot <
      semantic.objectFields.size + semantic.usizeFields.size := by omega
  have slotRead : readUSizeSlot state address slot =
      readUSizeField state address (slot - semantic.objectFields.size) := by
    unfold readUSizeSlot
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    rw [objectCountEq, usizeCountEq]
    simp [slotStart, slotEnd]
  rw [slotRead]
  exact related.readUSizeField_refines valueAt

theorem ValueRel.new_constructor_result (witness : RefinementWitness)
    (location : Location) (address : Word32) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) :
    ValueRel (witness.bindConstructor location address info fieldKinds)
      .object (.word32 address) (.object (.heap location)) :=
  .object (.mapped
    (RefinementWitness.lookup_bindConstructor_location
      witness location address info fieldKinds))

theorem ValueRel.new_natural_result (witness : RefinementWitness)
    (location : Location) (address : Word32) (value : Nat) :
    ValueRel (witness.bindNatural location address value)
      .tobject (.word32 address) (.object (.heap location)) :=
  .tobject (.heap (.mapped
    (RefinementWitness.lookup_bindNatural_location witness location address value)))

theorem ValueRel.new_integer_result (witness : RefinementWitness)
    (location : Location) (address : Word32) (value : Int) :
    ValueRel (witness.bindInteger location address value)
      .tobject (.word32 address) (.object (.heap location)) :=
  .tobject (.heap (.mapped
    (RefinementWitness.lookup_bindInteger_location witness location address value)))

theorem ValueRel.new_string_result (witness : RefinementWitness)
    (location : Location) (address : Word32) (value : String) :
    ValueRel (witness.bindString location address value)
      .object (.word32 address) (.object (.heap location)) :=
  .object (.mapped
    (RefinementWitness.lookup_bindString_location witness location address value))

end Fir.Wasm.Concrete
