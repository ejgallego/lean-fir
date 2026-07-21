import Fir.Wasm.Concrete.Runtime
import Fir.Wasm.Concrete.FreshAllocationCorrectness
import Fir.Wasm.Concrete.ClosureHeapCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

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
    header.persistent = false ∧
    header.aux0.toNat = semantic.tag ∧
    header.aux1.toNat = info.size ∧
    header.aux2.toNat = info.usize ∧
    header.aux3.toNat = info.ssize
  headerOwned : address.value + headerBytes ≤ state.heapCursor
  extent : address.value + (ConstructorLayout.ofInfo info).allocationBytes ≤
    state.heapCursor
  semanticObjectFields : semantic.objectFields.size = info.size
  semanticUSizeFields : semantic.usizeFields.size = info.usize
  /-- W6.2 packages the compiler's verified `UInt32`/`UInt64` packed fields.
  Every represented field carries the compiler-shaped scalar base, stays
  within the declared packed region, and reads back from concrete memory. -/
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
  obtain ⟨header, headerRead, headerKind, allocationBytes, persistent,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header
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
  refine {
    header := ⟨header, headerAfter, headerKind, allocationBytes, persistent,
      tag, objectCount, usizeCount, scalarCount⟩
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

/-- Exact decoded relation for one canonical heap-backed scalar box. The
semantic type/value pair is recovered from `kind` and `scalar`; no source
location identity is stored in linear memory. -/
structure BoxedObjectRel (state : MemoryState) (address : Word32)
    (kind : BoxedScalarKind) (scalar : BoxedScalar) (header : Header) : Prop where
  scalarKind : scalar.kind = kind
  headerRead : state.readLiveHeader address = .ok header
  headerKind : header.kind = .boxed
  ordinary : header.persistent = false
  allocationBytes : header.allocationBytes.toNat =
    align8 (headerBytes + target.semanticSlotBytes)
  kindCode : header.aux0 = kind.code
  payloadBytes : header.aux1 = UInt32.ofNat kind.payloadBytes
  reserved2 : header.aux2 = 0
  reserved3 : header.aux3 = 0
  headerOwned : address.value + headerBytes ≤ state.heapCursor
  extent : address.value + header.allocationBytes.toNat ≤ state.heapCursor
  decoded : readBoxedScalar state kind address = .ok scalar

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
      (ordinary : header.persistent = false)
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
    ordinary := related.ordinary
    allocationBytes := related.allocationBytes
    kindCode := related.kindCode
    payloadBytes := related.payloadBytes
    reserved2 := related.reserved2
    reserved3 := related.reserved3
    headerOwned := Nat.le_trans related.headerOwned extension.cursor
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
  | natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
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
      apply LiveCellRel.natural descriptor objectEq headerAfter headerKind ordinary marker
        (Nat.le_trans extent extension.cursor) limbsFit
      · rw [decoderEq]
        exact decoded
      · exact refCount
      · exact persistent
      · exact live
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
  | natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
        decoded refCount persistent live =>
      exact .natural (extension.descriptors _ _ descriptor) objectEq headerRead
        headerKind ordinary marker extent limbsFit decoded refCount persistent live
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
  | natural _ _ headerRead _ _ _ extent _ _ _ _ _ =>
      have minimum :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead).2.2.2.1
      omega
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
  | natural descriptor _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, descriptor⟩
  | closure closureRelated =>
      cases closureRelated with
      | closure _ objectRelated _ _ _ _ _ _ _ _ _ =>
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

end Fir.Wasm.Concrete
