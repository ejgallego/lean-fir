import Fir.Wasm.Concrete.Runtime
import Fir.Wasm.Concrete.FreshAllocationCorrectness

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
    header.allocationBytes.toNat = (ConstructorLayout.ofInfo info).allocationBytes ∧
    header.refCount.toNat = 1 ∧
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
    | .uint32 value =>
        field.width = info.size + info.usize ∧
        field.offset + 4 ≤ info.ssize ∧
        readScalarUInt32Field state address field.width field.offset = .ok value
    | .uint64 value =>
        field.width = info.size + info.usize ∧
        field.offset + 8 ≤ info.ssize ∧
        readScalarUInt64Field state address field.width field.offset = .ok value
    | _ => False
  fieldKindsSize : fieldKinds.size = info.size
  objectFields : ∀ index kind value,
    fieldKinds[index]? = some kind →
    semantic.objectFields[index]? = some value →
    ∃ word, readObjectField state address index = .ok word ∧
      ValueRel witness kind (.word32 word) value
  usizeFields : ∀ index value,
    semantic.usizeFields[index]? = some value →
    readUSizeField state address index = .ok value

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
  obtain ⟨header, headerRead, headerKind, allocationBytes, refCount, persistent,
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
      | .uint32 value =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field after address field.width field.offset = .ok value
      | .uint64 value =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field after address field.width field.offset = .ok value
      | _ => False := by
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
    | uint16 value => simp [valueEq] at beforeField
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
    header := ⟨header, headerAfter, headerKind, allocationBytes, refCount,
      persistent, tag, objectCount, usizeCount, scalarCount⟩
    headerOwned := Nat.le_trans related.headerOwned extension.cursor
    extent := Nat.le_trans related.extent extension.cursor
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := scalarFieldsAfter
    fieldKindsSize := related.fieldKindsSize
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
    objectFields := ?_
    usizeFields := related.usizeFields }
  intro index kind value kindAt valueAt
  obtain ⟨word, read, valueRelated⟩ :=
    related.objectFields index kind value kindAt valueAt
  exact ⟨word, read, valueRelated.witnessExtension extension⟩

/-- Relation for live semantic cells implemented by the current W6.1 runtime.
Dead cells, boxes, closures, and other heap objects receive cases in their
own implementation slices rather than being hidden behind a permissive
catch-all. -/
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
        simp [liftMemory, headerKind, ordinary, marker]
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
  | natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
        decoded refCount persistent live =>
      exact .natural (extension.descriptors _ _ descriptor) objectEq headerRead
        headerKind ordinary marker extent limbsFit decoded refCount persistent live

theorem LiveCellRel.headerOwned
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) :
    address.value + headerBytes ≤ state.heapCursor := by
  cases related with
  | constructor _ _ objectRelated _ _ _ _ _ => exact objectRelated.headerOwned
  | natural _ _ headerRead _ _ _ extent _ _ _ _ _ =>
      have minimum :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead).2.2.2.1
      omega

/-- A promoted tag is a concrete allocation without a semantic heap location.
It must decode to the original tagged payload and retain persistent/no-RC
behavior. -/
structure PromotedTagRel (state : MemoryState) (witness : RefinementWitness)
    (payload : UInt64) (address : Word32) : Prop where
  mapped : witness.promotedTags.lookup? payload = some address
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

/-- Heap-only state refinement for the W6.1 live allocation fragment. It is
bidirectional over live semantic cells and separately accounts for concrete
promoted tags. Later slices extend this to dead cells, globals, world/trace,
and the remaining object kinds. -/
structure LiveHeapRel (state : MemoryState) (witness : RefinementWitness)
    (semantic : RuntimeState) : Prop where
  frontier : state.FrontierInvariant
  witnessWellFormed : witness.WellFormed
  locationsBeforeNext : ∀ location cell,
    findCell? semantic.heap location = some cell → location < semantic.nextLocation
  descriptorsOwned : ∀ address descriptor,
    witness.descriptors.lookup? address = some descriptor →
    address.value + headerBytes ≤ state.heapCursor
  semanticToConcrete : ∀ location cell,
    findCell? semantic.heap location = some cell → cell.live = true →
    ∃ address, witness.locations.lookup? location = some address ∧
      LiveCellRel state witness address cell
  concreteToSemantic : ∀ location address,
    witness.locations.lookup? location = some address →
    ∃ cell, findCell? semantic.heap location = some cell ∧ cell.live = true ∧
      LiveCellRel state witness address cell
  promoted : ∀ payload address,
    witness.promotedTags.lookup? payload = some address →
    PromotedTagRel state witness payload address

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
    descriptorsOwned := ?_
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
  · intro address descriptor found
    exact Nat.le_trans (related.descriptorsOwned address descriptor found)
      extension.cursor
  · intro location cell found live
    obtain ⟨address, mapped, cellRelated⟩ :=
      related.semanticToConcrete location cell found live
    exact ⟨address, mapped, cellRelated.prefixExtension extension⟩
  · intro location address mapped
    obtain ⟨cell, found, live, cellRelated⟩ :=
      related.concreteToSemantic location address mapped
    exact ⟨cell, found, live, cellRelated.prefixExtension extension⟩
  · intro payload address mapped
    exact (related.promoted payload address mapped).prefixExtension extension

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
