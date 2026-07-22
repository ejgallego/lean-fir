import Fir.Wasm.Concrete.ConstructorHeapCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

theorem getObjectField_eq_ok_iff_of_cell
    (runtime : RuntimeState) (location : Location) (cell : HeapCell)
    (semantic : ConstructorObject) (index : Nat) (value : Value)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (objectEq : cell.object = .ctor semantic) :
    getObjectField runtime (.object (.heap location)) index = .ok value ↔
      semantic.objectFields[index]? = some value := by
  simp [getObjectField, getConstructor, getLiveCell, found, live]
  simp only [Bind.bind, Except.bind]
  rw [objectEq]
  simp only [Pure.pure, Except.pure]
  cases fieldAt : semantic.objectFields[index]? <;> simp

theorem getUSizeField_eq_ok_iff_of_cell
    (runtime : RuntimeState) (location : Location) (cell : HeapCell)
    (semantic : ConstructorObject) (index : Nat) (value : UInt64)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (objectEq : cell.object = .ctor semantic) :
    getUSizeField runtime (.object (.heap location)) index = .ok (.usize value) ↔
      semantic.usizeFields[index]? = some value := by
  simp [getUSizeField, getConstructor, getLiveCell, found, live]
  simp only [Bind.bind, Except.bind]
  rw [objectEq]
  simp only [Pure.pure, Except.pure]
  cases fieldAt : semantic.usizeFields[index]? <;> simp

theorem getObjectField_eq_error_outOfBounds_iff_of_cell
    (runtime : RuntimeState) (location : Location) (cell : HeapCell)
    (semantic : ConstructorObject) (index : Nat)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (objectEq : cell.object = .ctor semantic) :
    getObjectField runtime (.object (.heap location)) index =
        .error (.objectFieldOutOfBounds index semantic.objectFields.size) ↔
      semantic.objectFields[index]? = none := by
  simp [getObjectField, getConstructor, getLiveCell, found, live]
  simp only [Bind.bind, Except.bind]
  rw [objectEq]
  simp only [Pure.pure, Except.pure]
  cases fieldAt : semantic.objectFields[index]?
  · have outOfBounds := Array.getElem?_eq_none_iff.mp fieldAt
    constructor
    · intro
      exact outOfBounds
    · intro
      rfl
  · have inBounds := (Array.getElem?_eq_some_iff.mp fieldAt).1
    constructor
    · intro impossible
      contradiction
    · intro outOfBounds
      omega

theorem getUSizeField_eq_error_outOfBounds_iff_of_cell
    (runtime : RuntimeState) (location : Location) (cell : HeapCell)
    (semantic : ConstructorObject) (index : Nat)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (objectEq : cell.object = .ctor semantic) :
    getUSizeField runtime (.object (.heap location)) index =
        .error (.usizeFieldOutOfBounds index semantic.usizeFields.size) ↔
      semantic.usizeFields[index]? = none := by
  simp [getUSizeField, getConstructor, getLiveCell, found, live]
  simp only [Bind.bind, Except.bind]
  rw [objectEq]
  simp only [Pure.pure, Except.pure]
  cases fieldAt : semantic.usizeFields[index]?
  · have outOfBounds := Array.getElem?_eq_none_iff.mp fieldAt
    constructor
    · intro
      exact outOfBounds
    · intro
      rfl
  · have inBounds := (Array.getElem?_eq_some_iff.mp fieldAt).1
    constructor
    · intro impossible
      contradiction
    · intro outOfBounds
      omega

/-- A decoded constructor rejects every object-field index outside its
declared semantic array with the exact source-classified bounds fault. -/
theorem ConstructorObjectRel.readObjectField_outOfBounds
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    {index : Nat} (outOfBounds : semantic.objectFields.size ≤ index) :
    readObjectField state address index = .error
      (.source (.objectFieldOutOfBounds index semantic.objectFields.size)) := by
  obtain ⟨header, headerRead, headerKind, _, _, objectCount, _, _⟩ :=
    related.header
  have constructorHeader := readConstructorHeader_eq_ok_of_readLiveHeader
    state address header headerRead headerKind
  have sizeEq : header.aux1.toNat = semantic.objectFields.size := by
    rw [objectCount, related.semanticObjectFields]
  unfold readObjectField
  rw [constructorHeader]
  simp only [Bind.bind, Except.bind]
  rw [sizeEq]
  simp [Nat.not_lt.mpr outOfBounds]
  rfl

/-- A decoded constructor rejects every `USize` index outside its declared
semantic array with the exact source-classified bounds fault. -/
theorem ConstructorObjectRel.readUSizeField_outOfBounds
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    {index : Nat} (outOfBounds : semantic.usizeFields.size ≤ index) :
    readUSizeField state address index = .error
      (.source (.usizeFieldOutOfBounds index semantic.usizeFields.size)) := by
  obtain ⟨header, headerRead, headerKind, _, _, objectCount, usizeCount, _⟩ :=
    related.header
  have constructorHeader := readConstructorHeader_eq_ok_of_readLiveHeader
    state address header headerRead headerKind
  have sizeEq : header.aux2.toNat = semantic.usizeFields.size := by
    rw [usizeCount, related.semanticUSizeFields]
  unfold readUSizeField
  rw [constructorHeader]
  simp only [Bind.bind, Except.bind]
  rw [sizeEq]
  simp [Nat.not_lt.mpr outOfBounds]
  rfl

/-- A successful semantic packed-scalar projection identifies the exact
field selected by its compiler operands. -/
theorem scalarField_of_getScalarField_eq_ok_of_cell
    (runtime : RuntimeState) (location : Location) (cell : HeapCell)
    (semantic : ConstructorObject) (width offset : Nat) (value : ScalarValue)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (objectEq : cell.object = .ctor semantic)
    (projected : getScalarField runtime (.object (.heap location)) width offset =
      .ok (.scalar value)) :
    ∃ field, field ∈ semantic.scalarFields ∧ field.width = width ∧
      field.offset = offset ∧ field.value = value := by
  unfold getScalarField at projected
  simp [getConstructor, getLiveCell, found, live, objectEq, Bind.bind,
    Except.bind] at projected
  simp only [pure, Except.pure] at projected
  cases fieldFound : semantic.scalarFields.find? fun field =>
      field.width == width && field.offset == offset with
  | none =>
      rw [fieldFound] at projected
      contradiction
  | some field =>
      have selected := List.find?_some fieldFound
      have member := List.mem_of_find?_eq_some fieldFound
      rw [fieldFound] at projected
      have valueEq := Value.scalar.inj (Except.ok.inj projected)
      simp at selected
      exact ⟨field, member, selected.1, selected.2, valueEq⟩

/-- Successful semantic scalar projection exposes the related constructor
decoder and its selected packed-field witness. -/
theorem LiveHeapRel.scalarField_of_projected
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {width offset : Nat}
    {value : ScalarValue}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (projected : getScalarField runtime (.object (.heap location)) width offset =
      .ok (.scalar value)) :
    ∃ info fieldKinds semantic field,
      ConstructorObjectRel state witness address info fieldKinds semantic ∧
      field ∈ semantic.scalarFields ∧ field.width = width ∧
      field.offset = offset ∧ field.value = value := by
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  have live : cell.live = true := by
    cases liveEq : cell.live with
    | false =>
        simp [getScalarField, getConstructor, getLiveCell, found, liveEq,
          Bind.bind, Except.bind] at projected
    | true => rfl
  have cellRelated := cellRelation.live_of_eq_true live
  cases cellRelated with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
      persistent cellLive =>
      obtain ⟨field, member, fieldWidth, fieldOffset, fieldValue⟩ :=
        scalarField_of_getScalarField_eq_ok_of_cell runtime location cell _ width
          offset value found live objectEq projected
      exact ⟨_, _, _, field, objectRelated, member, fieldWidth, fieldOffset,
        fieldValue⟩
  | boxed descriptor objectEq objectRelated refCount persistent cellLive =>
      simp [getScalarField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected
  | natural descriptor objectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      simp [getScalarField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected
  | string descriptor objectEq objectRelated refCount persistent cellLive =>
      simp [getScalarField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected
  | closure closureRelated =>
      obtain ⟨function, arity, captures, objectEq⟩ := closureRelated.objectEq
      simp [getScalarField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected

/-- Checked packed `UInt8` projection refines semantic `getScalarField`. -/
theorem LiveHeapRel.readScalarUInt8Field_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {width offset : Nat} {value : UInt8}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (projected : getScalarField runtime (.object (.heap location)) width offset =
      .ok (.scalar (.uint8 value))) :
    readScalarUInt8Field state address width offset = .ok value ∧
      ValueRel witness .uint8 (.word32 (Word32.ofUInt8 value))
        (.scalar (.uint8 value)) := by
  obtain ⟨info, fieldKinds, semantic, field, objectRelated, member, fieldWidth,
      fieldOffset, fieldValue⟩ := related.scalarField_of_projected mapped projected
  have observed := objectRelated.semanticScalarFields field member
  rw [fieldValue] at observed
  simp only at observed
  rw [← fieldWidth, ← fieldOffset]
  exact ⟨observed.2.2, BoxedScalar.valueRel witness (.uint8 value)⟩

/-- Checked packed `UInt16` projection refines semantic `getScalarField`. -/
theorem LiveHeapRel.readScalarUInt16Field_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {width offset : Nat}
    {value : UInt16}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (projected : getScalarField runtime (.object (.heap location)) width offset =
      .ok (.scalar (.uint16 value))) :
    readScalarUInt16Field state address width offset = .ok value ∧
      ValueRel witness .uint16 (.word32 (Word32.ofUInt16 value))
        (.scalar (.uint16 value)) := by
  obtain ⟨info, fieldKinds, semantic, field, objectRelated, member, fieldWidth,
      fieldOffset, fieldValue⟩ := related.scalarField_of_projected mapped projected
  have observed := objectRelated.semanticScalarFields field member
  rw [fieldValue] at observed
  simp only at observed
  rw [← fieldWidth, ← fieldOffset]
  exact ⟨observed.2.2, BoxedScalar.valueRel witness (.uint16 value)⟩

/-- Checked packed `UInt32` projection refines semantic `getScalarField`. -/
theorem LiveHeapRel.readScalarUInt32Field_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {width offset : Nat}
    {value : UInt32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (projected : getScalarField runtime (.object (.heap location)) width offset =
      .ok (.scalar (.uint32 value))) :
    readScalarUInt32Field state address width offset = .ok value ∧
      ValueRel witness .uint32 (.word32 (Word32.ofUInt32 value))
        (.scalar (.uint32 value)) := by
  obtain ⟨info, fieldKinds, semantic, field, objectRelated, member, fieldWidth,
      fieldOffset, fieldValue⟩ := related.scalarField_of_projected mapped projected
  have observed := objectRelated.semanticScalarFields field member
  rw [fieldValue] at observed
  simp only at observed
  rw [← fieldWidth, ← fieldOffset]
  exact ⟨observed.2.2, BoxedScalar.valueRel witness (.uint32 value)⟩

/-- Checked packed `UInt64` projection refines semantic `getScalarField`. -/
theorem LiveHeapRel.readScalarUInt64Field_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {width offset : Nat}
    {value : UInt64}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (projected : getScalarField runtime (.object (.heap location)) width offset =
      .ok (.scalar (.uint64 value))) :
    readScalarUInt64Field state address width offset = .ok value ∧
      ValueRel witness .uint64 (.word64 value) (.scalar (.uint64 value)) := by
  obtain ⟨info, fieldKinds, semantic, field, objectRelated, member, fieldWidth,
      fieldOffset, fieldValue⟩ := related.scalarField_of_projected mapped projected
  have observed := objectRelated.semanticScalarFields field member
  rw [fieldValue] at observed
  simp only at observed
  rw [← fieldWidth, ← fieldOffset]
  exact ⟨observed.2.2, BoxedScalar.valueRel witness (.uint64 value)⟩

/-- Reading a concrete constructor tag returns the exact semantic constructor
tag recorded by the decoded-object relation. -/
theorem ConstructorObjectRel.readTag_refines
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic) :
    readTag state address = .ok (UInt64.ofNat semantic.tag) := by
  obtain ⟨header, headerRead, headerKind, _, tag, _, _, _⟩ := related.header
  have heap := (MemoryState.PrefixExtension.readLiveHeader_facts
    state address header headerRead).1
  unfold readTag
  simp [heap]
  rw [headerRead]
  simp only [Bind.bind, Except.bind]
  have tag64 : header.aux0.toUInt64 = UInt64.ofNat semantic.tag := by
    rw [← tag]
    simp
  have constructorBeq : (ObjectKind.constructor == ObjectKind.constructor) = true := by
    decide
  simp [liftMemory, headerKind, tag64, constructorBeq]
  rfl

/-- A concrete tag read cannot reinterpret a canonical released header: it
reports the exact address-indexed source fault before inspecting object kind or
tag metadata. -/
theorem DeadCellRel.readTag_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) :
    readTag state address =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨_, _, addressHeap, _, _, _, _, _, _, _, _, _, _, _⟩ := related.header
  unfold readTag
  rw [addressHeap]
  simp only
  rw [related.readLiveHeader_eq]
  rfl

/-- The shared constructor-header decoder rejects a released allocation before
examining constructor metadata. -/
theorem DeadCellRel.readConstructorHeader_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) :
    readConstructorHeader state address =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨_, _, addressHeap, _, _, _, _, _, _, _, _, _, _, _⟩ := related.header
  unfold readConstructorHeader
  simp [addressHeap]
  rw [related.readLiveHeader_eq]
  rfl

theorem DeadCellRel.readObjectField_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (index : Nat) :
    readObjectField state address index =
      .error (.sourceAddress (.deadObject address)) := by
  unfold readObjectField
  rw [related.readConstructorHeader_eq]
  rfl

theorem DeadCellRel.readUSizeField_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (index : Nat) :
    readUSizeField state address index =
      .error (.sourceAddress (.deadObject address)) := by
  unfold readUSizeField
  rw [related.readConstructorHeader_eq]
  rfl

theorem DeadCellRel.readScalarUInt8Field_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (slotIndex byteOffset : Nat) :
    readScalarUInt8Field state address slotIndex byteOffset =
      .error (.sourceAddress (.deadObject address)) := by
  unfold readScalarUInt8Field
  rw [related.readConstructorHeader_eq]
  rfl

theorem DeadCellRel.readScalarUInt16Field_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (slotIndex byteOffset : Nat) :
    readScalarUInt16Field state address slotIndex byteOffset =
      .error (.sourceAddress (.deadObject address)) := by
  unfold readScalarUInt16Field
  rw [related.readConstructorHeader_eq]
  rfl

theorem DeadCellRel.readScalarUInt32Field_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (slotIndex byteOffset : Nat) :
    readScalarUInt32Field state address slotIndex byteOffset =
      .error (.sourceAddress (.deadObject address)) := by
  unfold readScalarUInt32Field
  rw [related.readConstructorHeader_eq]
  rfl

theorem DeadCellRel.readScalarUInt64Field_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (slotIndex byteOffset : Nat) :
    readScalarUInt64Field state address slotIndex byteOffset =
      .error (.sourceAddress (.deadObject address)) := by
  unfold readScalarUInt64Field
  rw [related.readConstructorHeader_eq]
  rfl

/-- Exact tagged references decode through `readTag`, whether their physical
word is immediate or a promoted-tag allocation. -/
theorem LiveHeapRel.readTaggedReferenceTag_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {word : Word32} {payload : UInt64}
    (related : LiveHeapRel state witness runtime)
    (valueRelated : TaggedReferenceRel witness word payload) :
    readTag state word = .ok payload := by
  cases valueRelated with
  | immediate payload fits =>
      unfold readTag
      simp [Word32.classify_encodeImmediate, Word32.decode_encodeImmediate]
      rfl
  | promoted found =>
      exact (related.promoted payload word found).decoded

/-- The checked concrete object projection refines the actual W2 semantic
`getObjectField` operation for a mapped live constructor. -/
theorem LiveHeapRel.readObjectField_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat} {kind : AbiKind} {value : Value}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (kindAt : fieldKinds[index]? = some kind)
    (projected : getObjectField runtime (.object (.heap location)) index = .ok value) :
    ∃ word, readObjectField state address index = .ok word ∧
      ValueRel witness kind (.word32 word) value := by
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  have live : cell.live = true := by
    cases liveEq : cell.live with
    | false =>
        simp [getObjectField, getConstructor, getLiveCell, found, liveEq,
          Bind.bind, Except.bind] at projected
    | true => rfl
  have cellRelated := cellRelation.live_of_eq_true live
  cases cellRelated with
  | constructor storedDescriptor objectEq objectRelated _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have descriptorEq := Option.some.inj descriptor
      cases descriptorEq
      have valueAt := (getObjectField_eq_ok_iff_of_cell runtime location cell _ index
        value found live objectEq).mp projected
      exact objectRelated.readObjectField_refines kindAt valueAt
  | boxed _ objectEq _ _ _ _ =>
      simp [getObjectField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected
  | natural _ objectEq _ _ _ _ _ _ _ _ _ =>
      simp [getObjectField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected
  | string storedDescriptor _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  | closure closureRelated =>
      obtain ⟨function, arity, captureKinds, storedDescriptor⟩ :=
        closureRelated.descriptor
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible

/-- The checked concrete `USize` projection refines the actual W2 semantic
`getUSizeField` operation. -/
theorem LiveHeapRel.readUSizeField_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat} {value : UInt64}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (projected : getUSizeField runtime (.object (.heap location)) index =
      .ok (.usize value)) :
    readUSizeField state address index = .ok value ∧
      ValueRel witness .usize (.word64 value) (.usize value) := by
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  have live : cell.live = true := by
    cases liveEq : cell.live with
    | false =>
        simp [getUSizeField, getConstructor, getLiveCell, found, liveEq,
          Bind.bind, Except.bind] at projected
    | true => rfl
  have cellRelated := cellRelation.live_of_eq_true live
  cases cellRelated with
  | constructor storedDescriptor objectEq objectRelated _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have descriptorEq := Option.some.inj descriptor
      cases descriptorEq
      have valueAt := (getUSizeField_eq_ok_iff_of_cell runtime location cell _ index
        value found live objectEq).mp projected
      exact objectRelated.readUSizeField_refines valueAt
  | boxed _ objectEq _ _ _ _ =>
      simp [getUSizeField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected
  | natural _ objectEq _ _ _ _ _ _ _ _ _ =>
      simp [getUSizeField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected
  | string storedDescriptor _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  | closure closureRelated =>
      obtain ⟨function, arity, captureKinds, storedDescriptor⟩ :=
        closureRelated.descriptor
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible

/-- An exact semantic object-projection bounds fault is preserved by the
checked concrete reader for the mapped live constructor. -/
theorem LiveHeapRel.readObjectField_outOfBounds_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (projected : getObjectField runtime (.object (.heap location)) index =
      .error (.objectFieldOutOfBounds index info.size)) :
    readObjectField state address index =
      .error (.source (.objectFieldOutOfBounds index info.size)) := by
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  have live : cell.live = true := by
    cases liveEq : cell.live with
    | false =>
        simp [getObjectField, getConstructor, getLiveCell, found, liveEq,
          Bind.bind, Except.bind] at projected
    | true => rfl
  have cellRelated := cellRelation.live_of_eq_true live
  cases cellRelated with
  | constructor storedDescriptor objectEq objectRelated _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have descriptorEq := Option.some.inj descriptor
      cases descriptorEq
      have semanticSize := objectRelated.semanticObjectFields
      rw [← semanticSize] at projected
      have missing := (getObjectField_eq_error_outOfBounds_iff_of_cell runtime
        location cell _ index found live objectEq).mp projected
      have outOfBounds := Array.getElem?_eq_none_iff.mp missing
      simpa [semanticSize] using
        objectRelated.readObjectField_outOfBounds outOfBounds
  | boxed storedDescriptor _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  | natural storedDescriptor _ _ _ _ _ _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  | string storedDescriptor _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  | closure closureRelated =>
      obtain ⟨function, arity, captureKinds, storedDescriptor⟩ :=
        closureRelated.descriptor
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible

/-- An exact semantic `USize`-projection bounds fault is preserved by the
checked concrete reader for the mapped live constructor. -/
theorem LiveHeapRel.readUSizeField_outOfBounds_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (projected : getUSizeField runtime (.object (.heap location)) index =
      .error (.usizeFieldOutOfBounds index info.usize)) :
    readUSizeField state address index =
      .error (.source (.usizeFieldOutOfBounds index info.usize)) := by
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  have live : cell.live = true := by
    cases liveEq : cell.live with
    | false =>
        simp [getUSizeField, getConstructor, getLiveCell, found, liveEq,
          Bind.bind, Except.bind] at projected
    | true => rfl
  have cellRelated := cellRelation.live_of_eq_true live
  cases cellRelated with
  | constructor storedDescriptor objectEq objectRelated _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have descriptorEq := Option.some.inj descriptor
      cases descriptorEq
      have semanticSize := objectRelated.semanticUSizeFields
      rw [← semanticSize] at projected
      have missing := (getUSizeField_eq_error_outOfBounds_iff_of_cell runtime
        location cell _ index found live objectEq).mp projected
      have outOfBounds := Array.getElem?_eq_none_iff.mp missing
      simpa [semanticSize] using
        objectRelated.readUSizeField_outOfBounds outOfBounds
  | boxed storedDescriptor _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  | natural storedDescriptor _ _ _ _ _ _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  | string storedDescriptor _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible
  | closure closureRelated =>
      obtain ⟨function, arity, captureKinds, storedDescriptor⟩ :=
        closureRelated.descriptor
      rw [storedDescriptor] at descriptor
      have impossible := Option.some.inj descriptor
      cases impossible

/-- Object mutation performs the same checked read before storing, so an
out-of-bounds object slot fails without changing concrete memory. -/
theorem ConstructorObjectRel.writeObjectField_outOfBounds
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    {index : Nat} (word : Word32)
    (outOfBounds : semantic.objectFields.size ≤ index) :
    writeObjectField state address index word = .error
      (.source (.objectFieldOutOfBounds index semantic.objectFields.size)) := by
  unfold writeObjectField
  rw [related.readObjectField_outOfBounds outOfBounds]
  rfl

/-- `USize` mutation rejects an out-of-bounds slot before its payload store,
retaining the exact semantic bounds fault. -/
theorem ConstructorObjectRel.writeUSizeField_outOfBounds
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    {index : Nat} (value : UInt64)
    (outOfBounds : semantic.usizeFields.size ≤ index) :
    writeUSizeField state address index value = .error
      (.source (.usizeFieldOutOfBounds index semantic.usizeFields.size)) := by
  obtain ⟨header, headerRead, headerKind, _, _, _, usizeCount, _⟩ :=
    related.header
  have constructorHeader := readConstructorHeader_eq_ok_of_readLiveHeader
    state address header headerRead headerKind
  have sizeEq : header.aux2.toNat = semantic.usizeFields.size := by
    rw [usizeCount, related.semanticUSizeFields]
  unfold writeUSizeField
  rw [constructorHeader]
  simp only [Bind.bind, Except.bind]
  rw [sizeEq]
  simp [Nat.not_lt.mpr outOfBounds]
  rfl

/-- A mapped live constructor's object setter preserves an exact semantic
bounds failure and performs no concrete update. -/
theorem LiveHeapRel.writeObjectField_outOfBounds_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (field : Value) (word : Word32)
    (outOfBounds : semantic.objectFields.size ≤ index) :
    writeObjectField state address index word = .error
        (.source (.objectFieldOutOfBounds index semantic.objectFields.size)) ∧
      setObjectField runtime (.object (.heap location)) index field =
        .error (.objectFieldOutOfBounds index semantic.objectFields.size) := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated _ _ _ _ _ =>
      rw [descriptor] at descriptorFound
      have descriptorEq := Option.some.inj descriptorFound
      cases descriptorEq
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      constructor
      · exact objectRelated.writeObjectField_outOfBounds word outOfBounds
      · simp [setObjectField, modifyConstructor, getConstructor, getLiveCell,
          found, live, objectEq, Bind.bind, Except.bind]
        simp only [pure, Except.pure]
        rw [dif_neg (Nat.not_lt.mpr outOfBounds)]
  | boxed _ storedObjectEq _ _ _ _ =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural _ storedObjectEq _ _ _ _ _ _ _ _ _ =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string _ storedObjectEq _ _ _ _ =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- A mapped live constructor's `USize` setter preserves an exact semantic
bounds failure and performs no concrete update. -/
theorem LiveHeapRel.writeUSizeField_outOfBounds_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject} {index : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (value : UInt64)
    (outOfBounds : semantic.usizeFields.size ≤ index) :
    writeUSizeField state address index value = .error
        (.source (.usizeFieldOutOfBounds index semantic.usizeFields.size)) ∧
      setUSizeField runtime (.object (.heap location)) index (.usize value) =
        .error (.usizeFieldOutOfBounds index semantic.usizeFields.size) := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  cases targetRelated with
  | constructor _ storedObjectEq objectRelated _ _ _ _ _ =>
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      constructor
      · exact objectRelated.writeUSizeField_outOfBounds value outOfBounds
      · simp [setUSizeField, modifyConstructor, getConstructor, getLiveCell,
          found, live, objectEq, Bind.bind, Except.bind]
        simp only [pure, Except.pure]
        rw [dif_neg (Nat.not_lt.mpr outOfBounds)]
  | boxed _ storedObjectEq _ _ _ _ =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural _ storedObjectEq _ _ _ _ _ _ _ _ _ =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string _ storedObjectEq _ _ _ _ =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- Concrete constructor tag lookup refines semantic `getTag` for a mapped
live constructor. -/
theorem LiveHeapRel.readTag_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {tag : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (semanticTag : getTag runtime (.object (.heap location)) = .ok tag) :
    readTag state address = .ok (UInt64.ofNat tag) := by
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  have live : cell.live = true := by
    cases liveEq : cell.live with
    | false =>
        simp [getTag, getLiveCell, found, liveEq, Bind.bind, Except.bind]
          at semanticTag
    | true => rfl
  have cellRelated := cellRelation.live_of_eq_true live
  cases cellRelated with
  | constructor _ objectEq objectRelated _ _ _ _ _ =>
      simp [getTag, getLiveCell, found, live] at semanticTag
      simp only [Bind.bind, Except.bind] at semanticTag
      rw [objectEq] at semanticTag
      change Except.ok _ = Except.ok tag at semanticTag
      have tagEq := Except.ok.inj semanticTag
      rw [← tagEq]
      exact objectRelated.readTag_refines
  | boxed _ objectEq _ _ _ _ =>
      simp [getTag, getLiveCell, found, live] at semanticTag
      simp only [Bind.bind, Except.bind] at semanticTag
      rw [objectEq] at semanticTag
      simp at semanticTag
  | natural _ objectEq _ _ _ _ _ _ _ _ _ =>
      simp [getTag, getLiveCell, found, live] at semanticTag
      simp only [Bind.bind, Except.bind] at semanticTag
      rw [objectEq] at semanticTag
      simp at semanticTag
  | string _ objectEq _ _ _ _ =>
      simp [getTag, getLiveCell, found, live] at semanticTag
      simp only [Bind.bind, Except.bind] at semanticTag
      rw [objectEq] at semanticTag
      simp at semanticTag
  | closure closureRelated =>
      obtain ⟨function, arity, captures, objectEq⟩ := closureRelated.objectEq
      simp [getTag, getLiveCell, found, live] at semanticTag
      simp only [Bind.bind, Except.bind] at semanticTag
      rw [objectEq] at semanticTag
      simp at semanticTag

/-- A mapped stale constructor reference preserves `deadObject` through tag
observation.  As at the sharing boundary, the concrete side retains the wasm32
address while FIR retains the represented semantic location. -/
theorem LiveHeapRel.readTag_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    readTag state address =
        .error (.sourceAddress (.deadObject address)) ∧
      getTag runtime (.object (.heap location)) =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  exact ⟨deadRelated.readTag_eq, by
    simp [getTag, getLiveCell, found, dead]
    rfl⟩

/-- A stale mapped object-field projection fails before index or payload
decoding on both sides. -/
theorem LiveHeapRel.readObjectField_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) (index : Nat) :
    readObjectField state address index =
        .error (.sourceAddress (.deadObject address)) ∧
      getObjectField runtime (.object (.heap location)) index =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  exact ⟨deadRelated.readObjectField_eq index, by
    simp [getObjectField, getConstructor, getLiveCell, found, dead]
    rfl⟩

/-- A stale mapped `USize` projection has the same exact dead-object boundary. -/
theorem LiveHeapRel.readUSizeField_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) (index : Nat) :
    readUSizeField state address index =
        .error (.sourceAddress (.deadObject address)) ∧
      getUSizeField runtime (.object (.heap location)) index =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  exact ⟨deadRelated.readUSizeField_eq index, by
    simp [getUSizeField, getConstructor, getLiveCell, found, dead]
    rfl⟩

/-- All supported packed-integer readers share one stale-reference boundary;
the scalar coordinate and width-specific payload decoder are unreachable. -/
theorem LiveHeapRel.readScalarFields_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) (slotIndex byteOffset : Nat) :
    readScalarUInt8Field state address slotIndex byteOffset =
        .error (.sourceAddress (.deadObject address)) ∧
      readScalarUInt16Field state address slotIndex byteOffset =
        .error (.sourceAddress (.deadObject address)) ∧
      readScalarUInt32Field state address slotIndex byteOffset =
        .error (.sourceAddress (.deadObject address)) ∧
      readScalarUInt64Field state address slotIndex byteOffset =
        .error (.sourceAddress (.deadObject address)) ∧
      getScalarField runtime (.object (.heap location)) slotIndex byteOffset =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  refine ⟨deadRelated.readScalarUInt8Field_eq slotIndex byteOffset,
    deadRelated.readScalarUInt16Field_eq slotIndex byteOffset,
    deadRelated.readScalarUInt32Field_eq slotIndex byteOffset,
    deadRelated.readScalarUInt64Field_eq slotIndex byteOffset, ?_⟩
  simp [getScalarField, getConstructor, getLiveCell, found, dead]
  rfl

/-- Complete `.getTag` wrapper for its representation-polymorphic object ABI.
Mapped constructors use the heap theorem above; exact tagged values use the
immediate/promoted decoder relation without consulting the semantic heap. -/
theorem LiveHeapRel.readTag_tobject_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {word : Word32} {value : Value} {tag : Nat}
    (related : LiveHeapRel state witness runtime)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (semanticTag : getTag runtime value = .ok tag) :
    readTag state word = .ok (UInt64.ofNat tag) := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped => exact related.readTag_refines mapped semanticTag
      | tagged taggedRelated =>
          have tagEq := Except.ok.inj semanticTag
          rw [← tagEq]
          simpa using related.readTaggedReferenceTag_refines taggedRelated

end Fir.Wasm.Concrete
