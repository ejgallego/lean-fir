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
