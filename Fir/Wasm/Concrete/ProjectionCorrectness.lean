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

/-- Reading a concrete constructor tag returns the exact semantic constructor
tag recorded by the decoded-object relation. -/
theorem ConstructorObjectRel.readTag_refines
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic) :
    readTag state address = .ok (UInt64.ofNat semantic.tag) := by
  obtain ⟨header, headerRead, headerKind, _, _, tag, _, _, _⟩ := related.header
  have heap := (MemoryState.PrefixExtension.readLiveHeader_facts
    state address header headerRead).1
  unfold readTag
  simp [heap]
  rw [headerRead]
  simp only [Bind.bind, Except.bind]
  have tag64 : header.aux0.toUInt64 = UInt64.ofNat info.cidx := by
    rw [← tag]
    simp
  have constructorBeq : (ObjectKind.constructor == ObjectKind.constructor) = true := by
    decide
  simp [liftMemory, headerKind, related.semanticTag, tag64, constructorBeq]
  rfl

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
  obtain ⟨cell, found, live, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
  cases cellRelated with
  | constructor storedDescriptor objectEq objectRelated _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have descriptorEq := Option.some.inj descriptor
      cases descriptorEq
      have valueAt := (getObjectField_eq_ok_iff_of_cell runtime location cell _ index
        value found live objectEq).mp projected
      exact objectRelated.readObjectField_refines kindAt valueAt
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      simp [getObjectField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected

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
  obtain ⟨cell, found, live, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
  cases cellRelated with
  | constructor storedDescriptor objectEq objectRelated _ _ _ _ _ =>
      rw [storedDescriptor] at descriptor
      have descriptorEq := Option.some.inj descriptor
      cases descriptorEq
      have valueAt := (getUSizeField_eq_ok_iff_of_cell runtime location cell _ index
        value found live objectEq).mp projected
      exact objectRelated.readUSizeField_refines valueAt
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      simp [getUSizeField, getConstructor, getLiveCell, found, live] at projected
      simp only [Bind.bind, Except.bind] at projected
      rw [objectEq] at projected
      simp at projected

/-- Concrete constructor tag lookup refines semantic `getTag` for a mapped
live constructor. -/
theorem LiveHeapRel.readTag_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {tag : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (semanticTag : getTag runtime (.object (.heap location)) = .ok tag) :
    readTag state address = .ok (UInt64.ofNat tag) := by
  obtain ⟨cell, found, live, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
  cases cellRelated with
  | constructor _ objectEq objectRelated _ _ _ _ _ =>
      simp [getTag, getLiveCell, found, live] at semanticTag
      simp only [Bind.bind, Except.bind] at semanticTag
      rw [objectEq] at semanticTag
      change Except.ok _ = Except.ok tag at semanticTag
      have tagEq := Except.ok.inj semanticTag
      rw [← tagEq]
      exact objectRelated.readTag_refines
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      simp [getTag, getLiveCell, found, live] at semanticTag
      simp only [Bind.bind, Except.bind] at semanticTag
      rw [objectEq] at semanticTag
      simp at semanticTag

end Fir.Wasm.Concrete
