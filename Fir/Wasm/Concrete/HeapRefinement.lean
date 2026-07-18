import Fir.Wasm.Concrete.Runtime
import Fir.Wasm.Concrete.FrontierCorrectness

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
    header.aux0.toNat = info.cidx ∧
    header.aux1.toNat = info.size ∧
    header.aux2.toNat = info.usize ∧
    header.aux3.toNat = info.ssize
  semanticTag : semantic.tag = info.cidx
  semanticObjectFields : semantic.objectFields.size = info.size
  semanticUSizeFields : semantic.usizeFields.size = info.usize
  semanticScalarFields : semantic.scalarFields = []
  fieldKindsSize : fieldKinds.size = info.size
  objectFields : ∀ index kind value,
    fieldKinds[index]? = some kind →
    semantic.objectFields[index]? = some value →
    ∃ word, readObjectField state address index = .ok word ∧
      ValueRel witness kind (.word32 word) value
  usizeFields : ∀ index value,
    semantic.usizeFields[index]? = some value →
    readUSizeField state address index = .ok value

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
      (decoded : readNatural state address = .ok value)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      LiveCellRel state witness address cell

/-- A promoted tag is a concrete allocation without a semantic heap location.
It must decode to the original tagged payload and retain persistent/no-RC
behavior. -/
structure PromotedTagRel (state : MemoryState) (witness : RefinementWitness)
    (payload : UInt64) (address : Word32) : Prop where
  mapped : witness.promotedTags.lookup? payload = some address
  descriptor : witness.descriptors.lookup? address = some (.promotedTag payload)
  header : ∃ header,
    state.readLiveHeader address = .ok header ∧
    header.kind = .natural ∧ header.persistent = true ∧ header.refCount = 0
  decoded : readTag state address = .ok payload

/-- Heap-only state refinement for the W6.1 live allocation fragment. It is
bidirectional over live semantic cells and separately accounts for concrete
promoted tags. Later slices extend this to dead cells, globals, world/trace,
and the remaining object kinds. -/
structure LiveHeapRel (state : MemoryState) (witness : RefinementWitness)
    (semantic : RuntimeState) : Prop where
  frontier : state.FrontierInvariant
  witnessWellFormed : witness.WellFormed
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
