import FirTalos.ConcreteRuntime
import Fir.Wasm.WellFormed

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete

/--
Dynamic meaning of the validator's reset/reuse capacity evidence.

The relation deliberately covers both sides of `reset`: constructor results
are ordinary object lanes, while reset results are reuse-token lanes. A
definitely empty constructor is tagged and therefore resets to physical zero.
Retained evidence permits reset to return zero for a shared or persistent
object; when the value names a heap allocation, the concrete live header
carries the validated lower bound.
-/
inductive ReuseCapacityValueRel
    (heap : MemoryState) (witness : RefinementWitness) :
    ReuseCapacityEvidence → AbiKind → LaneValue → Value → Prop where
  | emptyObject
      (related :
        ValueRel witness kind (.word32 word)
          (.object (.tagged payload))) :
      ReuseCapacityValueRel heap witness .emptyToken kind (.word32 word)
        (.object (.tagged payload))
  | emptyToken :
      ReuseCapacityValueRel heap witness .emptyToken .reuseToken
        (.word32 Word32.zero) (.reuseToken none)
  | retainedObject
      (related :
        ValueRel witness kind (.word32 address)
          (.object (.heap location)))
      (headerRead : heap.readLiveHeader address = .ok header)
      (minimum : available ≤ header.allocationBytes.toNat) :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available) kind
        (.word32 address) (.object (.heap location))
  | retainedEmptyToken :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available)
        .reuseToken (.word32 Word32.zero) (.reuseToken none)
  | retainedToken
      (related :
        ValueRel witness .reuseToken (.word32 address)
          (.reuseToken (some location)))
      (headerRead : heap.readLiveHeader address = .ok header)
      (minimum : available ≤ header.allocationBytes.toNat) :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available)
        .reuseToken (.word32 address) (.reuseToken (some location))

/-- A decoded constructor relation supplies the exact dynamic lower bound
recorded when the validator sees its direct allocation. -/
theorem ReuseCapacityValueRel.retainedObject_of_constructor
    {heap : MemoryState} {witness : RefinementWitness}
    {address : Word32} {location : Location}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {object : ConstructorObject} {kind : AbiKind}
    (valueRelated :
      ValueRel witness kind (.word32 address)
        (.object (.heap location)))
    (objectRelated :
      ConstructorObjectRel heap witness address info fieldKinds object) :
    ReuseCapacityValueRel heap witness
      (.retainedAtLeast (ConstructorLayout.ofInfo info).allocationBytes)
      kind (.word32 address) (.object (.heap location)) := by
  obtain ⟨header, headerRead, _, allocationBytes, _, _, _, _⟩ :=
    objectRelated.header
  exact .retainedObject valueRelated headerRead allocationBytes

/-- At reuse-token kind, definitely-empty evidence fixes both the semantic
token and its physical word. -/
theorem ReuseCapacityValueRel.emptyToken_eq
    {heap : MemoryState} {witness : RefinementWitness}
    {lane : LaneValue} {token : Value}
    (related :
      ReuseCapacityValueRel heap witness .emptyToken .reuseToken lane token) :
    lane = .word32 Word32.zero ∧ token = .reuseToken none := by
  cases related with
  | emptyObject valueRelated => cases valueRelated
  | emptyToken => exact ⟨rfl, rfl⟩

/-- Retained evidence at reuse-token kind is either the zero fallback or a
nonzero mapped token whose live header realizes the tracked capacity. -/
theorem ReuseCapacityValueRel.retainedToken_cases
    {heap : MemoryState} {witness : RefinementWitness}
    {available : Nat} {lane : LaneValue} {token : Value}
    (related :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available)
        .reuseToken lane token) :
    (lane = .word32 Word32.zero ∧ token = .reuseToken none) ∨
      ∃ location address header,
        lane = .word32 address ∧
        token = .reuseToken (some location) ∧
        ValueRel witness .reuseToken (.word32 address)
          (.reuseToken (some location)) ∧
        heap.readLiveHeader address = .ok header ∧
        available ≤ header.allocationBytes.toNat := by
  cases related with
  | retainedObject valueRelated _ _ => cases valueRelated
  | retainedEmptyToken => exact .inl ⟨rfl, rfl⟩
  | retainedToken valueRelated headerRead minimum =>
      exact .inr ⟨_, _, _, rfl, rfl, valueRelated, headerRead, minimum⟩

/--
The central W6.6dg bridge: static fitting evidence and its dynamic header
meaning imply the exact retained-layout premise used by concrete reuse.
-/
theorem ReuseCapacityValueRel.reuseToken_some_layoutFits
    {heap : MemoryState} {witness : RefinementWitness}
    {facts : ReuseCapacityFacts} {tokenId : FVarId}
    {info : LCNF.CtorInfo} {evidence : ReuseCapacityEvidence}
    {location : Location} {address : Word32} {header : Header}
    (related :
      ReuseCapacityValueRel heap witness evidence .reuseToken
        (.word32 address) (.reuseToken (some location)))
    (fitting :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
    (headerRead : heap.readLiveHeader address = .ok header) :
    (ConstructorLayout.ofInfo info).allocationBytes ≤
      header.allocationBytes.toNat := by
  cases related with
  | retainedToken _ relatedHeaderRead minimum =>
      have layoutMinimum :=
        findFittingReuseCapacityEvidence?_retained_layoutFits
          facts tokenId info _ fitting
      rw [headerRead] at relatedHeaderRead
      injection relatedHeaderRead with headerEq
      subst header
      exact Nat.le_trans layoutMinimum minimum

/--
Operation-level reuse refinement with no free `layoutFits` premise. The
validator supplies a fitting fact, and `ReuseCapacityValueRel` ties that fact
to the exact live header consumed by `reuseStep`.
-/
theorem reuseStep_some_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {oldInfo : LCNF.CtorInfo}
    {oldFieldKinds : Array AbiKind} {old : ConstructorObject}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {resultKind : AbiKind} {fields : List Word32}
    {semanticFields : Array Value} {updateHeader : Bool}
    {physicalArgs : List Wasm.Value} {header : Header}
    {facts : ReuseCapacityFacts} {tokenId : FVarId}
    {evidence : ReuseCapacityEvidence}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (address, fields))
    (capacityRelated :
      ReuseCapacityValueRel initial.host.runtime.heap witness evidence
        .reuseToken (.word32 address) (.reuseToken (some location)))
    (capacityFitting :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor oldInfo oldFieldKinds))
    (objectEq : cell.object = .ctor old)
    (objectRelated : ConstructorObjectRel initial.host.runtime.heap witness
      address oldInfo oldFieldKinds old)
    (headerRead : initial.host.runtime.heap.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (refCount : header.refCount.toNat = cell.rc)
    (persistent : header.persistent = cell.persistent)
    (ordinary : cell.persistent = false)
    (cellLive : cell.live = true)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields.toArray[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultKindSupported : resultKind = .object ∨ resultKind = .tobject) :
    ∃ heap nextRuntime,
      let nextWitness := witness.rebindConstructor address info fieldKinds
      reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)] (replaceHeap initial heap) ∧
      WitnessTransport witness nextWitness ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        nextRuntime ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value)) (.object (.heap location)) ∧
      reuse runtime (.reuseToken (some location)) info updateHeader
          semanticFields = .ok (nextRuntime, .object (.heap location)) := by
  have layoutFits :=
    capacityRelated.reuseToken_some_layoutFits capacityFitting headerRead
  exact reuseStep_some_of_refines runtimeRelated argsLength decoded mapped found
    descriptor objectEq objectRelated headerRead headerKind refCount persistent
    ordinary cellLive layoutFits arity semanticArity fieldKindsSize
    fieldKindsValid fieldRelated tagFits objectFieldsFit usizeFieldsFit
    scalarBytesFit resultKindSupported

end FirTalos.Concrete
