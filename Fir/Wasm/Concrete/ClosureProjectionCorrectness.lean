import Fir.Wasm.Concrete.ConstructorHeapCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Complete-heap closure matching agrees with the exact source-visible
function/arity/fixed-count predicate for a mapped live closure. -/
theorem LiveHeapRel.closureMatches_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {function : Lean.Name} {arity : Nat} {captures : Array Value}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (expectedFunction : Lean.Name) (expectedArity expectedFixed : Nat) :
    closureMatches state witness.closureDispatch witness.closureDescriptors address
        expectedFunction expectedArity expectedFixed =
      .ok (if function == expectedFunction && arity == expectedArity &&
          captures.size == expectedFixed then 1 else 0) := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | integer descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      cases closureRelated with
      | @closure storedFunction storedArity captureKinds storedCaptures header _
          storedObjectEq objectRelated headerRead headerKind descriptorLookup
          fixedCount extent refCount persistent cellLive =>
          rw [objectEq] at storedObjectEq
          have identity := HeapObject.closure.inj storedObjectEq
          obtain ⟨functionEq, arityEq, capturesEq⟩ := identity
          subst storedFunction
          subst storedArity
          subst storedCaptures
          exact objectRelated.matches_eq expectedFunction expectedArity expectedFixed

/-- Complete-heap typed closure capture projection returns the concrete lane
related to the corresponding semantic capture. -/
theorem LiveHeapRel.projectClosureCapture_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {function : Lean.Name} {arity : Nat} {captures : Array Value}
    {captureKinds : Array AbiKind} {index : Nat} {kind : AbiKind} {value : Value}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.closure function arity captureKinds))
    (kindAt : captureKinds[index]? = some kind)
    (valueAt : captures[index]? = some value) :
    ∃ lane,
      projectClosureCapture state witness.closureDispatch witness.closureDescriptors
          address function arity captures.size index kind = .ok lane ∧
        ValueRel witness kind lane value := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | integer descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      cases closureRelated with
      | @closure storedFunction storedArity storedKinds storedCaptures header _
          storedObjectEq objectRelated headerRead headerKind descriptorLookup
          fixedCount extent refCount persistent cellLive =>
          rw [objectEq] at storedObjectEq
          have identity := HeapObject.closure.inj storedObjectEq
          obtain ⟨functionEq, arityEq, capturesEq⟩ := identity
          subst storedFunction
          subst storedArity
          subst storedCaptures
          rw [objectRelated.descriptor] at descriptorFound
          have kindsEq := AllocationDescriptor.closure.inj
            (Option.some.inj descriptorFound)
          have storedKindsEq : storedKinds = captureKinds := kindsEq.2.2
          subst captureKinds
          exact objectRelated.project index kind value kindAt valueAt

end Fir.Wasm.Concrete
