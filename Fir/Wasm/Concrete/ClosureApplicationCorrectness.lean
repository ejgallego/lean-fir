import Fir.Wasm.Concrete.OwnershipFrameCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Successful closure application is simulated by the concrete ownership
boundary. The theorem covers persistent, exclusive-transfer, and shared-retain
branches; only the shared branch consults the finite refcount resource
precondition. -/
theorem LiveHeapRel.takeClosureApplication_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {function : Lean.Name} {arity : Nat}
    {captures : Array Value}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (sharedCapacity : ∀ parentRuntime,
      setCell runtime location { cell with rc := cell.rc - 1 } =
          .ok parentRuntime →
        ClosureRetainCapacity parentRuntime captures.toList)
    (semanticOperation :
      Fir.LeanIR.Impure.takeClosureApplication runtime location =
        .ok (nextRuntime, function, arity, captures)) :
    ∃ (result : MemoryState) (application : ClosureApplication)
        (captureKinds : Array AbiKind),
      takeClosureApplication state witness.closureDispatch
          witness.closureDescriptors address = .ok (result, application) ∧
      ClosureApplicationRel witness application address function arity
        captureKinds captures ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  have targetOwnershipRelated := targetRelated
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
          obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
              metadataFixed, metadataKinds⟩ := objectRelated.metadata
          have metadataHeader : metadata.header = header :=
            readClosureMetadata_header_eq metadataRead headerRead
          have metadataPersistent :
              metadata.header.persistent = cell.persistent := by
            rw [metadataHeader]
            exact persistent
          have metadataRefCount : metadata.header.refCount.toNat = cell.rc := by
            rw [metadataHeader]
            exact refCount
          obtain ⟨lanes, lanesRead, applicationRelated⟩ :=
            objectRelated.readCaptures
          let application : ClosureApplication := {
            object := address
            function
            arity
            captureKinds
            captures := lanes.toArray }
          have applicationRelated' :
              ClosureApplicationRel witness application address function arity
                captureKinds captures := applicationRelated
          have semanticExpanded := semanticOperation
          unfold Fir.LeanIR.Impure.takeClosureApplication at semanticExpanded
          simp only [getLiveCell, found, live, if_true, Bind.bind, Except.bind]
            at semanticExpanded
          rw [objectEq] at semanticExpanded
          by_cases persistentCase : cell.persistent = true
          · have metadataPersistentTrue : metadata.header.persistent = true :=
              metadataPersistent.trans persistentCase
            simp only [persistentCase, if_true] at semanticExpanded
            have resultEq := Except.ok.inj semanticExpanded
            have runtimeEq : runtime = nextRuntime := by
              injection resultEq
            subst nextRuntime
            refine ⟨state, application, captureKinds, ?_, applicationRelated',
              related⟩
            unfold takeClosureApplication
            rw [metadataRead]
            simp only [Bind.bind, Except.bind]
            rw [metadataKinds, lanesRead]
            simp [application, metadataFunction, metadataArity, metadataKinds,
              metadataPersistentTrue]
            rfl
          · have ordinary : cell.persistent = false := by
              cases persistentValue : cell.persistent <;> simp_all
            have metadataOrdinary : metadata.header.persistent = false :=
              metadataPersistent.trans ordinary
            by_cases zero : cell.rc = 0
            · simp [ordinary, zero] at semanticExpanded
            · by_cases one : cell.rc = 1
              · have metadataOne : metadata.header.refCount = 1 := by
                  apply UInt32.toNat.inj
                  simpa [one] using metadataRefCount
                have explicitSetOperation :
                    setCell runtime location
                        { object := .closure function arity captures
                          rc := 0
                          live := false } = .ok nextRuntime := by
                  cases operation : setCell runtime location
                      { object := .closure function arity captures
                        rc := 0
                        live := false } with
                  | error fault =>
                      simp [ordinary, zero, one, operation] at semanticExpanded
                  | ok deletedRuntime =>
                      simp [ordinary, zero, one, operation] at semanticExpanded
                      have runtimeEq : deletedRuntime = nextRuntime := by
                        have tupleEq := Except.ok.inj semanticExpanded
                        exact congrArg Prod.fst tupleEq
                      subst deletedRuntime
                      rfl
                have setOperation :
                    setCell runtime location { cell with rc := 0, live := false } =
                      .ok nextRuntime := by
                  simpa [objectEq, ordinary] using explicitSetOperation
                have semanticDelete :
                    Fir.LeanIR.Impure.deleteValue runtime
                        (.object (.heap location)) = .ok nextRuntime := by
                  unfold Fir.LeanIR.Impure.deleteValue
                  simp only [getLiveCell, found, live, if_true, Bind.bind,
                    Except.bind]
                  exact setOperation
                obtain ⟨result, concreteDelete, resultRelated, _, _⟩ :=
                  related.deleteObject_refines_with_capacity mapped semanticDelete
                refine ⟨result, application, captureKinds, ?_,
                  applicationRelated', resultRelated⟩
                unfold takeClosureApplication
                rw [metadataRead]
                simp only [Bind.bind, Except.bind]
                rw [metadataKinds, lanesRead]
                simp [application, metadataFunction, metadataArity,
                  metadataOrdinary, metadataOne, concreteDelete]
                rfl
              · have oneLt : 1 < cell.rc := by omega
                have metadataNotZero : metadata.header.refCount ≠ 0 := by
                  intro headerZero
                  apply zero
                  have countZero : (0 : Nat) = cell.rc := by
                    simpa [headerZero] using metadataRefCount
                  exact countZero.symm
                have metadataNotOne : metadata.header.refCount ≠ 1 := by
                  intro headerOne
                  apply one
                  have countOne : (1 : Nat) = cell.rc := by
                    simpa [headerOne] using metadataRefCount
                  exact countOne.symm
                obtain ⟨words, wordsRead, wordsRelated⟩ :=
                  objectRelated.readClosureOwnedReferences
                obtain ⟨parentState, parentRuntime, concreteParent,
                    semanticParent, parentRelated⟩ :=
                  related.decrementReferenceOnce_refines_above_one
                    (descriptors := witness.closureDescriptors) mapped found live
                    ordinary oneLt true
                have semanticParentEq :=
                  targetOwnershipRelated.decValueOnce_above_one_eq ordinary runtime location
                    found oneLt true
                rw [semanticParentEq] at semanticParent
                have parentSet :
                    setCell runtime location { cell with rc := cell.rc - 1 } =
                      .ok parentRuntime := semanticParent
                have explicitParentSet :
                    setCell runtime location
                        { object := .closure function arity captures
                          rc := cell.rc - 1 } = .ok parentRuntime := by
                  simpa [objectEq, ordinary, live] using parentSet
                have semanticTailArray :
                    captures.foldlM (init := parentRuntime) retainOwnedValue =
                      .ok nextRuntime := by
                  cases operation :
                      captures.foldlM (init := parentRuntime) retainOwnedValue with
                  | error fault =>
                      simp [ordinary, zero, one, explicitParentSet, operation]
                        at semanticExpanded
                  | ok finalRuntime =>
                      simp [ordinary, zero, one, explicitParentSet, operation]
                        at semanticExpanded
                      have tupleEq := Except.ok.inj semanticExpanded
                      have runtimeEq : finalRuntime = nextRuntime :=
                        congrArg Prod.fst tupleEq
                      subst finalRuntime
                      rfl
                have semanticTail :
                    captures.toList.foldlM (init := parentRuntime)
                        retainOwnedValue = .ok nextRuntime := by
                  simpa using semanticTailArray
                have filteredTail :
                    (closureOwnedValues captureKinds.toList captures.toList).foldlM
                        (init := parentRuntime) retainOwnedValue =
                      .ok nextRuntime := by
                  rw [← objectRelated.foldlM_retainOwnedValue parentRuntime]
                  exact semanticTail
                obtain ⟨result, concreteTail, resultRelated⟩ :=
                  wordsRelated.foldlM_retainClosureCaptures_refines parentRelated
                    (objectRelated.closureOwnedValuesCapacity parentRuntime
                      (sharedCapacity parentRuntime parentSet)) filteredTail
                refine ⟨result, application, captureKinds, ?_,
                  applicationRelated', resultRelated⟩
                unfold takeClosureApplication
                rw [metadataRead]
                simp only [Bind.bind, Except.bind]
                rw [metadataKinds, lanesRead]
                have metadataZeroFalse :
                    (metadata.header.refCount == 0) = false := by
                  simp [metadataNotZero]
                have metadataOneFalse :
                    (metadata.header.refCount == 1) = false := by
                  simp [metadataNotOne]
                simp [metadataOrdinary, metadataZeroFalse, metadataOneFalse,
                  wordsRead, concreteParent, concreteTail, application,
                  metadataFunction, metadataArity]
                rfl

end Fir.Wasm.Concrete
