import Fir.Wasm.Concrete.ExternalCorrectness
import Fir.Wasm.Concrete.OwnershipFrameCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

theorem ConcreteError.toTrap_injective : Function.Injective ConcreteError.toTrap := by
  intro left right equal
  cases left <;> cases right <;> simp_all [ConcreteError.toTrap]

/-- Address-indexed source failures become exact FIR runtime faults once the
whole-heap witness identifies the semantic location represented by the word. -/
inductive ConcreteAddressFaultRel (witness : RefinementWitness) :
    ConcreteAddressFault → RuntimeFault → Prop where
  | deadObject
      (related : HeapReferenceRel witness address location) :
      ConcreteAddressFaultRel witness
        (.deadObject address)
        (.deadObject location)
  | referenceCountUnderflow
      (related : HeapReferenceRel witness address location) :
      ConcreteAddressFaultRel witness
        (.referenceCountUnderflow address)
        (.referenceCountUnderflow location)

inductive ConcreteSourceFailureRel (witness : RefinementWitness) :
    ConcreteSourceFailure → RuntimeFault → Prop where
  | runtime (fault : RuntimeFault) :
      ConcreteSourceFailureRel witness (.runtime fault) fault
  | address {failure : ConcreteAddressFault} {fault : RuntimeFault}
      (related : ConcreteAddressFaultRel witness failure fault) :
      ConcreteSourceFailureRel witness (.address failure) fault

/-- Only source-classified concrete errors can correspond to a FIR runtime
fault. Target failures are excluded by construction. -/
inductive ConcreteErrorSourceRel (witness : RefinementWitness) :
    ConcreteError → RuntimeFault → Prop where
  | source (fault : RuntimeFault) :
      ConcreteErrorSourceRel witness (.source fault) fault
  | sourceAddress {failure : ConcreteAddressFault} {fault : RuntimeFault}
      (related : ConcreteAddressFaultRel witness failure fault) :
      ConcreteErrorSourceRel witness (.sourceAddress failure) fault

theorem ConcreteErrorSourceRel.toTrap
    {witness : RefinementWitness} {failure : ConcreteError}
    {fault : RuntimeFault}
    (related : ConcreteErrorSourceRel witness failure fault) :
    ∃ sourceFailure,
      failure.toTrap = .source sourceFailure ∧
        ConcreteSourceFailureRel witness sourceFailure fault := by
  cases related with
  | source fault => exact ⟨.runtime fault, rfl, .runtime fault⟩
  | sourceAddress addressRelated =>
      exact ⟨.address _, rfl, .address addressRelated⟩

/-- Ordered ownership slots preserve the first recursively reached source
fault. Any successful prefix of child releases advances both related heaps;
the failing child then determines the exact concrete error and semantic fault,
and no later child is visited. -/
theorem OwnershipValuesRel.foldlM_fault_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {words : List Word32} {values : List Value} {fuel : Nat}
    {descriptors : ClosureDescriptorTable} {fault : RuntimeFault}
    (related : OwnershipValuesRel witness words values)
    (heap : LiveHeapRel state witness runtime)
    (admissible : RuntimeFault → Prop)
    (faultAdmissible : admissible fault)
    (recurseSuccess : ∀ {before : MemoryState}
        {semantic nextSemantic : RuntimeState}
        {location : Location} {address : Word32},
      LiveHeapRel before witness semantic →
      witness.locations.lookup? location = some address →
      Fir.LeanIR.Impure.decLocationFuel fuel semantic location =
        .ok nextSemantic →
      ∃ after,
        decrementReferenceOnceFuel fuel before address true descriptors =
            .ok after ∧
          LiveHeapRel after witness nextSemantic)
    (recurseFault : ∀ {before : MemoryState} {semantic : RuntimeState}
        {location : Location} {address : Word32} {childFault : RuntimeFault},
      LiveHeapRel before witness semantic →
      witness.locations.lookup? location = some address →
      Fir.LeanIR.Impure.decLocationFuel fuel semantic location =
        .error childFault →
      admissible childFault →
      ∃ failure,
        decrementReferenceOnceFuel fuel before address true descriptors =
            .error failure ∧
          ConcreteErrorSourceRel witness failure childFault)
    (semanticOperation :
      values.foldlM (init := runtime) (fun next value =>
        match value with
        | .object (.heap child) =>
            Fir.LeanIR.Impure.decLocationFuel fuel next child
        | _ => .ok next) = .error fault) :
    ∃ failure,
      words.foldlM (init := state) (fun next child =>
        decrementReferenceOnceFuel fuel next child true descriptors) =
          .error failure ∧
      ConcreteErrorSourceRel witness failure fault := by
  induction related generalizing state runtime fault with
  | nil =>
      simp only [List.foldlM_nil] at semanticOperation
      contradiction
  | @cons word value words values head tail ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at semanticOperation ⊢
      rcases head.releaseStep heap fuel descriptors with heapStep | noOpStep
      · obtain ⟨location, valueEq, mapped⟩ := heapStep
        subst value
        simp only at semanticOperation
        cases childEq :
            Fir.LeanIR.Impure.decLocationFuel fuel runtime location with
        | error childFault =>
            rw [childEq] at semanticOperation
            have faultEq : childFault = fault :=
              Except.error.inj semanticOperation
            subst fault
            obtain ⟨failure, concreteHead, faultRelated⟩ :=
              recurseFault heap mapped childEq faultAdmissible
            exact ⟨failure, by rw [concreteHead], faultRelated⟩
        | ok nextRuntime =>
            rw [childEq] at semanticOperation
            obtain ⟨nextState, concreteHead, nextHeap⟩ :=
              recurseSuccess heap mapped childEq
            obtain ⟨failure, concreteTail, faultRelated⟩ :=
              ih nextHeap faultAdmissible semanticOperation
            refine ⟨failure, ?_, faultRelated⟩
            rw [concreteHead]
            exact concreteTail
      · obtain ⟨notHeap, concreteHead⟩ := noOpStep
        have semanticHead :
            (match value with
            | .object (.heap child) =>
                Fir.LeanIR.Impure.decLocationFuel fuel runtime child
            | _ => .ok runtime) = .ok runtime := by
          cases value with
          | object reference =>
              cases reference with
              | heap location => exact False.elim (notHeap location rfl)
              | tagged payload => rfl
          | usize usize => rfl
          | scalar scalar => rfl
          | erased => rfl
          | reuseToken location => rfl
        rw [semanticHead] at semanticOperation
        obtain ⟨failure, concreteTail, faultRelated⟩ :=
          ih heap faultAdmissible semanticOperation
        refine ⟨failure, ?_, faultRelated⟩
        rw [concreteHead]
        exact concreteTail

/-- Complete same-fuel recursive fault refinement for one mapped heap
location. The only excluded semantic error is release-fuel exhaustion: its
concrete counterpart is intentionally target-classified and belongs to T4S.
Every source-classified fault, including one reached after releasing a
constructor or closure parent and any successful child prefix, retains its
exact witness-indexed concrete relation. -/
theorem LiveHeapRel.decrementReferenceOnceFuel_fault_refines
    {fuel : Nat} {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {fault : RuntimeFault}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticOperation :
      Fir.LeanIR.Impure.decLocationFuel fuel runtime location =
        .error fault) :
    ∃ failure,
      decrementReferenceOnceFuel fuel state address check
          witness.closureDescriptors =
        .error failure ∧
      ConcreteErrorSourceRel witness failure fault := by
  induction fuel generalizing state runtime location address fault check with
  | zero =>
      have fuelEq :
          (.malformed "reference-count release fuel exhausted" : RuntimeFault) =
            fault := by
        simpa [Fir.LeanIR.Impure.decLocationFuel] using semanticOperation
      exact False.elim (notFuel fuelEq.symm)
  | succ fuel ih =>
      obtain ⟨cell, found, cellRelation⟩ :=
        related.concreteToSemantic location address mapped
      cases liveEq : cell.live with
      | false =>
          have heapReference : HeapReferenceRel witness address location :=
            .mapped mapped
          have deadRelated :=
            related.deadCellRel heapReference found liveEq
          have semanticDead :
              Fir.LeanIR.Impure.decLocationFuel (fuel + 1) runtime location =
                .error (.deadObject location) := by
            simp [Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found, liveEq]
            rfl
          have faultEq : fault = .deadObject location :=
            (Except.error.inj (semanticDead.symm.trans semanticOperation)).symm
          subst fault
          exact ⟨.sourceAddress (.deadObject address),
            deadRelated.decrementReferenceOnceFuel_eq (fuel + 1) check
              witness.closureDescriptors,
            .sourceAddress (.deadObject heapReference)⟩
      | true =>
          have targetRelated := cellRelation.live_of_eq_true liveEq
          by_cases persistentCase : cell.persistent = true
          · have semanticSuccess :=
              targetRelated.decLocationFuel_persistent_eq persistentCase runtime
                location found fuel
            rw [semanticSuccess] at semanticOperation
            contradiction
          · have ordinary : cell.persistent = false := by
              cases value : cell.persistent
              · rfl
              · simp [value] at persistentCase
            by_cases zeroCase : cell.rc = 0
            · have concreteUnderflow :=
                targetRelated.decrementReferenceOnceFuel_underflow_eq ordinary
                  zeroCase fuel check witness.closureDescriptors
              have semanticUnderflow :=
                targetRelated.decLocationFuel_underflow_eq ordinary zeroCase
                  runtime location found fuel
              have faultEq : fault = .referenceCountUnderflow location :=
                (Except.error.inj
                  (semanticUnderflow.symm.trans semanticOperation)).symm
              subst fault
              exact ⟨.sourceAddress (.referenceCountUnderflow address),
                concreteUnderflow,
                .sourceAddress
                  (.referenceCountUnderflow (.mapped mapped))⟩
            · by_cases oneLt : 1 < cell.rc
              · obtain ⟨_, _, _, semanticSuccess, _⟩ :=
                  related.decrementReferenceOnceFuel_refines_above_one
                    (descriptors := witness.closureDescriptors) mapped found
                      liveEq ordinary oneLt fuel check
                rw [semanticSuccess] at semanticOperation
                contradiction
              · have one : cell.rc = 1 := by omega
                cases targetRelated with
                | @boxed kind scalar header _ descriptor objectEq objectRelated
                      refCount persistent cellLive =>
                    let leafCell : NonrecursiveCell cell :=
                      .inl (.inl (.inl ⟨kind, scalar, objectEq⟩))
                    obtain ⟨_, _, _, semanticSuccess, _⟩ :=
                      related.decrementReferenceOnceFuel_refines_leaf_one
                        (descriptors := witness.closureDescriptors) mapped found
                          liveEq leafCell ordinary one fuel check
                    rw [semanticSuccess] at semanticOperation
                    contradiction
                | @natural value header _ descriptor objectEq headerRead
                      headerKind marker extent limbsFit decoded refCount
                      persistent cellLive =>
                    let leafCell : NonrecursiveCell cell :=
                      .inl (.inl (.inr ⟨value, objectEq⟩))
                    obtain ⟨_, _, _, semanticSuccess, _⟩ :=
                      related.decrementReferenceOnceFuel_refines_leaf_one
                        (descriptors := witness.closureDescriptors) mapped found
                          liveEq leafCell ordinary one fuel check
                    rw [semanticSuccess] at semanticOperation
                    contradiction
                | @integer value header _ descriptor objectEq objectRelated
                      refCount persistent cellLive =>
                    let leafCell : NonrecursiveCell cell :=
                      .inr ⟨value, objectEq⟩
                    obtain ⟨_, _, _, semanticSuccess, _⟩ :=
                      related.decrementReferenceOnceFuel_refines_leaf_one
                        (descriptors := witness.closureDescriptors) mapped found
                          liveEq leafCell ordinary one fuel check
                    rw [semanticSuccess] at semanticOperation
                    contradiction
                | @string value header _ descriptor objectEq objectRelated
                      refCount persistent cellLive =>
                    let leafCell : NonrecursiveCell cell :=
                      .inl (.inr ⟨value, objectEq⟩)
                    obtain ⟨_, _, _, semanticSuccess, _⟩ :=
                      related.decrementReferenceOnceFuel_refines_leaf_one
                        (descriptors := witness.closureDescriptors) mapped found
                          liveEq leafCell ordinary one fuel check
                    rw [semanticSuccess] at semanticOperation
                    contradiction
                | @constructor info fieldKinds semantic header _ descriptor
                      objectEq objectRelated headerRead headerKind refCount
                      persistent cellLive =>
                    obtain ⟨words, ownedRead, ownershipRelated⟩ :=
                      objectRelated.readOwnedReferences headerRead
                    obtain ⟨released, memory, releasedOperation, releasedEq,
                        headerWrite, finalValid, deadRelated⟩ :=
                      releaseHeader related.frontier headerRead
                        objectRelated.headerOwned
                    obtain ⟨_, rawRead, _, _, _, _⟩ :=
                      MemoryState.PrefixExtension.readLiveHeader_facts state
                        address header headerRead
                    have headerInBounds :
                        address.value + headerBytes ≤ state.memory.size :=
                      Nat.le_trans objectRelated.headerOwned
                        related.frontier.cursorInBounds
                    let replacement : HeapCell :=
                      { cell with rc := 0, live := false }
                    have targetAfter :
                        CellRel released witness address replacement :=
                      .dead (by simp [replacement]) (by simp [replacement])
                        ⟨.constructor info fieldKinds, descriptor⟩ deadRelated
                    obtain ⟨parentRuntime, parentSemantic, parentRelated⟩ :=
                      related.setCell_of_headerWrite mapped found descriptor
                        rawRead releasedEq headerInBounds headerWrite rfl
                          finalValid targetAfter
                    let releaseChild :
                        RuntimeState → Fir.LeanIR.Impure.Value →
                          Except Fir.LeanIR.Impure.RuntimeFault RuntimeState :=
                      fun next value =>
                        match value with
                        | .object (.heap child) =>
                            Fir.LeanIR.Impure.decLocationFuel fuel next child
                        | _ => .ok next
                    have semanticFoldArray :
                        Array.foldlM releaseChild parentRuntime
                            semantic.objectFields =
                          .error fault := by
                      simp only [Fir.LeanIR.Impure.decLocationFuel, getLiveCell,
                        found, liveEq, ↓reduceIte, Bind.bind, Except.bind]
                        at semanticOperation
                      rw [if_neg (by simp [ordinary])] at semanticOperation
                      rw [if_neg zeroCase, if_neg oneLt] at semanticOperation
                      rw [parentSemantic] at semanticOperation
                      rw [objectEq] at semanticOperation
                      change Array.foldlM releaseChild parentRuntime
                        semantic.objectFields = .error fault at semanticOperation
                      exact semanticOperation
                    have semanticFoldList :
                        semantic.objectFields.toList.foldlM
                            (init := parentRuntime) releaseChild =
                          .error fault := by
                      simpa only [Array.foldlM_toList] using semanticFoldArray
                    have recurseSuccess : ∀ {before : MemoryState}
                        {semanticState nextSemantic : RuntimeState}
                        {childLocation : Location} {childAddress : Word32},
                        LiveHeapRel before witness semanticState →
                        witness.locations.lookup? childLocation =
                          some childAddress →
                        Fir.LeanIR.Impure.decLocationFuel fuel semanticState
                            childLocation =
                          .ok nextSemantic →
                        ∃ after,
                          decrementReferenceOnceFuel fuel before childAddress
                              true witness.closureDescriptors =
                            .ok after ∧
                          LiveHeapRel after witness nextSemantic := by
                      intro before semanticState nextSemantic childLocation
                        childAddress childRelated childMapped childOperation
                      exact childRelated.decrementReferenceOnceFuel_refines
                        childMapped true childOperation
                    have recurseFault : ∀ {before : MemoryState}
                        {semanticState : RuntimeState}
                        {childLocation : Location} {childAddress : Word32}
                        {childFault : RuntimeFault},
                        LiveHeapRel before witness semanticState →
                        witness.locations.lookup? childLocation =
                          some childAddress →
                        Fir.LeanIR.Impure.decLocationFuel fuel semanticState
                            childLocation =
                          .error childFault →
                        childFault ≠
                          .malformed
                            "reference-count release fuel exhausted" →
                        ∃ failure,
                          decrementReferenceOnceFuel fuel before childAddress
                              true witness.closureDescriptors =
                            .error failure ∧
                          ConcreteErrorSourceRel witness failure
                            childFault := by
                      intro before semanticState childLocation childAddress
                        childFault childRelated childMapped childOperation
                          childNotFuel
                      exact ih childRelated childMapped true childNotFuel
                        childOperation
                    obtain ⟨failure, concreteFold, faultRelated⟩ :=
                      ownershipRelated.foldlM_fault_refines parentRelated
                        (fun childFault =>
                          childFault ≠
                            .malformed
                              "reference-count release fuel exhausted")
                        notFuel recurseSuccess recurseFault semanticFoldList
                    have addressHeap :=
                      (MemoryState.PrefixExtension.readLiveHeader_facts state
                        address header headerRead).1
                    have notPromoted : header.isPromotedTag = false := by
                      have different :
                          (ObjectKind.constructor == ObjectKind.natural) =
                            false := by decide
                      have headerOrdinary : header.persistent = false :=
                        persistent.trans ordinary
                      simp [Header.isPromotedTag, headerKind, headerOrdinary,
                        different]
                    have headerOrdinary : header.persistent = false :=
                      persistent.trans ordinary
                    have concreteOperation :
                        decrementReferenceOnceFuel (fuel + 1) state address
                            check witness.closureDescriptors =
                          .error failure := by
                      simp only [decrementReferenceOnceFuel]
                      rw [addressHeap, headerRead]
                      simp only [Bind.bind, Except.bind, liftMemory]
                      rw [if_neg (by simp [notPromoted])]
                      rw [if_neg (by simp [headerOrdinary])]
                      have headerNonzero : header.refCount ≠ 0 := by
                        intro zero
                        rw [zero] at refCount
                        simp at refCount
                        omega
                      rw [if_neg (by simpa using headerNonzero)]
                      rw [refCount, if_neg oneLt]
                      have ownedReadWithDescriptors :
                          readOwnedReferences state address header
                              witness.closureDescriptors =
                            .ok words := by
                        simpa [readOwnedReferences, headerKind] using ownedRead
                      rw [ownedReadWithDescriptors, releasedOperation]
                      exact concreteFold
                    exact ⟨failure, concreteOperation, faultRelated⟩
                | closure closureRelated =>
                    cases closureRelated with
                    | @closure function arity captureKinds captures header _
                          objectEq objectRelated headerRead headerKind
                          descriptorLookup fixedCount extent refCount
                          persistent cellLive =>
                        let localClosure :
                            ClosureCellRel state witness address cell :=
                          .closure objectEq objectRelated headerRead headerKind
                            descriptorLookup fixedCount extent refCount
                              persistent cellLive
                        obtain ⟨words, closureWordsRead, ownershipRelated⟩ :=
                          objectRelated.readClosureOwnedReferences
                        have ownedRead :
                            readOwnedReferences state address header
                                witness.closureDescriptors =
                              .ok words := by
                          simpa [readOwnedReferences, headerKind,
                            descriptorLookup,
                            objectRelated.captureKindsSize, fixedCount] using
                              closureWordsRead
                        obtain ⟨released, memory, releasedOperation, releasedEq,
                            headerWrite, finalValid, deadRelated⟩ :=
                          releaseHeader related.frontier headerRead
                            localClosure.headerOwned
                        obtain ⟨_, rawRead, _, _, _, _⟩ :=
                          MemoryState.PrefixExtension.readLiveHeader_facts state
                            address header headerRead
                        have headerInBounds :
                            address.value + headerBytes ≤ state.memory.size :=
                          Nat.le_trans localClosure.headerOwned
                            related.frontier.cursorInBounds
                        let replacement : HeapCell :=
                          { cell with rc := 0, live := false }
                        have targetAfter :
                            CellRel released witness address replacement :=
                          .dead (by simp [replacement])
                            (by simp [replacement])
                            ⟨.closure function arity captureKinds,
                              objectRelated.descriptor⟩ deadRelated
                        obtain ⟨parentRuntime, parentSemantic,
                            parentRelated⟩ :=
                          related.setCell_of_headerWrite mapped found
                            objectRelated.descriptor rawRead releasedEq
                              headerInBounds headerWrite rfl finalValid
                                targetAfter
                        let releaseChild :
                            RuntimeState → Fir.LeanIR.Impure.Value →
                              Except Fir.LeanIR.Impure.RuntimeFault
                                RuntimeState :=
                          fun next value =>
                            match value with
                            | .object (.heap child) =>
                                Fir.LeanIR.Impure.decLocationFuel fuel next child
                            | _ => .ok next
                        have semanticFoldArray :
                            Array.foldlM releaseChild parentRuntime captures =
                              .error fault := by
                          simp only [Fir.LeanIR.Impure.decLocationFuel,
                            getLiveCell, found, liveEq, ↓reduceIte, Bind.bind,
                            Except.bind] at semanticOperation
                          rw [if_neg (by simp [ordinary])] at semanticOperation
                          rw [if_neg zeroCase, if_neg oneLt] at semanticOperation
                          rw [parentSemantic] at semanticOperation
                          rw [objectEq] at semanticOperation
                          change Array.foldlM releaseChild parentRuntime
                            captures = .error fault at semanticOperation
                          exact semanticOperation
                        have semanticFoldList :
                            captures.toList.foldlM (init := parentRuntime)
                                releaseChild =
                              .error fault := by
                          simpa only [Array.foldlM_toList] using
                            semanticFoldArray
                        have semanticOwnedFoldList :
                            (closureOwnedValues captureKinds.toList
                                captures.toList).foldlM
                                (init := parentRuntime) releaseChild =
                              .error fault := by
                          have foldEq :=
                            objectRelated.foldlM_closureOwnedValues fuel
                              parentRuntime
                          unfold releaseChild
                          exact foldEq.symm.trans semanticFoldList
                        have recurseSuccess : ∀ {before : MemoryState}
                            {semanticState nextSemantic : RuntimeState}
                            {childLocation : Location}
                            {childAddress : Word32},
                            LiveHeapRel before witness semanticState →
                            witness.locations.lookup? childLocation =
                              some childAddress →
                            Fir.LeanIR.Impure.decLocationFuel fuel semanticState
                                childLocation =
                              .ok nextSemantic →
                            ∃ after,
                              decrementReferenceOnceFuel fuel before
                                  childAddress true
                                  witness.closureDescriptors =
                                .ok after ∧
                              LiveHeapRel after witness nextSemantic := by
                          intro before semanticState nextSemantic childLocation
                            childAddress childRelated childMapped childOperation
                          exact
                            childRelated.decrementReferenceOnceFuel_refines
                              childMapped true childOperation
                        have recurseFault : ∀ {before : MemoryState}
                            {semanticState : RuntimeState}
                            {childLocation : Location}
                            {childAddress : Word32}
                            {childFault : RuntimeFault},
                            LiveHeapRel before witness semanticState →
                            witness.locations.lookup? childLocation =
                              some childAddress →
                            Fir.LeanIR.Impure.decLocationFuel fuel semanticState
                                childLocation =
                              .error childFault →
                            childFault ≠
                              .malformed
                                "reference-count release fuel exhausted" →
                            ∃ failure,
                              decrementReferenceOnceFuel fuel before
                                  childAddress true
                                  witness.closureDescriptors =
                                .error failure ∧
                              ConcreteErrorSourceRel witness failure
                                childFault := by
                          intro before semanticState childLocation childAddress
                            childFault childRelated childMapped childOperation
                              childNotFuel
                          exact ih childRelated childMapped true childNotFuel
                            childOperation
                        obtain ⟨failure, concreteFold, faultRelated⟩ :=
                          ownershipRelated.foldlM_fault_refines parentRelated
                            (fun childFault =>
                              childFault ≠
                                .malformed
                                  "reference-count release fuel exhausted")
                            notFuel recurseSuccess recurseFault
                              semanticOwnedFoldList
                        have addressHeap :=
                          (MemoryState.PrefixExtension.readLiveHeader_facts
                            state address header headerRead).1
                        have concreteOrdinary :
                            header.persistent = false :=
                          persistent.trans ordinary
                        have notPromoted : header.isPromotedTag = false := by
                          have different :
                              (ObjectKind.closure == ObjectKind.natural) =
                                false := by decide
                          simp [Header.isPromotedTag, headerKind,
                            concreteOrdinary, different]
                        have concreteOperation :
                            decrementReferenceOnceFuel (fuel + 1) state address
                                check witness.closureDescriptors =
                              .error failure := by
                          simp only [decrementReferenceOnceFuel]
                          rw [addressHeap, headerRead]
                          simp only [Bind.bind, Except.bind, liftMemory]
                          rw [if_neg (by simp [notPromoted])]
                          rw [if_neg (by simp [concreteOrdinary])]
                          have headerNonzero : header.refCount ≠ 0 := by
                            intro zero
                            rw [zero] at refCount
                            simp at refCount
                            omega
                          rw [if_neg (by simpa using headerNonzero)]
                          rw [refCount, if_neg oneLt]
                          rw [ownedRead, releasedOperation]
                          exact concreteFold
                        exact ⟨failure, concreteOperation, faultRelated⟩

/-- A non-fuel concrete error is monotone in the recursive release budget.
Successful earlier children use the established success monotonicity theorem;
the first failing child uses this induction. Target-classified fuel exhaustion
is excluded because additional fuel is specifically allowed to change it. -/
theorem decrementReferenceOnceFuel_error_mono
    {fuel more : Nat} {state : MemoryState} {object : Word32}
    {check : Bool} {descriptors : ClosureDescriptorTable}
    {failure : ConcreteError}
    (fuelLe : fuel ≤ more)
    (notFuel : failure ≠ .target .releaseFuelExhausted)
    (operation :
      decrementReferenceOnceFuel fuel state object check descriptors =
        .error failure) :
    decrementReferenceOnceFuel more state object check descriptors =
      .error failure := by
  induction fuel generalizing more state object check descriptors failure with
  | zero =>
      cases more with
      | zero => exact operation
      | succ more =>
          cases classEq : object.classify with
          | sentinel | immediate | invalid =>
              simpa [decrementReferenceOnceFuel, classEq] using operation
          | heap =>
              cases headerEq : state.readLiveHeader object with
              | error memoryFailure =>
                  simpa [decrementReferenceOnceFuel, classEq, headerEq,
                    liftMemory, Bind.bind, Except.bind] using operation
              | ok header =>
                  by_cases promoted : header.isPromotedTag = true
                  · simpa [decrementReferenceOnceFuel, classEq, headerEq,
                      liftMemory, Bind.bind, Except.bind, promoted] using
                        operation
                  · have failureEq :
                        failure = .target .releaseFuelExhausted := by
                      simp [decrementReferenceOnceFuel, classEq, headerEq,
                        liftMemory, Bind.bind, Except.bind, promoted] at operation
                      change
                        (Except.error
                          (.target .releaseFuelExhausted) :
                            Except ConcreteError MemoryState) =
                          .error failure at operation
                      exact (Except.error.inj operation).symm
                    exact False.elim (notFuel failureEq)
  | succ fuel ih =>
      cases more with
      | zero => omega
      | succ more =>
          have smaller : fuel ≤ more := by omega
          cases classEq : object.classify with
          | sentinel | immediate | invalid =>
              simpa [decrementReferenceOnceFuel, classEq] using operation
          | heap =>
              cases headerEq : state.readLiveHeader object with
              | error memoryFailure =>
                  simpa [decrementReferenceOnceFuel, classEq, headerEq,
                    liftMemory, Bind.bind, Except.bind] using operation
              | ok header =>
                  by_cases promoted : header.isPromotedTag = true
                  · simpa [decrementReferenceOnceFuel, classEq, headerEq,
                      liftMemory, Bind.bind, Except.bind, promoted] using
                        operation
                  · by_cases persistent : header.persistent = true
                    · simp [decrementReferenceOnceFuel, classEq, headerEq,
                        liftMemory, Bind.bind, Except.bind, promoted,
                        persistent] at operation
                      contradiction
                    · by_cases zero : (header.refCount == 0) = true
                      · simpa [decrementReferenceOnceFuel, classEq, headerEq,
                          liftMemory, Bind.bind, Except.bind, promoted,
                          persistent, zero] using operation
                      · by_cases above : 1 < header.refCount.toNat
                        · simpa [decrementReferenceOnceFuel, classEq, headerEq,
                            liftMemory, Bind.bind, Except.bind, promoted,
                            persistent, zero, above] using operation
                        · cases ownedEq :
                            readOwnedReferences state object header descriptors with
                          | error ownedFailure =>
                              simpa [decrementReferenceOnceFuel, classEq,
                                headerEq, liftMemory, Bind.bind, Except.bind,
                                promoted, persistent, zero, above, ownedEq]
                                  using operation
                          | ok owned =>
                              cases releasedEq :
                                  writeLiveHeader state object header.forRelease with
                              | error releasedFailure =>
                                  simpa [decrementReferenceOnceFuel, classEq,
                                    headerEq, liftMemory, Bind.bind,
                                    Except.bind, promoted, persistent, zero,
                                    above, ownedEq, releasedEq] using operation
                              | ok released =>
                                  have foldMono : ∀ (children : List Word32)
                                      (before : MemoryState),
                                      children.foldlM (init := before)
                                          (fun next child =>
                                            decrementReferenceOnceFuel fuel next
                                              child true descriptors) =
                                        .error failure →
                                      children.foldlM (init := before)
                                          (fun next child =>
                                            decrementReferenceOnceFuel more next
                                              child true descriptors) =
                                        .error failure := by
                                    intro children
                                    induction children with
                                    | nil =>
                                        intro before folded
                                        simp only [List.foldlM_nil] at folded
                                        contradiction
                                    | cons child children tailIH =>
                                        intro before folded
                                        simp only [List.foldlM_cons, Bind.bind,
                                          Except.bind] at folded ⊢
                                        cases childEq :
                                            decrementReferenceOnceFuel fuel
                                              before child true descriptors with
                                        | error childFailure =>
                                            rw [childEq] at folded
                                            have failureEq :
                                                childFailure = failure :=
                                              Except.error.inj folded
                                            subst childFailure
                                            rw [ih smaller notFuel childEq]
                                        | ok middle =>
                                            rw [childEq] at folded
                                            rw [
                                              decrementReferenceOnceFuel_ok_mono
                                                smaller childEq]
                                            exact tailIH middle folded
                                  have folded :
                                      owned.foldlM (init := released)
                                          (fun next child =>
                                            decrementReferenceOnceFuel fuel next
                                              child true descriptors) =
                                        .error failure := by
                                    simpa [decrementReferenceOnceFuel, classEq,
                                      headerEq, liftMemory, Bind.bind,
                                      Except.bind, promoted, persistent, zero,
                                      above, ownedEq, releasedEq] using operation
                                  have foldedMore :=
                                    foldMono owned released folded
                                  simpa [decrementReferenceOnceFuel, classEq,
                                    headerEq, liftMemory, Bind.bind, Except.bind,
                                    promoted, persistent, zero, above, ownedEq,
                                    releasedEq] using foldedMore

/-- Public recursive decrement fault refinement. The semantic heap-length
budget is sufficient for the source operation; the related concrete cursor
provides at least that much fuel, and non-fuel source errors are stable when
the concrete budget is enlarged. -/
theorem LiveHeapRel.decrementReferenceOnce_fault_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {fault : RuntimeFault}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticOperation :
      Fir.LeanIR.Impure.decLocation runtime location = .error fault) :
    ∃ failure,
      decrementReferenceOnce state address check witness.closureDescriptors =
          .error failure ∧
        ConcreteErrorSourceRel witness failure fault := by
  unfold Fir.LeanIR.Impure.decLocation at semanticOperation
  obtain ⟨failure, concreteSemanticFuel, faultRelated⟩ :=
    related.decrementReferenceOnceFuel_fault_refines mapped check notFuel
      semanticOperation
  have failureNotFuel : failure ≠ .target .releaseFuelExhausted := by
    cases faultRelated <;> simp
  have concretePublic :=
    decrementReferenceOnceFuel_error_mono
      related.semanticFuel_le_concreteFuel failureNotFuel concreteSemanticFuel
  exact ⟨failure, by
    unfold decrementReferenceOnce
    exact concretePublic, faultRelated⟩

/-- Repeated public decrement preserves the first source-classified fault.
Every successful earlier repetition advances the related heaps; the failing
repetition uses the public one-step fault theorem and prevents the suffix from
executing. -/
theorem LiveHeapRel.decrementReference_fault_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {amount : Nat} {fault : RuntimeFault}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticOperation :
      Fir.LeanIR.Impure.decValue runtime (.object (.heap location)) amount check =
        .error fault) :
    ∃ failure,
      decrementReference state address amount check
          witness.closureDescriptors =
        .error failure ∧
      ConcreteErrorSourceRel witness failure fault := by
  induction amount generalizing state runtime fault with
  | zero =>
      simp [Fir.LeanIR.Impure.decValue, pure, Except.pure] at semanticOperation
  | succ amount ih =>
      simp only [Fir.LeanIR.Impure.decValue, List.replicate_succ,
        List.foldlM_cons, Bind.bind, Except.bind,
        Fir.LeanIR.Impure.decValueOnce] at semanticOperation
      cases firstSemantic :
          Fir.LeanIR.Impure.decLocation runtime location with
      | error firstFault =>
          rw [firstSemantic] at semanticOperation
          have faultEq : firstFault = fault :=
            Except.error.inj semanticOperation
          subst firstFault
          obtain ⟨failure, firstConcrete, faultRelated⟩ :=
            related.decrementReferenceOnce_fault_refines mapped check notFuel
              firstSemantic
          refine ⟨failure, ?_, faultRelated⟩
          simp only [decrementReference, List.replicate_succ,
            List.foldlM_cons, Bind.bind, Except.bind]
          rw [firstConcrete]
      | ok middleRuntime =>
          rw [firstSemantic] at semanticOperation
          obtain ⟨middleState, firstConcrete, middleRelated⟩ :=
            related.decrementReferenceOnce_refines mapped check firstSemantic
          obtain ⟨failure, restConcrete, faultRelated⟩ :=
            ih middleRelated notFuel semanticOperation
          refine ⟨failure, ?_, faultRelated⟩
          simp only [decrementReference, List.replicate_succ,
            List.foldlM_cons, Bind.bind, Except.bind]
          rw [firstConcrete]
          exact restConcrete

theorem ConcreteExternalImpl.invoke_error
    {implementation : ConcreteExternalImpl}
    {request : ConcreteExternalRequest} {before : ConcreteRuntimeState}
    {failure : ConcreteError}
    (called : implementation.call request before = .error failure) :
    implementation.invoke request before = .error failure ∧
      ∀ after value,
        implementation.invoke request before ≠ .ok (after, value) := by
  constructor
  · unfold ConcreteExternalImpl.invoke
    rw [called]
    rfl
  · intro after value successful
    unfold ConcreteExternalImpl.invoke at successful
    rw [called] at successful
    contradiction

/-- An exact external source failure agrees with the source implementation
and produces no concrete post-state. -/
theorem ConcreteExternalImpl.invoke_source_refines
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {concreteBefore : ConcreteRuntimeState}
    {semanticBefore : RuntimeState}
    {fault : RuntimeFault}
    (concreteCalled : concreteImplementation.call concreteRequest concreteBefore =
      .error (.source fault))
    (semanticCalled : semanticImplementation.call semanticRequest semanticBefore =
      .error fault) :
    concreteImplementation.invoke concreteRequest concreteBefore =
        .error (.source fault) ∧
      semanticImplementation.call semanticRequest semanticBefore = .error fault ∧
      (.source fault : ConcreteError).toTrap =
        .source (.runtime fault) := by
  exact ⟨(concreteImplementation.invoke_error concreteCalled).1,
    semanticCalled, rfl⟩

theorem ConcreteError.targetMemory_classified (failure : MemoryError) :
    (ConcreteError.target failure).toTrap =
      .target (.memory failure) := rfl

theorem ConcreteError.targetGlobal_classified (failure : ConcreteGlobalError) :
    (ConcreteError.targetGlobal failure).toTrap =
      .target (.global failure) := rfl

end Fir.Wasm.Concrete
