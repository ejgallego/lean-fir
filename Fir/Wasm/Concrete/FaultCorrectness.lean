import Fir.Wasm.Concrete.ExternalCorrectness
import Fir.Wasm.Concrete.OwnershipFrameCorrectness
import Fir.Wasm.Concrete.ResetReuseCorrectness
import Fir.LeanIR.Passes.ElimDeadRuntimeRel

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-! ## Recursive-release target safety -/

/-- A semantic recursive release with more fuel than live heap cells cannot
reach its internal exhaustion marker. Each recursive parent is marked dead
before its children run, so the live-cell measure strictly decreases at every
genuine descent and never increases across a successful sibling prefix. -/
private theorem decLocationFuel_ne_releaseFuel_of_liveCellCount_lt
    {fuel : Nat} {runtime : RuntimeState} {location : Location}
    (enough :
      Fir.LeanIR.Passes.ElimDead.liveCellCount runtime.heap < fuel) :
    Fir.LeanIR.Impure.decLocationFuel fuel runtime location ≠
      .error (.malformed "reference-count release fuel exhausted") := by
  generalize countEq :
      Fir.LeanIR.Passes.ElimDead.liveCellCount runtime.heap = count at enough
  induction count using Nat.strongRecOn generalizing fuel runtime location with
  | ind count smaller =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          intro operation
          cases found : findCell? runtime.heap location with
          | none =>
              have deadGet :
                  getLiveCell runtime location =
                    .error (.deadObject location) := by
                simp [getLiveCell, found]
              simp only [Fir.LeanIR.Impure.decLocationFuel, deadGet,
                Bind.bind, Except.bind] at operation
              cases Except.error.inj operation
          | some cell =>
              cases liveEq : cell.live with
              | false =>
                  have deadGet :
                      getLiveCell runtime location =
                        .error (.deadObject location) := by
                    simp [getLiveCell, found, liveEq]
                  simp only [Fir.LeanIR.Impure.decLocationFuel, deadGet,
                    Bind.bind, Except.bind] at operation
                  cases Except.error.inj operation
              | true =>
                  have liveGet :
                      getLiveCell runtime location = .ok cell := by
                    simp [getLiveCell, found, liveEq]
                  by_cases persistent : cell.persistent = true
                  · simp only [Fir.LeanIR.Impure.decLocationFuel, liveGet,
                      Bind.bind, Except.bind] at operation
                    rw [if_pos persistent] at operation
                    cases operation
                  · by_cases zero : cell.rc = 0
                    · simp only [Fir.LeanIR.Impure.decLocationFuel, liveGet,
                        Bind.bind, Except.bind] at operation
                      rw [if_neg persistent, if_pos zero] at operation
                      cases Except.error.inj operation
                    · by_cases above : 1 < cell.rc
                      · obtain ⟨nextHeap, nextPost⟩ :=
                          replaceCell_spec_of_find runtime.heap location cell
                            { cell with rc := cell.rc - 1 } found
                        let next : RuntimeState :=
                          { runtime with heap := nextHeap }
                        have nextEq :
                            setCell runtime location
                                { cell with rc := cell.rc - 1 } =
                              .ok next := by
                          unfold setCell
                          rw [nextPost.replaced]
                        simp only [Fir.LeanIR.Impure.decLocationFuel, liveGet,
                          Bind.bind, Except.bind] at operation
                        rw [if_neg persistent, if_neg zero, if_pos above,
                          nextEq] at operation
                        cases operation
                      · obtain ⟨parentHeap, parentPost⟩ :=
                          replaceCell_spec_of_find runtime.heap location cell
                            { cell with rc := 0, live := false } found
                        let parent : RuntimeState :=
                          { runtime with heap := parentHeap }
                        have parentEq :
                            setCell runtime location
                                { cell with rc := 0, live := false } =
                              .ok parent := by
                          unfold setCell
                          rw [parentPost.replaced]
                        have parentCount :=
                          Fir.LeanIR.Passes.ElimDead.setCell_liveCellCount
                            found parentEq
                        simp [liveEq] at parentCount
                        have parentLtCount :
                            Fir.LeanIR.Passes.ElimDead.liveCellCount
                                parent.heap < count := by
                          rw [← countEq]
                          omega
                        have parentLtFuel :
                            Fir.LeanIR.Passes.ElimDead.liveCellCount
                                parent.heap < fuel := by
                          omega
                        let releaseChild
                            (before : RuntimeState) (value : Value) :
                            Except RuntimeFault RuntimeState :=
                          match value with
                          | .object (.heap child) =>
                              Fir.LeanIR.Impure.decLocationFuel fuel before child
                          | _ => .ok before
                        have foldSafe : ∀ (values : List Value)
                            (before : RuntimeState),
                            Fir.LeanIR.Passes.ElimDead.liveCellCount
                                before.heap < count →
                            Fir.LeanIR.Passes.ElimDead.liveCellCount
                                before.heap < fuel →
                            values.foldlM (init := before) releaseChild ≠
                              .error (.malformed
                                "reference-count release fuel exhausted") := by
                          intro values
                          induction values with
                          | nil =>
                              intro before _ _ folded
                              simp only [List.foldlM_nil] at folded
                              contradiction
                          | cons value values tailIH =>
                              intro before beforeLtCount beforeLtFuel folded
                              simp only [List.foldlM_cons, Bind.bind,
                                Except.bind] at folded
                              cases value with
                              | object reference =>
                                  cases reference with
                                  | tagged payload =>
                                      exact tailIH before beforeLtCount
                                        beforeLtFuel folded
                                  | heap child =>
                                      dsimp only [releaseChild] at folded
                                      cases childEq :
                                          Fir.LeanIR.Impure.decLocationFuel fuel
                                            before child with
                                      | error childFault =>
                                          rw [childEq] at folded
                                          have childFaultEq :
                                              childFault =
                                                .malformed
                                                  "reference-count release fuel exhausted" :=
                                            Except.error.inj folded
                                          subst childFault
                                          exact smaller
                                            (Fir.LeanIR.Passes.ElimDead.liveCellCount
                                              before.heap)
                                            beforeLtCount
                                            (runtime := before)
                                            (location := child)
                                            (fuel := fuel)
                                            rfl beforeLtFuel childEq
                                      | ok middle =>
                                          rw [childEq] at folded
                                          have middleLe :=
                                            Fir.LeanIR.Passes.ElimDead.decLocationFuel_liveCellCount_le
                                              childEq
                                          exact tailIH middle
                                            (Nat.lt_of_le_of_lt middleLe
                                              beforeLtCount)
                                            (Nat.lt_of_le_of_lt middleLe
                                              beforeLtFuel)
                                            folded
                              | usize | scalar | erased | reuseToken =>
                                  exact tailIH before beforeLtCount beforeLtFuel
                                    folded
                        have semanticFold :
                            cell.object.ownedValues.toList.foldlM
                                (init := parent) releaseChild =
                              .error (.malformed
                                "reference-count release fuel exhausted") := by
                          simp only [Fir.LeanIR.Impure.decLocationFuel, liveGet,
                            Bind.bind, Except.bind] at operation
                          rw [if_neg persistent, if_neg zero, if_neg above]
                            at operation
                          rw [parentEq] at operation
                          change
                            Array.foldlM releaseChild parent
                                cell.object.ownedValues =
                              .error (.malformed
                                "reference-count release fuel exhausted")
                            at operation
                          simpa only [Array.foldlM_toList] using operation
                        exact foldSafe cell.object.ownedValues.toList parent
                          parentLtCount parentLtFuel semanticFold

/-- FIR's public heap-length budget strictly dominates the live-cell
termination measure, so release-fuel exhaustion is not an observable semantic
runtime fault. -/
theorem decLocation_ne_releaseFuelExhausted
    (runtime : RuntimeState) (location : Location) :
    Fir.LeanIR.Impure.decLocation runtime location ≠
      .error (.malformed "reference-count release fuel exhausted") := by
  unfold Fir.LeanIR.Impure.decLocation
  apply decLocationFuel_ne_releaseFuel_of_liveCellCount_lt
  exact Nat.lt_of_le_of_lt
    (Fir.LeanIR.Passes.ElimDead.liveCellCount_le_length runtime.heap)
    (Nat.lt_succ_self runtime.heap.length)

/-- Repeating public semantic decrements cannot turn the private fuel marker
into a runtime-visible fault: each individual public decrement excludes it,
and every successful prefix restarts with the public heap-length budget of the
updated runtime. -/
theorem decValue_heap_ne_releaseFuelExhausted
    (runtime : RuntimeState) (location : Location) (amount : Nat)
    (check : Bool) :
    Fir.LeanIR.Impure.decValue runtime (.object (.heap location)) amount check ≠
      .error (.malformed "reference-count release fuel exhausted") := by
  induction amount generalizing runtime with
  | zero =>
      simp [Fir.LeanIR.Impure.decValue, pure, Except.pure]
  | succ amount ih =>
      intro operation
      simp only [Fir.LeanIR.Impure.decValue, List.replicate_succ,
        List.foldlM_cons, Bind.bind, Except.bind,
        Fir.LeanIR.Impure.decValueOnce] at operation
      cases first : Fir.LeanIR.Impure.decLocation runtime location with
      | error fault =>
          rw [first] at operation
          have faultEq :
              fault =
                .malformed "reference-count release fuel exhausted" :=
            Except.error.inj operation
          subst fault
          exact decLocation_ne_releaseFuelExhausted runtime location first
      | ok nextRuntime =>
          rw [first] at operation
          exact ih nextRuntime operation

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

/-- Reset's temporary constructor-descriptor shadow does not change the
location identity carried by a source-classified fault. -/
theorem ConcreteErrorSourceRel.of_rebindConstructor
    {witness : RefinementWitness} {failure : ConcreteError}
    {fault : RuntimeFault} {address : Word32}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    (related :
      ConcreteErrorSourceRel
        (witness.rebindConstructor address info fieldKinds) failure fault) :
    ConcreteErrorSourceRel witness failure fault := by
  cases related with
  | source fault => exact .source fault
  | sourceAddress addressRelated =>
      cases addressRelated with
      | deadObject heapRelated =>
          cases heapRelated with
          | mapped found =>
              exact .sourceAddress (.deadObject (.mapped (by simpa using found)))
      | referenceCountUnderflow heapRelated =>
          cases heapRelated with
          | mapped found =>
              exact .sourceAddress
                (.referenceCountUnderflow (.mapped (by simpa using found)))

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
                | @array elements capacity header _ descriptor objectEq
                      objectRelated refCount persistent cellLive =>
                    obtain ⟨words, ownedRead, ownershipRelated⟩ :=
                      objectRelated.readOwnedReferences
                    obtain ⟨released, memory, releasedOperation, releasedEq,
                        headerWrite, finalValid, deadRelated⟩ :=
                      releaseHeader related.frontier objectRelated.headerRead
                        objectRelated.headerOwned
                    obtain ⟨_, rawRead, _, _, _, _⟩ :=
                      MemoryState.PrefixExtension.readLiveHeader_facts state
                        address header objectRelated.headerRead
                    have headerInBounds :
                        address.value + headerBytes ≤ state.memory.size :=
                      Nat.le_trans objectRelated.headerOwned
                        related.frontier.cursorInBounds
                    let replacement : HeapCell :=
                      { cell with rc := 0, live := false }
                    have targetAfter :
                        CellRel released witness address replacement :=
                      .dead (by simp [replacement]) (by simp [replacement])
                        ⟨.array capacity, descriptor⟩ deadRelated
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
                        Array.foldlM releaseChild parentRuntime elements =
                          .error fault := by
                      simp only [Fir.LeanIR.Impure.decLocationFuel, getLiveCell,
                        found, liveEq, ↓reduceIte, Bind.bind, Except.bind]
                        at semanticOperation
                      rw [if_neg (by simp [ordinary])] at semanticOperation
                      rw [if_neg zeroCase, if_neg oneLt] at semanticOperation
                      rw [parentSemantic] at semanticOperation
                      rw [objectEq] at semanticOperation
                      change Array.foldlM releaseChild parentRuntime elements =
                        .error fault at semanticOperation
                      exact semanticOperation
                    have semanticFoldList :
                        elements.toList.foldlM
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
                        address header objectRelated.headerRead).1
                    have headerOrdinary : header.persistent = false :=
                      persistent.trans ordinary
                    have notPromoted : header.isPromotedTag = false := by
                      have different :
                          (ObjectKind.opaque == ObjectKind.natural) = false :=
                        by decide
                      simp [Header.isPromotedTag, objectRelated.headerKind,
                        headerOrdinary, different]
                    have concreteOperation :
                        decrementReferenceOnceFuel (fuel + 1) state address
                            check witness.closureDescriptors =
                          .error failure := by
                      simp only [decrementReferenceOnceFuel]
                      rw [addressHeap, objectRelated.headerRead]
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
                        simpa [readOwnedReferences,
                          objectRelated.headerKind] using ownedRead
                      rw [ownedReadWithDescriptors, releasedOperation]
                      exact concreteFold
                    exact ⟨failure, concreteOperation, faultRelated⟩
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

/-- A public decrement of a represented heap object cannot expose the
concrete runtime's target-only release-fuel trap. The semantic operation is
total with respect to its internal fuel marker; its success and remaining
fault branches both refine to non-target concrete results. -/
theorem LiveHeapRel.decrementReferenceOnce_ne_releaseFuelExhausted
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool) :
    decrementReferenceOnce state address check witness.closureDescriptors ≠
      .error (.target .releaseFuelExhausted) := by
  intro targetOperation
  cases semanticOperation :
      Fir.LeanIR.Impure.decLocation runtime location with
  | ok nextRuntime =>
      obtain ⟨result, concreteOperation, _⟩ :=
        related.decrementReferenceOnce_refines mapped check semanticOperation
      rw [targetOperation] at concreteOperation
      contradiction
  | error fault =>
      have notFuel :
          fault ≠
            .malformed "reference-count release fuel exhausted" := by
        intro faultEq
        subst fault
        exact decLocation_ne_releaseFuelExhausted runtime location
          semanticOperation
      obtain ⟨failure, concreteOperation, faultRelated⟩ :=
        related.decrementReferenceOnce_fault_refines mapped check notFuel
          semanticOperation
      rw [targetOperation] at concreteOperation
      have failureEq : (.target .releaseFuelExhausted : ConcreteError) =
          failure :=
        Except.error.inj concreteOperation
      subst failure
      cases faultRelated

/-- An ABI-admissible ownership slot carries either an object reference or
the erased marker. Scalar and reuse-token lanes cannot inhabit constructor
ownership fields. -/
theorem OwnershipValueRel.object_or_erased
    {witness : RefinementWitness} {word : Word32} {value : Value}
    (related : OwnershipValueRel witness word value) :
    (∃ reference, value = .object reference) ∨ value = .erased := by
  cases related with
  | intro kind admissible valueRelated =>
      cases valueRelated with
      | object heapRelated => exact .inl ⟨_, rfl⟩
      | tagged taggedRelated => exact .inl ⟨_, rfl⟩
      | tobject objectRelated => exact .inl ⟨_, rfl⟩
      | erased => exact .inr rfl
      | reuseNone | reuseSome | uint8 | uint16 | uint32 =>
          simp [AbiKind.isObjectField] at admissible

/-- Ordered reset slots preserve the first fault through public checked
decrement. Successful children advance both heaps; erased children are exact
no-ops; the first failing child determines the exact source-classified error
and prevents the suffix from running. -/
theorem OwnershipValuesRel.foldlM_public_fault_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {words : List Word32} {values : List Value}
    {fault : RuntimeFault}
    (related : OwnershipValuesRel witness words values)
    (heap : LiveHeapRel state witness runtime)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticOperation :
      values.foldlM (init := runtime) (fun next value =>
        Fir.LeanIR.Impure.releaseResetField next value) = .error fault) :
    ∃ failure,
      words.foldlM (init := state) (fun next child =>
        decrementReferenceOnce next child true witness.closureDescriptors) =
          .error failure ∧
      ConcreteErrorSourceRel witness failure fault := by
  induction related generalizing state runtime fault with
  | nil =>
      simp only [List.foldlM_nil] at semanticOperation
      contradiction
  | @cons word value words values head tail ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at semanticOperation ⊢
      rcases head.releaseStep heap (state.heapCursor / headerBytes + 1)
          witness.closureDescriptors with heapStep | noOpStep
      · obtain ⟨location, valueEq, mapped⟩ := heapStep
        subst value
        simp only [Fir.LeanIR.Impure.releaseResetField,
          Fir.LeanIR.Impure.decValueOnce] at semanticOperation
        cases childEq : Fir.LeanIR.Impure.decLocation runtime location with
        | error childFault =>
            rw [childEq] at semanticOperation
            have faultEq : childFault = fault :=
              Except.error.inj semanticOperation
            subst childFault
            obtain ⟨failure, concreteHead, faultRelated⟩ :=
              heap.decrementReferenceOnce_fault_refines mapped true notFuel
                childEq
            exact ⟨failure, by rw [concreteHead], faultRelated⟩
        | ok nextRuntime =>
            rw [childEq] at semanticOperation
            obtain ⟨nextState, concreteHead, nextHeap⟩ :=
              heap.decrementReferenceOnce_refines mapped true childEq
            obtain ⟨failure, concreteTail, faultRelated⟩ :=
              ih nextHeap notFuel semanticOperation
            refine ⟨failure, ?_, faultRelated⟩
            rw [concreteHead]
            exact concreteTail
      · obtain ⟨notHeap, concreteFuelNoOp⟩ := noOpStep
        rcases head.object_or_erased with ⟨reference, valueEq⟩ | valueEq
        · subst value
          cases reference with
          | heap location => exact False.elim (notHeap location rfl)
          | tagged payload =>
              have semanticHead :
                  Fir.LeanIR.Impure.releaseResetField runtime
                      (.object (.tagged payload)) =
                    .ok runtime := by
                rfl
              rw [semanticHead] at semanticOperation
              obtain ⟨failure, concreteTail, faultRelated⟩ :=
                ih heap notFuel semanticOperation
              have concreteHead :
                  decrementReferenceOnce state word true
                      witness.closureDescriptors =
                    .ok state := by
                unfold decrementReferenceOnce
                exact concreteFuelNoOp
              refine ⟨failure, ?_, faultRelated⟩
              rw [concreteHead]
              exact concreteTail
        · subst value
          obtain ⟨failure, concreteTail, faultRelated⟩ :=
            ih heap notFuel (by
              simpa [Fir.LeanIR.Impure.releaseResetField] using
                semanticOperation)
          have concreteHead :
              decrementReferenceOnce state word true
                  witness.closureDescriptors =
                .ok state := by
            unfold decrementReferenceOnce
            exact concreteFuelNoOp
          refine ⟨failure, ?_, faultRelated⟩
          rw [concreteHead]
          exact concreteTail

/-- A represented ownership list cannot expose release-fuel exhaustion while
running its public checked decrement fold. Mapped children either take a
refined semantic success step, advancing both heaps, or stop with a
source-classified fault; every represented non-heap slot is an exact no-op. -/
theorem OwnershipValuesRel.foldlM_public_ne_releaseFuelExhausted
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {words : List Word32} {values : List Value}
    (related : OwnershipValuesRel witness words values)
    (heap : LiveHeapRel state witness runtime) :
    words.foldlM (init := state) (fun next child =>
        decrementReferenceOnce next child true witness.closureDescriptors) ≠
      .error (.target .releaseFuelExhausted) := by
  induction related generalizing state runtime with
  | nil =>
      simp [pure, Except.pure]
  | @cons word value words values head tail ih =>
      intro operation
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at operation
      rcases head.releaseStep heap (state.heapCursor / headerBytes + 1)
          witness.closureDescriptors with heapStep | noOpStep
      · obtain ⟨location, valueEq, mapped⟩ := heapStep
        subst value
        cases semanticOperation :
            Fir.LeanIR.Impure.decLocation runtime location with
        | ok nextRuntime =>
            obtain ⟨nextState, concreteOperation, nextHeap⟩ :=
              heap.decrementReferenceOnce_refines mapped true
                semanticOperation
            rw [concreteOperation] at operation
            exact ih nextHeap operation
        | error fault =>
            have notFuel :
                fault ≠
                  .malformed "reference-count release fuel exhausted" := by
              intro faultEq
              subst fault
              exact decLocation_ne_releaseFuelExhausted runtime location
                semanticOperation
            obtain ⟨failure, concreteOperation, faultRelated⟩ :=
              heap.decrementReferenceOnce_fault_refines mapped true notFuel
                semanticOperation
            rw [concreteOperation] at operation
            have failureEq :
                failure = (.target .releaseFuelExhausted : ConcreteError) :=
              Except.error.inj operation
            subst failure
            cases faultRelated
      · obtain ⟨_, concreteFuelNoOp⟩ := noOpStep
        have concreteOperation :
            decrementReferenceOnce state word true
                witness.closureDescriptors =
              .ok state := by
          unfold decrementReferenceOnce
          exact concreteFuelNoOp
        rw [concreteOperation] at operation
        exact ih heap operation

/-- A unique ordinary constructor reset preserves the first recursively
reached child-release fault. The protocol descriptor is needed only while
relating the cleared parent and child traversal; the reported fault is
projected back to the original location witness because reset commits no heap
state on error. -/
theorem LiveHeapRel.resetObject_unique_fault_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {object : ConstructorObject} {count : Nat}
    {fault : RuntimeFault}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1) (constructor : cell.object = .ctor object)
    (countFits : count ≤ object.objectFields.size)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticOperation :
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .error fault) :
    ∃ failure,
      resetObject state count address witness.closureDescriptors =
          .error failure ∧
      ConcreteErrorSourceRel witness failure fault := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  cases targetRelated with
  | @constructor info fieldKinds semantic header _ descriptor objectEq
      objectRelated headerRead headerKind refCount persistent cellLive =>
      rw [constructor] at objectEq
      injection objectEq with semanticEq
      subst semantic
      let replacement : HeapCell :=
        { cell with object := .ctor (resetProtocolObject object count) }
      obtain ⟨middleRuntime, semanticSet, _, _, _, _⟩ :=
        setCell_spec_of_find runtime location cell replacement found
      have semanticFold :
          (object.objectFields.extract 0 count).foldlM
              (fun next value =>
                Fir.LeanIR.Impure.releaseResetField next value)
              middleRuntime = .error fault := by
        unfold Fir.LeanIR.Impure.reset at semanticOperation
        simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
          at semanticOperation
        rw [if_neg (by simp [ordinary, unique])] at semanticOperation
        rw [constructor] at semanticOperation
        simp only at semanticOperation
        rw [if_neg (Nat.not_lt.mpr countFits)] at semanticOperation
        have semanticOperation' : (do
            let next ← setCell runtime location replacement
            let next ← (object.objectFields.extract 0 count).foldlM
              (fun next value =>
                Fir.LeanIR.Impure.releaseResetField next value)
              next
            return (next, Value.reuseToken (some location))) =
              .error fault := by
          simpa only [replacement, resetProtocolObject, live, Bind.bind,
            Except.bind] using semanticOperation
        rw [semanticSet] at semanticOperation'
        simp only [Bind.bind, Except.bind] at semanticOperation'
        cases foldEq :
            (object.objectFields.extract 0 count).foldlM
              (fun next value =>
                Fir.LeanIR.Impure.releaseResetField next value)
              middleRuntime with
        | error childFault =>
            rw [foldEq] at semanticOperation'
            have childFaultEq : childFault = fault :=
              Except.error.inj semanticOperation'
            subst childFault
            rfl
        | ok finalRuntime =>
            rw [foldEq] at semanticOperation'
            contradiction
      obtain ⟨words, ownedRead, ownershipRelated⟩ :=
        objectRelated.readOwnedPrefix count countFits
      have fieldsBeforeFrontier :
          objectFieldAddress address.value count ≤ state.heapCursor := by
        have aligned := align8_ge
          (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
            info.ssize)
        have activeExtent := objectRelated.extent
        have countFitsInfo : count ≤ info.size := by
          rw [← objectRelated.semanticObjectFields]
          exact countFits
        simp [objectFieldAddress, ConstructorLayout.ofInfo, target] at aligned activeExtent ⊢
        omega
      have fieldsInBounds :
          objectFieldAddress address.value (0 + count) ≤ state.memory.size := by
        simp only [Nat.zero_add]
        exact Nat.le_trans fieldsBeforeFrontier
          related.frontier.cursorInBounds
      obtain ⟨fieldMemory, fieldWrite, _⟩ :=
        writeObjectFields_spec state.memory address.value 0
          (List.replicate count taggedZero) (by simpa using fieldsInBounds)
      obtain ⟨protocolRuntime, protocolSet, protocolHeap, _⟩ :=
        LiveHeapRel.writeObjectFields_resetPrefix state fieldMemory witness
          runtime location address cell header info fieldKinds object count
          related mapped found descriptor constructor objectRelated headerRead
          headerKind refCount persistent cellLive countFits fieldWrite
      have protocolRuntimeEq : protocolRuntime = middleRuntime := by
        exact Except.ok.inj (protocolSet.symm.trans semanticSet)
      subst protocolRuntime
      have semanticFoldList :
          (object.objectFields.extract 0 count).toList.foldlM
              (init := middleRuntime)
              (fun next value =>
                Fir.LeanIR.Impure.releaseResetField next value) =
            .error fault := by
        simpa only [Array.foldlM_toList] using semanticFold
      have protocolOwnership :=
        ownershipRelated.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)
      obtain ⟨failure, concreteFold, faultRelated⟩ :=
        protocolOwnership.foldlM_public_fault_refines protocolHeap notFuel
          semanticFoldList
      obtain ⟨addressHeap, _, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address header
          headerRead
      obtain ⟨objectHeader, objectHeaderRead, _, _, _, objectCount, _, _⟩ :=
        objectRelated.header
      rw [headerRead] at objectHeaderRead
      have objectHeaderEq := Except.ok.inj objectHeaderRead
      subst objectHeader
      have headerOrdinary : header.persistent = false :=
        persistent.trans ordinary
      have headerOne : header.refCount = 1 := by
        apply UInt32.toNat.inj
        simpa [unique] using refCount
      have notPromoted : header.isPromotedTag = false := by
        have different :
            (ObjectKind.constructor == ObjectKind.natural) = false := by decide
        simp [Header.isPromotedTag, headerKind, different]
      have countFitsInfo : count ≤ info.size := by
        rw [← objectRelated.semanticObjectFields]
        exact countFits
      have headerKindCheck :
          (header.kind == ObjectKind.constructor) = true := by
        rw [headerKind]
        decide
      have concreteFoldOriginal :
          words.foldlM
              (init := ({ state with memory := fieldMemory } : MemoryState))
              (fun next child => decrementReferenceOnce next child true
                witness.closureDescriptors) =
            .error failure := by
        simpa [RefinementWitness.rebindConstructor] using concreteFold
      have concreteReset :
          resetObject state count address witness.closureDescriptors =
            .error failure := by
        unfold resetObject
        rw [addressHeap, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        rw [if_neg (by simp [notPromoted, headerOrdinary, headerOne])]
        rw [if_pos headerKindCheck]
        rw [objectCount, if_neg (Nat.not_lt.mpr countFitsInfo)]
        rw [ownedRead, fieldWrite]
        simp only
        rw [concreteFoldOriginal]
      exact ⟨failure, concreteReset,
        faultRelated.of_rebindConstructor⟩
  | boxed descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | natural descriptor objectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | integer descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | string descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | array descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, closureEq⟩ := closureRelated.objectEq
      rw [constructor] at closureEq
      contradiction

/-- A unique ordinary constructor reset cannot expose release-fuel exhaustion
from its cleared-prefix child fold. The proof uses the rebound protocol heap
only while the parent contains the temporary reset descriptor; erased fields
remain concrete no-ops and therefore require no source-fault premise. -/
theorem LiveHeapRel.resetObject_unique_ne_releaseFuelExhausted
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {object : ConstructorObject} {count : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1) (constructor : cell.object = .ctor object)
    (countFits : count ≤ object.objectFields.size) :
    resetObject state count address witness.closureDescriptors ≠
      .error (.target .releaseFuelExhausted) := by
  intro targetOperation
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  cases targetRelated with
  | @constructor info fieldKinds semantic header _ descriptor objectEq
      objectRelated headerRead headerKind refCount persistent cellLive =>
      rw [constructor] at objectEq
      injection objectEq with semanticEq
      subst semantic
      let replacement : HeapCell :=
        { cell with object := .ctor (resetProtocolObject object count) }
      obtain ⟨middleRuntime, semanticSet, _, _, _, _⟩ :=
        setCell_spec_of_find runtime location cell replacement found
      obtain ⟨words, ownedRead, ownershipRelated⟩ :=
        objectRelated.readOwnedPrefix count countFits
      have fieldsBeforeFrontier :
          objectFieldAddress address.value count ≤ state.heapCursor := by
        have aligned := align8_ge
          (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
            info.ssize)
        have activeExtent := objectRelated.extent
        have countFitsInfo : count ≤ info.size := by
          rw [← objectRelated.semanticObjectFields]
          exact countFits
        simp [objectFieldAddress, ConstructorLayout.ofInfo, target]
          at aligned activeExtent ⊢
        omega
      have fieldsInBounds :
          objectFieldAddress address.value (0 + count) ≤ state.memory.size := by
        simp only [Nat.zero_add]
        exact Nat.le_trans fieldsBeforeFrontier
          related.frontier.cursorInBounds
      obtain ⟨fieldMemory, fieldWrite, _⟩ :=
        writeObjectFields_spec state.memory address.value 0
          (List.replicate count taggedZero) (by simpa using fieldsInBounds)
      obtain ⟨protocolRuntime, protocolSet, protocolHeap, _⟩ :=
        LiveHeapRel.writeObjectFields_resetPrefix state fieldMemory witness
          runtime location address cell header info fieldKinds object count
          related mapped found descriptor constructor objectRelated headerRead
          headerKind refCount persistent cellLive countFits fieldWrite
      have protocolRuntimeEq : protocolRuntime = middleRuntime :=
        Except.ok.inj (protocolSet.symm.trans semanticSet)
      subst protocolRuntime
      have protocolOwnership :=
        ownershipRelated.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)
      have concreteFoldSafe :=
        protocolOwnership.foldlM_public_ne_releaseFuelExhausted protocolHeap
      obtain ⟨addressHeap, _, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address header
          headerRead
      obtain ⟨objectHeader, objectHeaderRead, _, _, _, objectCount, _, _⟩ :=
        objectRelated.header
      rw [headerRead] at objectHeaderRead
      have objectHeaderEq := Except.ok.inj objectHeaderRead
      subst objectHeader
      have headerOrdinary : header.persistent = false :=
        persistent.trans ordinary
      have headerOne : header.refCount = 1 := by
        apply UInt32.toNat.inj
        simpa [unique] using refCount
      have notPromoted : header.isPromotedTag = false := by
        have different :
            (ObjectKind.constructor == ObjectKind.natural) = false := by decide
        simp [Header.isPromotedTag, headerKind, different]
      have countFitsInfo : count ≤ info.size := by
        rw [← objectRelated.semanticObjectFields]
        exact countFits
      have headerKindCheck :
          (header.kind == ObjectKind.constructor) = true := by
        rw [headerKind]
        decide
      have concreteFoldOriginalSafe :
          words.foldlM
              (init := ({ state with memory := fieldMemory } : MemoryState))
              (fun next child => decrementReferenceOnce next child true
                witness.closureDescriptors) ≠
            .error (.target .releaseFuelExhausted) := by
        simpa [RefinementWitness.rebindConstructor] using concreteFoldSafe
      simp only [resetObject] at targetOperation
      rw [addressHeap, headerRead] at targetOperation
      simp only [Bind.bind, Except.bind, liftMemory] at targetOperation
      rw [if_neg (by simp [notPromoted, headerOrdinary, headerOne])]
        at targetOperation
      rw [if_pos headerKindCheck] at targetOperation
      rw [objectCount, if_neg (Nat.not_lt.mpr countFitsInfo)]
        at targetOperation
      rw [ownedRead, fieldWrite] at targetOperation
      simp only at targetOperation
      cases concreteFoldOperation :
          words.foldlM
            (init := ({ state with memory := fieldMemory } : MemoryState))
            (fun next child => decrementReferenceOnce next child true
              witness.closureDescriptors) with
      | error failure =>
          rw [concreteFoldOperation] at targetOperation
          have failureEq :
              failure = (.target .releaseFuelExhausted : ConcreteError) :=
            Except.error.inj targetOperation
          subst failure
          exact concreteFoldOriginalSafe concreteFoldOperation
      | ok finalState =>
          rw [concreteFoldOperation] at targetOperation
          contradiction
  | boxed descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | natural descriptor objectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | integer descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | string descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | array descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, closureEq⟩ := closureRelated.objectEq
      rw [constructor] at closureEq
      contradiction

/-- Reset's fallback gate cannot expose release-fuel exhaustion. The gate is
taken for a persistent or nonunique represented cell and delegates exactly
one public checked decrement, whose target-safety theorem supplies the result. -/
theorem LiveHeapRel.resetObject_fallback_ne_releaseFuelExhausted
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {count : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (fallbackSemantic : cell.persistent = true ∨ cell.rc ≠ 1) :
    resetObject state count address witness.closureDescriptors ≠
      .error (.target .releaseFuelExhausted) := by
  intro targetOperation
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, persistent, refCount⟩ :=
    targetRelated.ownershipHeader
  have fallback :
      (header.isPromotedTag || header.persistent || header.refCount != 1) =
        true := by
    rcases fallbackSemantic with semanticPersistent | notUnique
    · have headerPersistent : header.persistent = true :=
        persistent.trans semanticPersistent
      simp [notPromoted, headerPersistent]
    · have headerCountNe : header.refCount ≠ 1 := by
        intro one
        rw [one] at refCount
        simp at refCount
        exact notUnique refCount.symm
      simp [notPromoted, headerCountNe]
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  have decrementSafe :=
    related.decrementReferenceOnce_ne_releaseFuelExhausted mapped true
  simp only [resetObject] at targetOperation
  rw [addressHeap, headerRead] at targetOperation
  simp only [Bind.bind, Except.bind, liftMemory] at targetOperation
  rw [if_pos fallback] at targetOperation
  cases decrementOperation :
      decrementReferenceOnce state address true witness.closureDescriptors with
  | error failure =>
      rw [decrementOperation] at targetOperation
      have failureEq :
          failure = (.target .releaseFuelExhausted : ConcreteError) :=
        Except.error.inj targetOperation
      subst failure
      exact decrementSafe decrementOperation
  | ok nextState =>
      rw [decrementOperation] at targetOperation
      contradiction

/-- Complete reset release-fuel target safety for every mapped semantic heap
reference. Dead, nonconstructor, and bounds failures stop before ownership
recursion; persistent or nonunique cells use the fallback theorem; an
in-bounds unique constructor uses the reset-prefix fold theorem. -/
theorem LiveHeapRel.resetObject_ne_releaseFuelExhausted
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (count : Nat) :
    resetObject state count address witness.closureDescriptors ≠
      .error (.target .releaseFuelExhausted) := by
  intro targetOperation
  obtain ⟨cell, found, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  cases live : cell.live with
  | false =>
      have concreteOperation :=
        (related.resetObject_deadObject (.mapped mapped) found live count
          witness.closureDescriptors).1
      rw [concreteOperation] at targetOperation
      cases Except.error.inj targetOperation
  | true =>
      by_cases persistent : cell.persistent = true
      · exact related.resetObject_fallback_ne_releaseFuelExhausted mapped found
          live (.inl persistent) targetOperation
      · have ordinary : cell.persistent = false := by
          cases persistentEq : cell.persistent with
          | false => rfl
          | true => exact False.elim (persistent persistentEq)
        by_cases unique : cell.rc = 1
        · by_cases constructorCase :
              ∃ object, cell.object = .ctor object
          · obtain ⟨object, constructor⟩ := constructorCase
            by_cases countFits : count ≤ object.objectFields.size
            · exact related.resetObject_unique_ne_releaseFuelExhausted mapped
                found live ordinary unique constructor countFits targetOperation
            · have concreteOperation :=
                (related.resetObject_outOfBounds_refines (.mapped mapped) found
                  live ordinary unique constructor count
                  (Nat.lt_of_not_ge countFits)
                  witness.closureDescriptors).1
              rw [concreteOperation] at targetOperation
              cases Except.error.inj targetOperation
          · have notConstructor : ∀ object, cell.object ≠ .ctor object := by
              intro object constructor
              exact constructorCase ⟨object, constructor⟩
            have concreteOperation :=
              (related.resetObject_expectedConstructor_refines (.mapped mapped)
                found live ordinary unique notConstructor count
                witness.closureDescriptors).1
            rw [concreteOperation] at targetOperation
            cases Except.error.inj targetOperation
        · exact related.resetObject_fallback_ne_releaseFuelExhausted mapped
            found live (.inr unique) targetOperation

/-- A live nonunique reset delegates its entire failing branch to one public
checked decrement. The reset wrapper preserves the exact non-fuel source
fault and performs no token-producing continuation. -/
theorem LiveHeapRel.resetObject_nonunique_fault_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {count : Nat} {fault : RuntimeFault}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (notUnique : cell.rc ≠ 1)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticOperation :
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .error fault) :
    ∃ failure,
      resetObject state count address witness.closureDescriptors =
          .error failure ∧
      ConcreteErrorSourceRel witness failure fault := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, _, refCount⟩ :=
    targetRelated.ownershipHeader
  have headerCountNe : header.refCount ≠ 1 := by
    intro one
    rw [one] at refCount
    simp at refCount
    exact notUnique refCount.symm
  have fallback :
      (header.isPromotedTag || header.persistent || header.refCount != 1) =
        true := by
    simp [notPromoted, headerCountNe]
  have semanticDec :
      Fir.LeanIR.Impure.decLocation runtime location = .error fault := by
    unfold Fir.LeanIR.Impure.reset at semanticOperation
    simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
      at semanticOperation
    rw [if_pos (by simp [notUnique])] at semanticOperation
    cases decEq : Fir.LeanIR.Impure.decLocation runtime location with
    | error childFault =>
        rw [decEq] at semanticOperation
        have childFaultEq : childFault = fault :=
          Except.error.inj semanticOperation
        subst childFault
        rfl
    | ok nextRuntime =>
        rw [decEq] at semanticOperation
        contradiction
  obtain ⟨failure, concreteDec, faultRelated⟩ :=
    related.decrementReferenceOnce_fault_refines mapped true notFuel
      semanticDec
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  have concreteReset :
      resetObject state count address witness.closureDescriptors =
        .error failure := by
    unfold resetObject
    rw [addressHeap, headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_pos fallback, concreteDec]
  exact ⟨failure, concreteReset, faultRelated⟩

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

/-- Every finite repeated decrement of a represented heap object excludes the
target-only release-fuel trap. This is the public ownership-operation form
used by generated nonpersistent decrements. -/
theorem LiveHeapRel.decrementReference_ne_releaseFuelExhausted
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {amount : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (check : Bool) :
    decrementReference state address amount check witness.closureDescriptors ≠
      .error (.target .releaseFuelExhausted) := by
  intro targetOperation
  cases semanticOperation :
      Fir.LeanIR.Impure.decValue runtime (.object (.heap location)) amount check
  with
  | ok nextRuntime =>
      obtain ⟨result, concreteOperation, _⟩ :=
        related.decrementReference_refines mapped check semanticOperation
      rw [targetOperation] at concreteOperation
      contradiction
  | error fault =>
      have notFuel :
          fault ≠
            .malformed "reference-count release fuel exhausted" := by
        intro faultEq
        subst fault
        exact decValue_heap_ne_releaseFuelExhausted runtime location amount check
          semanticOperation
      obtain ⟨failure, concreteOperation, faultRelated⟩ :=
        related.decrementReference_fault_refines mapped check notFuel
          semanticOperation
      rw [targetOperation] at concreteOperation
      have failureEq : (.target .releaseFuelExhausted : ConcreteError) =
          failure :=
        Except.error.inj concreteOperation
      subst failure
      cases faultRelated

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
