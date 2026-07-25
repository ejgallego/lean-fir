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
              recurseFault heap mapped childEq
            exact ⟨failure, by rw [concreteHead], faultRelated⟩
        | ok nextRuntime =>
            rw [childEq] at semanticOperation
            obtain ⟨nextState, concreteHead, nextHeap⟩ :=
              recurseSuccess heap mapped childEq
            obtain ⟨failure, concreteTail, faultRelated⟩ :=
              ih nextHeap semanticOperation
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
          ih heap semanticOperation
        refine ⟨failure, ?_, faultRelated⟩
        rw [concreteHead]
        exact concreteTail

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
