import Fir.Wasm.Concrete.ExternalCorrectness

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
