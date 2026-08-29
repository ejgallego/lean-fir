import FirTalos.ConcreteTraceSimulation
import Fir.LeanIR.Passes.NonLockstep

/-!
# Backward pass composition for the concrete Wasm theorem

This module connects FIR's existing finite-stuttering pass interface to the
generic observable finite-prefix framework used by W6.  It deliberately keeps
the pass observation relation explicit: address-renaming or representation
compatibility belongs in a reusable relation-composition theorem, not in a
program-specific execution witness.
-/

namespace FirTalos.Concrete

open FirTalos.Correctness
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.NonLockstep

/-- The relational external specification containing exactly the successful
responses selected by one deterministic interpreter implementation. -/
def executableExternalSpec (externals : ExternalImpl) : ExternalSpec :=
  fun request before response =>
    externals.call request before = .ok response

theorem externalImpl_implements_executableExternalSpec
    (externals : ExternalImpl) :
    externals.Implements (executableExternalSpec externals) := by
  intro request before response called
  exact called

/-- The relational step specialized to the implementation graph is precisely
the executable interpreter's successful successor relation. -/
theorem executeStep_next_iff_step_executableExternalSpec
    {externals : ExternalImpl} {before after : MachineState} :
    executeStep externals before = .next after ↔
      Step (executableExternalSpec externals) before after := by
  constructor
  · exact executeStep_sound
      (externalImpl_implements_executableExternalSpec externals)
  · intro step
    cases step with
    | internal transition =>
        simp [executeStep, transition]
    | external transition called =>
        unfold executeStep
        rw [transition]
        unfold executableExternalSpec at called
        simp [called]

/-- A relational execution over the exact implementation graph is executable
by that implementation with the same endpoints and step count. -/
theorem execSteps_of_steps_executableExternalSpec
    {externals : ExternalImpl} {count : Nat}
    {before after : MachineState}
    (steps : Steps (executableExternalSpec externals) count before after) :
    ExecSteps externals count before after := by
  induction steps with
  | refl state => exact .refl state
  | step head tail ih =>
      exact .step
        (executeStep_next_iff_step_executableExternalSpec.mpr head) ih

/-- FIR's count-erased pass reachability embeds into the exact generic finite
path used by the concrete backend theorem. -/
theorem finitePath_of_reaches_executableExternalSpec
    {externals : ExternalImpl} {before after : MachineState}
    (path : Reaches (executableExternalSpec externals) before after) :
    ∃ count,
      FinitePath (sourceExecutionSystem externals).step count before after := by
  obtain ⟨count, steps⟩ := path
  exact ⟨count, finitePath_of_execSteps
    (execSteps_of_steps_executableExternalSpec steps)⟩

/-- Turn an existing FIR finite-stuttering pass simulation into an observable
finite-prefix simulation for the deterministic source interpreter.  The only
new obligation is the pass's relation between prefix observations. -/
noncomputable def StutteringSimulation.toObservedFinitePrefixSimulation
    {externals : ExternalImpl}
    {relation : MachineState → MachineState → Prop}
    {observationRel : SourcePrefixObservation → SourcePrefixObservation → Prop}
    (simulation : StutteringSimulation
      (executableExternalSpec externals) relation)
    (observes : ∀ {before after}, relation before after →
      observationRel (sourcePrefixObservation before)
        (sourcePrefixObservation after)) :
    ObservedWeakSimulation (sourceExecutionSystem externals)
      (sourceExecutionSystem externals) where
  relation := relation
  observationRel := observationRel
  observes := observes
  advance := by
    intro sourceBefore sourceAfter targetBefore related transition
    have relationalStep :
        Step (executableExternalSpec externals) sourceBefore sourceAfter :=
      executeStep_next_iff_step_executableExternalSpec.mp transition
    obtain ⟨targetAfter, targetPath, finalRelated⟩ :=
      simulation.advance related relationalStep
    obtain ⟨targetCount, targetPath⟩ :=
      finitePath_of_reaches_executableExternalSpec targetPath
    exact ⟨targetCount, targetAfter, targetPath, finalRelated⟩

/-- Entry-point form of the pass adapter. -/
theorem StutteringSimulation.toObservedFinitePrefixCorrect
    {externals : ExternalImpl}
    {relation : MachineState → MachineState → Prop}
    {observationRel : SourcePrefixObservation → SourcePrefixObservation → Prop}
    {beforeInitial afterInitial : MachineState}
    (simulation : StutteringSimulation
      (executableExternalSpec externals) relation)
    (observes : ∀ {before after}, relation before after →
      observationRel (sourcePrefixObservation before)
        (sourcePrefixObservation after))
    (initial : relation beforeInitial afterInitial) :
    ObservedFinitePrefixCorrect (sourceExecutionSystem externals)
      (sourceExecutionSystem externals) beforeInitial afterInitial :=
  ⟨StutteringSimulation.toObservedFinitePrefixSimulation simulation observes,
    initial⟩

/-- Reusable one-edge backward composition theorem for impure LCNF passes.
The intermediate final-LCNF state and prefix observation are existential in
the resulting relations. -/
theorem ConcreteFiniteTraceCorrect.precomposeStutteringPass
    {externals : ExternalImpl} {target : ConcreteResumableMachine}
    {relation : MachineState → MachineState → Prop}
    {observationRel : SourcePrefixObservation → SourcePrefixObservation → Prop}
    {beforeInitial afterInitial : MachineState}
    {targetInitial : target.State}
    (simulation : StutteringSimulation
      (executableExternalSpec externals) relation)
    (observes : ∀ {before after}, relation before after →
      observationRel (sourcePrefixObservation before)
        (sourcePrefixObservation after))
    (initial : relation beforeInitial afterInitial)
    (wasmCorrect : ConcreteFiniteTraceCorrect externals target afterInitial
      targetInitial) :
    ObservedFinitePrefixCorrect (sourceExecutionSystem externals) target.system
      beforeInitial targetInitial :=
  (StutteringSimulation.toObservedFinitePrefixCorrect simulation observes
    initial).comp
    wasmCorrect.toObservedFinitePrefixCorrect

/-- The identity pass is a closed regression for the complete adapter and
backward-composition surface. -/
theorem ConcreteFiniteTraceCorrect.precomposeEqualityPass
    {externals : ExternalImpl} {target : ConcreteResumableMachine}
    {sourceInitial : MachineState} {targetInitial : target.State}
    (wasmCorrect : ConcreteFiniteTraceCorrect externals target sourceInitial
      targetInitial) :
    ObservedFinitePrefixCorrect (sourceExecutionSystem externals) target.system
      sourceInitial targetInitial :=
  wasmCorrect.precomposeStutteringPass
    (equalitySimulation (executableExternalSpec externals))
    (observationRel := Eq) (by
      intro before after equal
      cases equal
      rfl)
    rfl

end FirTalos.Concrete
