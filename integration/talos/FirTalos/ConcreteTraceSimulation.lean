import FirTalos.Correctness.WeakSimulation
import FirTalos.ConcreteRuntime

/-!
# Concrete finite-trace simulation boundary

This module fixes the observations and progress contract for the W6
LCNF-to-Wasm simulation without pretending that Talos's current big-step
interpreter is resumable.  A later module will supply the actual structured
Wasm configuration and prove its terminating executions agree with
`Wasm.run`.
-/

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.Wasm.Concrete
open Fir.LeanIR.Impure
open FirTalos.Correctness

/-- The externally visible prefix of a source interpreter configuration. -/
structure SourcePrefixObservation where
  world : Nat
  trace : Array ExternalEvent

/-- The externally visible prefix of a concrete Wasm runtime configuration. -/
structure ConcretePrefixObservation where
  world : Nat
  trace : Array ConcreteExternalEvent

def sourcePrefixObservation (state : MachineState) : SourcePrefixObservation :=
  { world := state.runtime.world
    trace := state.runtime.trace }

def concretePrefixObservation (store : Wasm.Store Host) :
    ConcretePrefixObservation :=
  { world := store.host.runtime.world
    trace := store.host.runtime.trace }

/-- Source prefixes use the deterministic interpreter transition that retains
the successor configuration after every successful internal or external
step. -/
def sourceExecutionSystem (externals : ExternalImpl) :
    ObservableTransitionSystem where
  State := MachineState
  Observation := SourcePrefixObservation
  step := fun before after => executeStep externals before = .next after
  observe := sourcePrefixObservation

/-- Interface required of the resumable concrete Wasm semantics.  The state
must retain enough control to resume and must expose the current concrete
store.  This is intentionally stronger than a fuel result that says only
`OutOfFuel`. -/
structure ConcreteResumableMachine where
  State : Type
  step : State → State → Prop
  store : State → Wasm.Store Host

def ConcreteResumableMachine.system (machine : ConcreteResumableMachine) :
    ObservableTransitionSystem where
  State := machine.State
  Observation := ConcretePrefixObservation
  step := machine.step
  observe := fun state => concretePrefixObservation (machine.store state)

/-- Exact world and external-event trace agreement at a finite prefix.  Heap
addresses inside event arguments/results may differ only through the same W6
refinement witness used by the concrete runtime proofs. -/
def ConcretePrefixObservationRel
    (source : SourcePrefixObservation)
    (target : ConcretePrefixObservation) : Prop :=
  ∃ witness : RefinementWitness,
    target.world = source.world ∧
    ConcreteTraceRel witness target.trace source.trace

/-- The precise W6 simulation object to construct for a supported generated
export.  Zero-step target matches are permitted only while a source rank
strictly decreases, excluding infinite silent stuttering. -/
structure ConcreteRankedTraceSimulation
    (externals : ExternalImpl) (target : ConcreteResumableMachine) where
  relation : MachineState → target.State → Prop
  rank : MachineState → Nat
  observes : ∀ {sourceState targetState},
    relation sourceState targetState →
      ConcretePrefixObservationRel
        (sourcePrefixObservation sourceState)
        (concretePrefixObservation (target.store targetState))
  advance : ∀ {sourceBefore sourceAfter targetBefore},
    relation sourceBefore targetBefore →
    executeStep externals sourceBefore = .next sourceAfter →
    ∃ targetCount targetAfter,
      FinitePath target.step targetCount targetBefore targetAfter ∧
      relation sourceAfter targetAfter ∧
      (targetCount = 0 → rank sourceAfter < rank sourceBefore)

/-- The concrete contract is an instance of the generic ranked observable
weak-simulation framework. -/
def ConcreteRankedTraceSimulation.toGeneric
    {externals : ExternalImpl} {target : ConcreteResumableMachine}
    (simulation : ConcreteRankedTraceSimulation externals target) :
    RankedObservedWeakSimulation (sourceExecutionSystem externals)
      target.system where
  relation := simulation.relation
  observationRel := ConcretePrefixObservationRel
  rank := simulation.rank
  observes := simulation.observes
  advance := simulation.advance

/-- The source interpreter's exact finite-step evidence embeds directly into
the generic finite-path relation. -/
theorem finitePath_of_execSteps
    {externals : ExternalImpl}
    {count : Nat} {before after : MachineState}
    (steps : ExecSteps externals count before after) :
    FinitePath (sourceExecutionSystem externals).step count before after := by
  induction steps with
  | refl => exact .refl _
  | step head _tail ih => exact .cons head ih

/-- Main finite-prefix consequence of the concrete simulation boundary.

For every finite source execution prefix, independently of whether the whole
source program terminates, there is a finite target prefix with the exact same
world/trace observation modulo the concrete address witness. -/
theorem ConcreteRankedTraceSimulation.execSteps
    {externals : ExternalImpl} {target : ConcreteResumableMachine}
    {count : Nat} {sourceBefore sourceAfter : MachineState}
    {targetBefore : target.State}
    (simulation : ConcreteRankedTraceSimulation externals target)
    (related : simulation.relation sourceBefore targetBefore)
    (steps : ExecSteps externals count sourceBefore sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath target.step targetCount targetBefore targetAfter ∧
      simulation.relation sourceAfter targetAfter ∧
      ConcretePrefixObservationRel
        (sourcePrefixObservation sourceAfter)
        (concretePrefixObservation (target.store targetAfter)) :=
  simulation.toGeneric.finitePrefix related (finitePath_of_execSteps steps)

/-- Public shape of the eventual compiler theorem from a concrete source and
target entry.  The witness is a simulation relation generated from the
compiler proof itself, not a translation certificate supplied by its caller. -/
def ConcreteFiniteTraceCorrect
    (externals : ExternalImpl) (target : ConcreteResumableMachine)
    (sourceInitial : MachineState) (targetInitial : target.State) : Prop :=
  ∃ simulation : ConcreteRankedTraceSimulation externals target,
    simulation.relation sourceInitial targetInitial

end FirTalos.Concrete
