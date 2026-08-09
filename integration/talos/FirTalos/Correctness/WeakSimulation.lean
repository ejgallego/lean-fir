import FirTalos.Correctness.Execution

/-!
# Heterogeneous observable weak simulation

The LCNF pass proofs already use a same-machine stuttering relation.  The
LCNF-to-Wasm boundary needs the corresponding heterogeneous form: source and
target configurations have different types and a source transition may be
implemented by any finite number of target transitions.

This file deliberately does not choose a Wasm transition system.  In
particular, Talos's executable `Wasm.run` is a fuel-bounded big-step function
whose `OutOfFuel` result does not expose a resumable configuration.  The W6
compiler theorem will instantiate this framework only after defining a
resumable target configuration and relating its terminating executions back to
`Wasm.run`.
-/

namespace FirTalos.Correctness

universe uState uObservation vState vObservation

/-- A transition system together with the observation available at every
finite configuration, not merely at termination. -/
structure ObservableTransitionSystem where
  State : Type uState
  Observation : Type uObservation
  step : State → State → Prop
  observe : State → Observation

/-- An exact-length finite path for an arbitrary transition relation. -/
inductive FinitePath (step : α → α → Prop) : Nat → α → α → Prop where
  | refl (state : α) : FinitePath step 0 state state
  | cons (head : step before middle)
      (tail : FinitePath step count middle after) :
      FinitePath step (Nat.succ count) before after

namespace FinitePath

/-- One transition as a length-one finite path. -/
theorem single (transition : step before after) :
    FinitePath step 1 before after :=
  .cons transition (.refl after)

/-- Concatenation retains the exact sum of the two path lengths. -/
theorem trans
    (first : FinitePath step firstCount before middle)
    (second : FinitePath step secondCount middle after) :
    FinitePath step (firstCount + secondCount) before after := by
  induction first with
  | refl => simpa using second
  | cons head tail ih =>
      simpa [Nat.succ_add] using FinitePath.cons head (ih second)

/-- A zero-length path cannot change configurations. -/
theorem eq_of_zero (path : FinitePath step 0 before after) : before = after := by
  cases path
  rfl

end FinitePath

/-- Reachability hides the exact finite number of transitions. -/
def FiniteReaches (step : α → α → Prop) (before after : α) : Prop :=
  ∃ count, FinitePath step count before after

@[refl] theorem finiteReaches_refl (state : α) :
    FiniteReaches step state state :=
  ⟨0, .refl state⟩

theorem finiteReaches_of_step (transition : step before after) :
    FiniteReaches step before after :=
  ⟨1, .single transition⟩

theorem FiniteReaches.trans
    (first : FiniteReaches step before middle)
    (second : FiniteReaches step middle after) :
    FiniteReaches step before after := by
  obtain ⟨firstCount, first⟩ := first
  obtain ⟨secondCount, second⟩ := second
  exact ⟨firstCount + secondCount, first.trans second⟩

/-- The complete result of matching one source transition or finite source
path.  Keeping the target step count visible permits later divergence proofs
to rule out infinite zero-step stuttering. -/
def WeakPathMatch
    (targetStep : Target → Target → Prop)
    (relation : Source → Target → Prop)
    (sourceAfter : Source) (targetBefore : Target) : Prop :=
  ∃ count targetAfter,
    FinitePath targetStep count targetBefore targetAfter ∧
    relation sourceAfter targetAfter

/-- Observation-aware heterogeneous weak simulation.  A source step may be
matched by zero or more target steps, and every related finite configuration
must expose related observations. -/
structure ObservedWeakSimulation
    (source : ObservableTransitionSystem.{uState, uObservation})
    (target : ObservableTransitionSystem.{vState, vObservation}) where
  relation : source.State → target.State → Prop
  observationRel : source.Observation → target.Observation → Prop
  observes : ∀ {sourceState targetState}, relation sourceState targetState →
    observationRel (source.observe sourceState) (target.observe targetState)
  advance : ∀ {sourceBefore sourceAfter targetBefore},
    relation sourceBefore targetBefore →
    source.step sourceBefore sourceAfter →
    WeakPathMatch target.step relation sourceAfter targetBefore

namespace ObservedWeakSimulation

/-- Match an arbitrary finite source path by concatenating the target paths
chosen for its individual transitions. -/
theorem matchPath
    (simulation : ObservedWeakSimulation source target)
    (related : simulation.relation sourceBefore targetBefore)
    (path : FinitePath source.step count sourceBefore sourceAfter) :
    WeakPathMatch target.step simulation.relation sourceAfter targetBefore := by
  induction path generalizing targetBefore with
  | refl =>
      exact ⟨0, targetBefore, .refl targetBefore, related⟩
  | cons head tail ih =>
      obtain ⟨firstCount, targetMiddle, firstPath, middleRelated⟩ :=
        simulation.advance related head
      obtain ⟨restCount, targetAfter, restPath, finalRelated⟩ :=
        ih middleRelated
      exact ⟨firstCount + restCount, targetAfter,
        firstPath.trans restPath, finalRelated⟩

/-- Every finite source prefix has a finite target match whose current
observation is related.  This is the trace-preservation result used by a weak
simulation; it neither assumes nor concludes termination. -/
theorem finitePrefix
    (simulation : ObservedWeakSimulation source target)
    (related : simulation.relation sourceBefore targetBefore)
    (path : FinitePath source.step count sourceBefore sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath target.step targetCount targetBefore targetAfter ∧
      simulation.relation sourceAfter targetAfter ∧
      simulation.observationRel
        (source.observe sourceAfter) (target.observe targetAfter) := by
  obtain ⟨targetCount, targetAfter, targetPath, finalRelated⟩ :=
    simulation.matchPath related path
  exact ⟨targetCount, targetAfter, targetPath, finalRelated,
    simulation.observes finalRelated⟩

/-- The count-erased reachability formulation of `finitePrefix`. -/
theorem reaches
    (simulation : ObservedWeakSimulation source target)
    (related : simulation.relation sourceBefore targetBefore)
    (path : FiniteReaches source.step sourceBefore sourceAfter) :
    ∃ targetAfter,
      FiniteReaches target.step targetBefore targetAfter ∧
      simulation.relation sourceAfter targetAfter ∧
      simulation.observationRel
        (source.observe sourceAfter) (target.observe targetAfter) := by
  obtain ⟨count, path⟩ := path
  obtain ⟨targetCount, targetAfter, targetPath, finalRelated, observations⟩ :=
    simulation.finitePrefix related path
  exact ⟨targetAfter, ⟨targetCount, targetPath⟩, finalRelated, observations⟩

end ObservedWeakSimulation

/-- A weak simulation equipped with a well-founded source rank for zero-step
matches.  A source transition may stutter on the target only while this rank
strictly decreases.  Consequently an infinite source execution cannot be
matched forever by zero target transitions; this is the progress premise
needed to strengthen finite-prefix preservation to silent-divergence
preservation. -/
structure RankedObservedWeakSimulation
    (source : ObservableTransitionSystem.{uState, uObservation})
    (target : ObservableTransitionSystem.{vState, vObservation}) where
  relation : source.State → target.State → Prop
  observationRel : source.Observation → target.Observation → Prop
  rank : source.State → Nat
  observes : ∀ {sourceState targetState}, relation sourceState targetState →
    observationRel (source.observe sourceState) (target.observe targetState)
  advance : ∀ {sourceBefore sourceAfter targetBefore},
    relation sourceBefore targetBefore →
    source.step sourceBefore sourceAfter →
    ∃ targetCount targetAfter,
      FinitePath target.step targetCount targetBefore targetAfter ∧
      relation sourceAfter targetAfter ∧
      (targetCount = 0 → rank sourceAfter < rank sourceBefore)

/-- Forget only the anti-stuttering rank, retaining ordinary finite-prefix
weak simulation. -/
noncomputable def RankedObservedWeakSimulation.toObserved
    (simulation : RankedObservedWeakSimulation source target) :
    ObservedWeakSimulation source target where
  relation := simulation.relation
  observationRel := simulation.observationRel
  observes := simulation.observes
  advance := by
    intro sourceBefore sourceAfter targetBefore related transition
    obtain ⟨targetCount, targetAfter, path, finalRelated, _progress⟩ :=
      simulation.advance related transition
    exact ⟨targetCount, targetAfter, path, finalRelated⟩

/-- The ranked interface exposes its intended finite-trace theorem without a
termination premise. -/
theorem RankedObservedWeakSimulation.finitePrefix
    (simulation : RankedObservedWeakSimulation source target)
    (related : simulation.relation sourceBefore targetBefore)
    (path : FinitePath source.step count sourceBefore sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath target.step targetCount targetBefore targetAfter ∧
      simulation.relation sourceAfter targetAfter ∧
      simulation.observationRel
        (source.observe sourceAfter) (target.observe targetAfter) :=
  simulation.toObserved.finitePrefix related path

end FirTalos.Correctness
