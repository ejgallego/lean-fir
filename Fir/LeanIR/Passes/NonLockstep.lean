import Fir.LeanIR.Passes.SimpCase

namespace Fir.LeanIR.Passes.NonLockstep

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.SimpCase

/-- Reachability hides the exact number of small steps. This is the basic
currency for transformations that add, remove, or reorder administrative
steps. -/
def Reaches (externals : ExternalSpec) (before after : MachineState) : Prop :=
  ∃ count, Steps externals count before after

@[refl] theorem reaches_refl (state : MachineState) :
    Reaches externals state state :=
  ⟨0, .refl state⟩

theorem reaches_of_step (step : Step externals before after) :
    Reaches externals before after :=
  ⟨1, .step step (.refl after)⟩

theorem Reaches.trans
    (first : Reaches externals before middle)
    (second : Reaches externals middle after) :
    Reaches externals before after := by
  rcases first with ⟨count, first⟩
  induction first with
  | refl state => exact second
  | step head tail ih =>
      rcases ih second with ⟨tailCount, combined⟩
      exact ⟨tailCount + 1, .step head combined⟩

/-- A predicate containing the initial state and closed under one semantic
step contains every finitely reachable state.  Compiler clients can expose
their local heap/control invariant once, without repeating induction over the
hidden step count carried by `Reaches`. -/
theorem Reaches.invariant
    {predicate : MachineState → Prop}
    (path : Reaches externals initial state)
    (initialReady : predicate initial)
    (preserved : ∀ {before after},
      predicate before → Step externals before after → predicate after) :
    predicate state := by
  rcases path with ⟨count, execution⟩
  induction execution with
  | refl => exact initialReady
  | step head tail ih =>
      exact ih (preserved initialReady head)

/-- A reachable prefix can be prepended to a terminating evaluation. -/
theorem evaluatesState_of_reaches
    (path : Reaches externals before after)
    (evaluation : EvaluatesState externals after observation) :
    EvaluatesState externals before observation := by
  rcases evaluation with ⟨count, final, execution, done⟩
  rcases path.trans ⟨count, execution⟩ with ⟨combinedCount, combined⟩
  exact ⟨combinedCount, final, combined, done⟩

/-- One-sided finite-stuttering simulation. A source step may be matched by
any finite number of target steps, including zero; terminal source states must
already have the same observable behavior on the target. -/
structure StutteringSimulation (externals : ExternalSpec)
    (relation : MachineState → MachineState → Prop) : Prop where
  terminal : ∀ {left right observation}, relation left right →
    coreStep left = .done observation →
      EvaluatesState externals right observation
  advance : ∀ {leftBefore leftAfter right}, relation leftBefore right →
    Step externals leftBefore leftAfter →
      ∃ rightAfter, Reaches externals right rightAfter ∧
        relation leftAfter rightAfter

/-- Two finite-stuttering simulations, with independently chosen matching
paths in the two directions. -/
structure StutteringBisimulation (externals : ExternalSpec)
    (relation : MachineState → MachineState → Prop) : Prop where
  forward : StutteringSimulation externals relation
  backward : StutteringSimulation externals (fun right left => relation left right)

/-- A stuttering simulation preserves every terminating observation. The
induction is on the source execution, not on the target step count. -/
theorem StutteringSimulation.evaluatesState
    (simulation : StutteringSimulation externals relation)
    (related : relation left right) :
    EvaluatesState externals left observation →
      EvaluatesState externals right observation := by
  rintro ⟨count, final, execution, done⟩
  induction execution generalizing right with
  | refl state => exact simulation.terminal related done
  | step head tail ih =>
      rcases simulation.advance related head with
        ⟨rightAfter, rightSteps, afterRelated⟩
      exact evaluatesState_of_reaches rightSteps (ih afterRelated done)

/-- A simulation maps an arbitrary finite source path to a finite target path.
This is the closure property needed to compose non-lockstep passes. -/
theorem StutteringSimulation.reaches
    (simulation : StutteringSimulation externals relation)
    (related : relation leftBefore rightBefore)
    (path : Reaches externals leftBefore leftAfter) :
    ∃ rightAfter, Reaches externals rightBefore rightAfter ∧
      relation leftAfter rightAfter := by
  rcases path with ⟨count, execution⟩
  induction execution generalizing rightBefore with
  | refl state => exact ⟨rightBefore, reaches_refl rightBefore, related⟩
  | step head tail ih =>
      rcases simulation.advance related head with
        ⟨rightSecond, rightHead, secondRelated⟩
      rcases ih secondRelated with
        ⟨rightAfter, rightTail, finalRelated⟩
      exact ⟨rightAfter, rightHead.trans rightTail, finalRelated⟩

/-- Relational composition, with the intermediate machine state hidden. -/
def RelationComp
    (first second : MachineState → MachineState → Prop)
    (left right : MachineState) : Prop :=
  ∃ middle, first left middle ∧ second middle right

/-- Finite-stuttering simulations compose. Matching paths from the first
simulation are themselves transported through the second simulation. -/
theorem StutteringSimulation.comp
    (first : StutteringSimulation externals firstRelation)
    (second : StutteringSimulation externals secondRelation) :
    StutteringSimulation externals
      (RelationComp firstRelation secondRelation) where
  terminal := by
    intro left right observation related done
    rcases related with ⟨middle, firstRelated, secondRelated⟩
    exact second.evaluatesState secondRelated (first.terminal firstRelated done)
  advance := by
    intro leftBefore leftAfter right related step
    rcases related with ⟨middleBefore, firstRelated, secondRelated⟩
    rcases first.advance firstRelated step with
      ⟨middleAfter, middleSteps, firstAfter⟩
    rcases second.reaches secondRelated middleSteps with
      ⟨rightAfter, rightSteps, secondAfter⟩
    exact ⟨rightAfter, rightSteps,
      ⟨middleAfter, firstAfter, secondAfter⟩⟩

/-- Transport a simulation across a pointwise equivalent presentation of its
state relation. -/
theorem StutteringSimulation.reindex
    (simulation : StutteringSimulation externals relation)
    (same : ∀ left right, newRelation left right ↔ relation left right) :
    StutteringSimulation externals newRelation where
  terminal := by
    intro left right observation related done
    exact simulation.terminal ((same left right).mp related) done
  advance := by
    intro leftBefore leftAfter right related step
    rcases simulation.advance ((same leftBefore right).mp related) step with
      ⟨rightAfter, rightSteps, afterRelated⟩
    exact ⟨rightAfter, rightSteps,
      (same leftAfter rightAfter).mpr afterRelated⟩

/-- Non-lockstep bisimulations compose. The backwards simulation differs only
by the presentation order of the hidden intermediate witness. -/
theorem StutteringBisimulation.comp
    (first : StutteringBisimulation externals firstRelation)
    (second : StutteringBisimulation externals secondRelation) :
    StutteringBisimulation externals
      (RelationComp firstRelation secondRelation) where
  forward := first.forward.comp second.forward
  backward := (second.backward.comp first.backward).reindex (by
    intro right left
    constructor
    · rintro ⟨middle, firstRelated, secondRelated⟩
      exact ⟨middle, secondRelated, firstRelated⟩
    · rintro ⟨middle, secondRelated, firstRelated⟩
      exact ⟨middle, firstRelated, secondRelated⟩)

/-- A finite-stuttering bisimulation gives observational equivalence without
requiring equal step counts or equal programs. -/
theorem StutteringBisimulation.evaluatesState_iff
    (bisimulation : StutteringBisimulation externals relation)
    (related : relation left right) :
    EvaluatesState externals left observation ↔
      EvaluatesState externals right observation :=
  ⟨bisimulation.forward.evaluatesState related,
    bisimulation.backward.evaluatesState related⟩

/-- Either the states coincide or the left state has one deterministic
internal administrative step to the right state. -/
inductive InternalPrefixOrEq : MachineState → MachineState → Prop where
  | refl (state : MachineState) : InternalPrefixOrEq state state
  | one (transition : coreStep before = .next after) :
      InternalPrefixOrEq before after

theorem internalPrefixForward (externals : ExternalSpec) :
    StutteringSimulation externals InternalPrefixOrEq where
  terminal := by
    intro left right observation related done
    cases related with
    | refl => exact ⟨0, _, .refl _, done⟩
    | one transition => simp [transition] at done
  advance := by
    intro leftBefore leftAfter right related step
    cases related with
    | refl => exact ⟨leftAfter, reaches_of_step step, .refl leftAfter⟩
    | one transition =>
        cases step with
        | internal actual =>
            rw [transition] at actual
            cases actual
            exact ⟨_, reaches_refl _, .refl _⟩
        | external actual external => simp [transition] at actual

theorem internalPrefixBackward (externals : ExternalSpec) :
    StutteringSimulation externals
      (fun right left => InternalPrefixOrEq left right) where
  terminal := by
    intro right left observation related done
    cases related with
    | refl => exact ⟨0, _, .refl _, done⟩
    | one transition =>
        exact evaluatesState_of_reaches
          (reaches_of_step (.internal transition))
          ⟨0, right, .refl right, done⟩
  advance := by
    intro rightBefore rightAfter left related step
    cases related with
    | refl => exact ⟨rightAfter, reaches_of_step step, .refl rightAfter⟩
    | one transition =>
        exact ⟨rightAfter,
          (reaches_of_step (.internal transition)).trans (reaches_of_step step),
          .refl rightAfter⟩

theorem internalPrefixBisimulation (externals : ExternalSpec) :
    StutteringBisimulation externals InternalPrefixOrEq where
  forward := internalPrefixForward externals
  backward := internalPrefixBackward externals

/-- Regression exercising genuine stuttering: the left administrative step is
matched by zero right steps in the forward direction. -/
theorem evaluatesState_internal_iff_via_stuttering
    (transition : coreStep before = .next after) :
    EvaluatesState externals before observation ↔
      EvaluatesState externals after observation :=
  (internalPrefixBisimulation externals).evaluatesState_iff (.one transition)

/-- Entering the selected case arm is exactly the one-step/zero-step shape
captured by `InternalPrefixOrEq`. -/
theorem selectedCase_internalPrefix
    {state : MachineState} {caseInfo : LCNF.Cases .impure}
    {discr : Value} {tag : Nat} {branch : LCNF.Code .impure}
    (lookupDiscr : lookupValue state.env caseInfo.discr = .ok discr)
    (readTag : getTag state.runtime discr = .ok tag)
    (selected : chooseAlt tag caseInfo.alts.toList = some branch) :
    InternalPrefixOrEq
      { state with control := .code (.cases caseInfo) }
      { state with control := .code branch } := by
  apply InternalPrefixOrEq.one
  simp [coreStep, lookupDiscr, readTag, selected]

/-- The first concrete pass-shaped use of the non-lockstep framework. -/
theorem selected_case_elimination_via_stuttering
    {state : MachineState} {caseInfo : LCNF.Cases .impure}
    {discr : Value} {tag : Nat} {branch : LCNF.Code .impure}
    (lookupDiscr : lookupValue state.env caseInfo.discr = .ok discr)
    (readTag : getTag state.runtime discr = .ok tag)
    (selected : chooseAlt tag caseInfo.alts.toList = some branch) :
    EvaluatesState externals
        { state with control := .code (.cases caseInfo) } observation ↔
      EvaluatesState externals
        { state with control := .code branch } observation :=
  (internalPrefixBisimulation externals).evaluatesState_iff
    (selectedCase_internalPrefix lookupDiscr readTag selected)

/-- The entry-state obligation for lifting a machine relation to a pass
theorem. Different entries and argument arrays may use different witnesses of
the same relation. -/
def InitialStatesRelated (relation : MachineState → MachineState → Prop)
    (before after : ImpureProgram) (entries : Array Name) : Prop :=
  ∀ entry, entry ∈ entries → ∀ args,
    relation (initialState before entry args) (initialState after entry args)

/-- A non-lockstep bisimulation that relates every original entry state proves
the repository's same-phase pass-correctness contract. -/
theorem samePhaseCorrect_of_stuttering
    (bisimulation : StutteringBisimulation externals relation)
    (initial : InitialStatesRelated relation before after entries) :
    SamePhaseCorrect (Impure.semantics externals) before after entries := by
  intro entry member args observation
  exact bisimulation.evaluatesState_iff (initial entry member args)

/-- Equality is the degenerate one-step instance of finite stuttering. -/
theorem equalitySimulation (externals : ExternalSpec) :
    StutteringSimulation externals (fun left right => left = right) where
  terminal := by
    intro left right observation related done
    subst right
    exact ⟨0, left, .refl left, done⟩
  advance := by
    intro leftBefore leftAfter right related step
    subst right
    exact ⟨_, reaches_of_step step, rfl⟩

theorem reverseEqualitySimulation (externals : ExternalSpec) :
    StutteringSimulation externals (fun left right => right = left) where
  terminal := by
    intro left right observation related done
    subst right
    exact ⟨0, left, .refl left, done⟩
  advance := by
    intro leftBefore leftAfter right related step
    subst right
    exact ⟨_, reaches_of_step step, rfl⟩

theorem equalityBisimulation (externals : ExternalSpec) :
    StutteringBisimulation externals (fun left right => left = right) where
  forward := equalitySimulation externals
  backward := reverseEqualitySimulation externals

/-- Regression for the program-level lifting interface. -/
theorem samePhaseCorrect_refl_via_stuttering
    (program : ImpureProgram) (entries : Array Name) :
    SamePhaseCorrect (Impure.semantics externals) program program entries := by
  apply samePhaseCorrect_of_stuttering (equalityBisimulation externals)
  intro entry member args
  rfl

end Fir.LeanIR.Passes.NonLockstep
