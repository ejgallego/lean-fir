import Fir.LeanIR.Passes.NonLockstep

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.SimpCase

/-!
Proof kernels for Lean 4.32's impure `elimDeadVars` pass.

The upstream pass combines two independent obligations when it removes a
binding: evaluating the unused value must have no observable effect, and the
new binding must be irrelevant to the continuation.  Keeping those obligations
separate is useful both for the backwards liveness proof and for transformations
whose only runtime difference is unreachable heap garbage.
-/

/-- Audited local copy of Lean 4.32's impure `LetValue.safeToElim` predicate.
This is deliberately syntax-only; semantic safety is stated separately below. -/
def safeToElim : LCNF.LetValue .impure → Bool
  | .ctor .. | .reset .. | .reuse .. | .oproj .. | .uproj .. | .sproj ..
  | .lit .. | .pap .. | .box .. | .unbox .. | .erased .. | .isShared .. => true
  | .fap _ args => args.isEmpty
  | .fvar .. => false

/-- State-indexed semantic kernel for an eliminable value whose evaluation is
successful, returns an ordinary value, and leaves the runtime unchanged.  This
is the exact subset compatible with FIR's current raw-observation equality. -/
def RuntimeNeutralAt (state : MachineState)
    (declaration : LCNF.LetDecl .impure) : Prop :=
  ∃ value, evalLetValue state declaration =
    .ok (state.runtime, .value value)

/-- Semantic form of the backwards liveness obligation: extending the current
environment with the eliminated result does not affect the continuation. -/
def BindingIrrelevantAt (externals : ExternalSpec) (state : MachineState)
    (declaration : LCNF.LetDecl .impure) (value : Value)
    (continuation : LCNF.Code .impure) : Prop :=
  ∀ observation,
    EvaluatesState externals
        { state with
          env := bind state.env declaration.fvarId value
          control := .code continuation } observation ↔
      EvaluatesState externals
        { state with control := .code continuation } observation

/-- A runtime-neutral let evaluates by one internal step to its continuation
with the result added to the environment. -/
theorem evalLetValue_control_eq
    (state : MachineState) (control : Control)
    (declaration : LCNF.LetDecl .impure) :
    evalLetValue { state with control } declaration =
      evalLetValue state declaration := by
  cases declaration with
  | mk fvarId binderName type value =>
      cases value <;> rfl

theorem coreStep_runtimeNeutralLet
    (evaluated : evalLetValue state declaration =
      .ok (state.runtime, .value value)) :
    coreStep
        { state with control := .code (.let declaration continuation) } =
      .next
        { state with
          env := bind state.env declaration.fvarId value
          control := .code continuation } := by
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]

/-- First reusable elimination theorem.  The source takes one internal step,
the target stutters, and backwards liveness discharges the resulting extra
environment binding. -/
theorem eliminateLet_correct_of_runtimeNeutral
    (evaluated : evalLetValue state declaration =
      .ok (state.runtime, .value value))
    (irrelevant : BindingIrrelevantAt externals state declaration value
      continuation) :
    EvaluatesState externals
        { state with control := .code (.let declaration continuation) }
        observation ↔
      EvaluatesState externals
        { state with control := .code continuation } observation := by
  rw [evaluatesState_internal_iff
    (coreStep_runtimeNeutralLet (state := state) (declaration := declaration)
      (continuation := continuation) evaluated)]
  exact irrelevant observation

/-- Local form of the terminal-state characterization. -/
theorem evaluatesState_done_iff
    (done : coreStep initial = .done result) :
    EvaluatesState externals initial observation ↔ result = observation := by
  constructor
  · rintro ⟨count, final, execution, finalDone⟩
    cases execution with
    | refl _ => simpa [done] using finalDone
    | step head _ =>
        cases head with
        | internal transition => simp [done] at transition
        | external transition _ => simp [done] at transition
  · rintro rfl
    exact ⟨0, initial, .refl initial, done⟩

/-- An unreachable continuation observes neither the current lexical
environment nor the value of the eliminated binding. -/
theorem bindingIrrelevantAt_unreach
    (state : MachineState) (declaration : LCNF.LetDecl .impure)
    (value : Value) (type : Expr) :
    BindingIrrelevantAt externals state declaration value (.unreach type) := by
  intro observation
  let result := observe state (.fault .unreachable)
  have leftDone :
      coreStep
          { state with
            env := bind state.env declaration.fvarId value
            control := .code (.unreach type) } = .done result := by
    simp [coreStep, fail, result, observe]
  have rightDone :
      coreStep { state with control := .code (.unreach type) } =
        .done result := by
    simp [coreStep, fail, result, observe]
  rw [evaluatesState_done_iff leftDone, evaluatesState_done_iff rightDone]

/-- Executing an erased value is runtime-neutral in every state. -/
theorem erased_runtimeNeutralAt
    (state : MachineState) (fvarId : FVarId) (binderName : Name)
    (type : Expr) :
    RuntimeNeutralAt state
      { fvarId, binderName, type, value := .erased } := by
  exact ⟨.erased, rfl⟩

def erasedLetDecl (fvarId : FVarId) (binderName : Name) (type : Expr) :
    LCNF.LetDecl .impure :=
  { fvarId, binderName, type, value := .erased }

/-- Concrete kernel regression: an unused erased binding before `unreach` may
be deleted, with the source's administrative step matched by target stutter. -/
theorem eliminate_erased_before_unreach
    (state : MachineState) (fvarId : FVarId) (binderName : Name)
    (valueType resultType : Expr) :
    EvaluatesState externals
        { state with control := .code (.let
          (erasedLetDecl fvarId binderName valueType)
          (.unreach resultType)) } observation ↔
      EvaluatesState externals
        { state with control := .code (.unreach resultType) } observation := by
  apply eliminateLet_correct_of_runtimeNeutral
    (value := .erased)
  · rfl
  · exact bindingIrrelevantAt_unreach state
      (erasedLetDecl fvarId binderName valueType)
      .erased resultType

/-! ## Reachable-observation evidence for the whole pass -/

/-- The empty address renaming is sufficient when neither observation exposes
a heap location. -/
def emptyAddressRenaming : AddressRenaming where
  forward := fun _ => none
  reverse := fun _ => none
  leftInverse := by simp
  rightInverse := by simp

theorem not_reachable_from_erased
    (reachable : Reachable heap [.erased] location) : False := by
  induction reachable with
  | root member => simp at member
  | child _ _ _ _ parentImpossible => exact parentImpossible

/-- `ObservationRel` already expresses the equivalence needed for deleting a
dead allocation: arbitrary heaps are related when the only observable result
is erased and there are no external events. -/
theorem observationRel_returned_erased_ignore_heap
    (leftHeap rightHeap : Heap) (world : Nat) :
    ObservationRel
      { outcome := .returned .erased
        heap := leftHeap
        world
        trace := #[] }
      { outcome := .returned .erased
        heap := rightHeap
        world
        trace := #[] } := by
  refine ⟨emptyAddressRenaming, .erased, rfl, .nil, ?_⟩
  constructor
  · intro location reachable
    exact (not_reachable_from_erased reachable).elim
  · intro location reachable
    exact (not_reachable_from_erased reachable).elim

end Fir.LeanIR.Passes.ElimDead
