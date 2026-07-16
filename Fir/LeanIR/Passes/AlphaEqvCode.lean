import Fir.LeanIR.Passes.SimpCase

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.SimpCase

/-- The terminal fragment of the proof-facing impure-code relation. -/
inductive TerminalCodeRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) :
    LCNF.Code .impure → LCNF.Code .impure → Prop where
  | ret (related : ScopedFVarRelated rho leftScope rightScope leftId rightId) :
      TerminalCodeRelated rho leftScope rightScope (.return leftId) (.return rightId)
  | unreachable :
      TerminalCodeRelated rho leftScope rightScope (.unreach leftType) (.unreach rightType)

/-- The matching immediate outcomes of two related terminal instructions. -/
inductive TerminalResultRelated (leftEnv rightEnv : Env) (state : MachineState) :
    CoreResult → CoreResult → Prop where
  | yielded (value : Value) :
      TerminalResultRelated leftEnv rightEnv state
        (.next { state with env := leftEnv, control := .yielded value })
        (.next { state with env := rightEnv, control := .yielded value })
  | done (observation : Observation) :
      TerminalResultRelated leftEnv rightEnv state (.done observation) (.done observation)

theorem coreStep_terminal_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : TerminalCodeRelated rho leftScope rightScope left right) :
    TerminalResultRelated leftEnv rightEnv state
      (coreStep { state with env := leftEnv, control := .code left })
      (coreStep { state with env := rightEnv, control := .code right }) := by
  cases related with
  | ret related =>
      obtain ⟨value, leftFound, rightFound⟩ :=
        agree _ related.1 _ related.2.1 related.2.2
      simpa [coreStep, lookupValue, leftFound, rightFound] using
        TerminalResultRelated.yielded (state := state)
          (leftEnv := leftEnv) (rightEnv := rightEnv) value
  | unreachable =>
      simpa [coreStep, fail, observe] using
        TerminalResultRelated.done (state := state)
          (leftEnv := leftEnv) (rightEnv := rightEnv)
          (observe state (.fault .unreachable))

/-- A machine state whose core step is already done has exactly one observation. -/
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

theorem unreach_codeEquivalentAt (leftType rightType : Expr) :
    CodeEquivalentAt externals state (.unreach leftType) (.unreach rightType) := by
  intro observation
  have leftDone :
      coreStep { state with control := .code (.unreach leftType) } =
        .done (observe state (.fault .unreachable)) := by
    simp [coreStep, fail, observe]
  have rightDone :
      coreStep { state with control := .code (.unreach rightType) } =
        .done (observe state (.fault .unreachable)) := by
    simp [coreStep, fail, observe]
  rw [evaluatesState_done_iff leftDone, evaluatesState_done_iff rightDone]

theorem terminalCodeRelated_empty_sound
    (related : TerminalCodeRelated ({} : FVarIdMap FVarId) scope scope left right) :
    CodeEquivalentAt externals state left right := by
  cases related with
  | ret related =>
      rename_i leftId rightId
      have ids : leftId = rightId := by
        have fvarRelated := related.2.2
        change (leftId == rightId) = true at fvarRelated
        cases leftId with
        | mk leftName =>
            cases rightId with
            | mk rightName =>
                congr
                exact Name.beq_iff_eq.mp fvarRelated
      subst rightId
      exact codeEquivalentAt_refl
  | unreachable => exact unreach_codeEquivalentAt _ _

/--
Reduce executable terminal alpha-soundness to the missing checker-to-relation
bridge. Lean 4.32 exposes `LCNF.AlphaEqv.eqv` as an opaque `partial def`, so
that bridge cannot currently be proved by unfolding the checker.
-/
theorem alphaEqvSoundAt_of_terminal_bridge
    (bridge : left.alphaEqv right = true →
      TerminalCodeRelated ({} : FVarIdMap FVarId) scope scope left right) :
    AlphaEqvSoundAt externals state left right := by
  intro accepted
  exact terminalCodeRelated_empty_sound (bridge accepted)

end Fir.LeanIR.Passes.AlphaEqv
