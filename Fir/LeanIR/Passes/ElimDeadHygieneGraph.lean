import Fir.LeanIR.Passes.ElimDeadHygiene
import Fir.LeanIR.Passes.ElimDeadProgram

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler

/-!
Proof-relevant exact graphs for the transparent `elimDeadVars` traversal.

The operational `ShadowCodeGraph` is intentionally `Prop`-valued and permits
monotone liveness widening.  It is therefore the right relation for runtime
environment agreement, but the wrong place to recover which computational
branch made a deletion decision.  This module retains the exact traversal
seed and replays its branch decisions as transparent data before forgetting
them into the monotone graph.
-/

/-- Exact successful traversal witness.  Unlike `ShadowCodeGraph`, the final
liveness set is not widened and the seed remains proof-relevant data. -/
structure ExactShadowCodeGraph (fuel : Nat) (final : UsedLocals)
    (source target : LCNF.Code .impure) where
  initial : UsedLocals
  result : shadowCode? fuel initial source = some (target, final)

def ExactShadowCodeGraph.ofResult
    {initial : UsedLocals}
    (result : shadowCode? fuel initial source = some (target, final)) :
    ExactShadowCodeGraph fuel final source target :=
  ⟨initial, result⟩

/-- Forget exact branch provenance into the monotone operational graph. -/
theorem ExactShadowCodeGraph.toShadowCodeGraph
    (exact : ExactShadowCodeGraph fuel final source target) :
    ShadowCodeGraph fuel final source target :=
  ⟨fuel, exact.initial, final, Nat.le_refl fuel, exact.result, .refl final⟩

/-- Transparent replay of the let deletion decision at an exact traversal
seed.  `true` means the continuation succeeded, the binder was absent, and
the value passed `safeToElim`. -/
def shadowLetWasDeleted (fuel : Nat) (initial : UsedLocals)
    (declaration : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure) : Bool :=
  match fuel with
  | 0 => false
  | nextFuel + 1 =>
      match shadowCode? nextFuel initial continuation with
      | none => false
      | some (_, continuationUsed) =>
          !continuationUsed.contains declaration.fvarId &&
            safeToElim declaration.value

/-- Transparent replay of the join deletion decision. -/
def shadowJoinWasDeleted (fuel : Nat) (initial : UsedLocals)
    (declaration : LCNF.FunDecl .impure)
    (continuation : LCNF.Code .impure) : Bool :=
  match fuel with
  | 0 => false
  | nextFuel + 1 =>
      match shadowCode? nextFuel initial continuation with
      | none => false
      | some (_, continuationUsed) =>
          !continuationUsed.contains declaration.fvarId

/-- A successful exact let run selected as deleted exposes binder absence in
its exact final liveness set. -/
theorem ExactShadowCodeGraph.deletedLet_absent
    (exact : ExactShadowCodeGraph fuel final
      (.let declaration continuation) target)
    (deleted :
      shadowLetWasDeleted fuel exact.initial declaration continuation =
        true) :
    final.contains declaration.fvarId = false := by
  cases fuel with
  | zero => simp [shadowLetWasDeleted] at deleted
  | succ nextFuel =>
      cases continuationResult :
          shadowCode? nextFuel exact.initial continuation with
      | none => simp [shadowLetWasDeleted, continuationResult] at deleted
      | some output =>
          obtain ⟨targetContinuation, continuationUsed⟩ := output
          simp only [shadowLetWasDeleted, continuationResult,
            Bool.not_eq_true', Bool.and_eq_true] at deleted
          have keep :
              ¬(declaration.fvarId ∈ continuationUsed ∨
                safeToElim declaration.value = false) := by
            intro keep
            rcases keep with binderLive | notSafe <;> simp_all
          have exactResult := exact.result
          simp [shadowCode?, continuationResult, keep] at exactResult
          rcases exactResult with ⟨rfl, rfl⟩
          exact deleted.1

/-- A successful exact join run selected as deleted likewise exposes binder
absence in its exact final liveness set. -/
theorem ExactShadowCodeGraph.deletedJoin_absent
    (exact : ExactShadowCodeGraph fuel final
      (.jp declaration continuation) target)
    (deleted :
      shadowJoinWasDeleted fuel exact.initial declaration continuation =
        true) :
    final.contains declaration.fvarId = false := by
  cases declaration with
  | mk fvarId binderName params type body =>
      cases fuel with
      | zero => simp [shadowJoinWasDeleted] at deleted
      | succ nextFuel =>
          cases continuationResult :
              shadowCode? nextFuel exact.initial continuation with
          | none =>
              simp [shadowJoinWasDeleted, continuationResult] at deleted
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              simp only [shadowJoinWasDeleted, continuationResult,
                LCNF.FunDecl.fvarId, Bool.not_eq_true'] at deleted
              have keep : ¬fvarId ∈ continuationUsed := by
                simpa using deleted
              have exactResult := exact.result
              simp [shadowCode?, continuationResult, keep] at exactResult
              rcases exactResult with ⟨rfl, rfl⟩
              exact deleted

/-- Static active-node readiness for an exact graph.  The source equalities
avoid a dependent match and make the definition easy to consume from later
recursive graph certificates. -/
def ExactShadowCodeHeadBinderReady
    (exact : ExactShadowCodeGraph fuel final source target) : Prop :=
  (∀ declaration continuation,
      source = .let declaration continuation →
      shadowLetWasDeleted fuel exact.initial declaration continuation =
          true →
        final.contains declaration.fvarId = false) ∧
    ∀ declaration continuation,
      source = .jp declaration continuation →
      shadowJoinWasDeleted fuel exact.initial declaration continuation =
          true →
        final.contains declaration.fvarId = false

theorem ExactShadowCodeGraph.headBinderReady
    (exact : ExactShadowCodeGraph fuel final source target) :
    ExactShadowCodeHeadBinderReady exact := by
  constructor
  · intro declaration continuation sourceEq deleted
    subst source
    exact exact.deletedLet_absent deleted
  · intro declaration continuation sourceEq deleted
    subst source
    exact exact.deletedJoin_absent deleted

end Fir.LeanIR.Passes.ElimDead
