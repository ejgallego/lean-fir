import Fir.LeanIR.Passes.ElimDeadRelation
import Fir.LeanIR.Passes.Structural

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.NonLockstep.Structural

/-!
The declaration/program graph for the transparent `elimDeadVars` shadow.

This layer records only what the traversal produced.  Semantic admissibility
of an eliminated operation remains a separate phase premise: in particular,
the existing raw-observation contract cannot validate dead allocations whose
unreachable heap cells remain visible.
-/

/-- Two code bodies are related when some successful residual traversal,
bounded by the declaration's top-level fuel, produced the target.  Retaining
the threaded input set makes this one relation usable for branch bodies,
join bodies, and saved continuations as execution descends through the graph. -/
def ShadowCodeRelated (fuel : Nat)
    (source target : LCNF.Code .impure) : Prop :=
  ∃ remaining initial final, remaining ≤ fuel ∧
    shadowCode? remaining initial source = some (target, final)

/-- Every target body in the program graph carries the liveness coverage
proved for the transparent traversal. -/
theorem ShadowCodeRelated.covered
    (related : ShadowCodeRelated fuel source target) :
    ∃ final, CodeCovered final target := by
  rcases related with ⟨remaining, initial, final, bounded, result⟩
  exact ⟨final, (shadowCode_spec result).1⟩

/-- A successful declaration traversal preserves all declaration metadata and
either keeps identical external metadata or relates the two internal bodies. -/
theorem shadowDecl_related
    (result : shadowDecl? fuel source = some target) :
    DeclRelated (ShadowCodeRelated fuel) source target := by
  cases valueEq : source.value with
  | extern metadata =>
      simp [shadowDecl?, valueEq] at result
      subst target
      exact {
        name_eq := rfl
        levelParams_eq := rfl
        type_eq := rfl
        params_eq := rfl
        safe_eq := rfl
        value := by
          rw [valueEq]
          exact .extern metadata
        recursive_eq := rfl
        inlineAttr_eq := rfl
      }
  | code code =>
      cases transformed : shadowCode? fuel {} code with
      | none => simp [shadowDecl?, valueEq, transformed] at result
      | some output =>
          obtain ⟨targetCode, final⟩ := output
          simp [shadowDecl?, valueEq, transformed] at result
          subst target
          exact {
            name_eq := rfl
            levelParams_eq := rfl
            type_eq := rfl
            params_eq := rfl
            safe_eq := rfl
            value := by
              rw [valueEq]
              exact .code ⟨fuel, {}, final, Nat.le_refl fuel, transformed⟩
            recursive_eq := rfl
            inlineAttr_eq := rfl
          }

/-- The declaration-list traversal is pointwise related for lists of arbitrary
length. -/
theorem shadowDecls_related
    (result : shadowDecls? fuel sources = some targets) :
    ListRel (DeclRelated (ShadowCodeRelated fuel)) sources targets := by
  induction sources generalizing targets with
  | nil =>
      simp [shadowDecls?] at result
      subst targets
      exact .nil
  | cons source rest ih =>
      cases headResult : shadowDecl? fuel source with
      | none => simp [shadowDecls?, headResult] at result
      | some target =>
          cases tailResult : shadowDecls? fuel rest with
          | none => simp [shadowDecls?, headResult, tailResult] at result
          | some targetsRest =>
              simp [shadowDecls?, headResult, tailResult] at result
              subst targets
              exact .cons (shadowDecl_related headResult) (ih tailResult)

/-- A successful whole-program shadow traversal preserves ordered declaration
lookup and relates every internal body produced by the same fuel bound. -/
theorem shadowProgram_related
    (result : shadowProgram? fuel source = some target) :
    ProgramRelated (ShadowCodeRelated fuel) source target := by
  cases declarationsResult : shadowDecls? fuel source.decls.toList with
  | none => simp [shadowProgram?, declarationsResult] at result
  | some declarations =>
      simp [shadowProgram?, declarationsResult] at result
      subst target
      unfold ProgramRelated
      simpa using shadowDecls_related declarationsResult

end Fir.LeanIR.Passes.ElimDead
