import Fir.LeanIR.PassCorrectness
import Lean.Compiler.LCNF.AlphaEqv

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.ImpureHygiene

/-- Lean's right-to-left free-variable lookup, exposed as a proposition. -/
def FVarRelated (rho : FVarIdMap FVarId) (left right : FVarId) : Prop :=
  (LCNF.AlphaEqv.eqvFVar left right).run rho = true

/-- Every variable in a syntactic scope has a runtime value. -/
def EnvCovers (scope : List FVarId) (env : Env) : Prop :=
  ∀ fvarId, scope.contains fvarId = true → ∃ value, lookup env fvarId = some value

/--
Two runtime environments agree on every alpha-related pair in their current
syntactic scopes. Values, unlike identifiers, are unchanged by alpha-renaming.
-/
def EnvsAgree (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) (left right : Env) : Prop :=
  ∀ leftId, leftScope.contains leftId = true →
    ∀ rightId, rightScope.contains rightId = true →
      FVarRelated rho leftId rightId →
        ∃ value, lookup left leftId = some value ∧ lookup right rightId = some value

def ArgRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    (left right : LCNF.Arg .impure) : Prop :=
  argScoped leftScope left = true ∧
    argScoped rightScope right = true ∧
    (LCNF.AlphaEqv.eqvArg left right).run rho = true

def ArgsRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    (left right : Array (LCNF.Arg .impure)) : Prop :=
  ListRel (ArgRelated rho leftScope rightScope) left.toList right.toList

/-- A fresh binder does not reuse the runtime lookup name of an older scope entry. -/
def FreshForScope (fvarId : FVarId) (scope : List FVarId) : Prop :=
  ∀ oldId, scope.contains oldId = true → fvarId.name ≠ oldId.name

theorem lookup_bind_of_name_ne
    (different : binder.name ≠ fvarId.name) :
    lookup (bind env binder value) fvarId = lookup env fvarId := by
  cases binder with
  | mk binderName =>
      cases fvarId with
      | mk fvarName =>
          simp [Fir.LeanIR.Impure.bind, Fir.LeanIR.Impure.lookup, different]

theorem envsAgree_refl_of_covers
    (covers : EnvCovers scope env) :
    EnvsAgree {} scope scope env env := by
  intro leftId leftScoped rightId rightScoped related
  have ids : leftId = rightId := by
    change (leftId == rightId) = true at related
    cases leftId with
    | mk leftName =>
        cases rightId with
        | mk rightName =>
            congr
            exact eq_of_beq related
  subst rightId
  obtain ⟨value, found⟩ := covers leftId leftScoped
  exact ⟨value, found, found⟩

theorem lookupValue_eq_of_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (leftScoped : leftScope.contains leftId = true)
    (rightScoped : rightScope.contains rightId = true)
    (related : FVarRelated rho leftId rightId) :
    lookupValue leftEnv leftId = lookupValue rightEnv rightId := by
  obtain ⟨value, leftFound, rightFound⟩ :=
    agree leftId leftScoped rightId rightScoped related
  simp [lookupValue, leftFound, rightFound]

/--
Extend related environments with one equal runtime value. The `classify`
hypothesis is the exact syntactic obligation later discharged from
`withFVar`, alpha-equivalence, and declaration-wide hygiene: every related pair
in the extended scopes is either the new binder pair or an old related pair.
-/
theorem envsAgree_bind_of_classified
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (leftFresh : FreshForScope leftId leftScope)
    (rightFresh : FreshForScope rightId rightScope)
    (classify :
      ∀ candidateLeft, (leftId :: leftScope).contains candidateLeft = true →
        ∀ candidateRight, (rightId :: rightScope).contains candidateRight = true →
          FVarRelated extended candidateLeft candidateRight →
            (candidateLeft = leftId ∧ candidateRight = rightId) ∨
              (leftScope.contains candidateLeft = true ∧
                rightScope.contains candidateRight = true ∧
                FVarRelated rho candidateLeft candidateRight)) :
    EnvsAgree extended (leftId :: leftScope) (rightId :: rightScope)
      (bind leftEnv leftId value) (bind rightEnv rightId value) := by
  intro candidateLeft candidateLeftScoped candidateRight candidateRightScoped related
  rcases classify candidateLeft candidateLeftScoped candidateRight candidateRightScoped related with
    newPair | oldPair
  · rcases newPair with ⟨rfl, rfl⟩
    exact ⟨value, lookup_bind_self _ _ _, lookup_bind_self _ _ _⟩
  · rcases oldPair with ⟨leftScoped, rightScoped, oldRelated⟩
    obtain ⟨oldValue, leftFound, rightFound⟩ :=
      agree candidateLeft leftScoped candidateRight rightScoped oldRelated
    refine ⟨oldValue, ?_, ?_⟩
    · rw [lookup_bind_of_name_ne (leftFresh candidateLeft leftScoped)]
      exact leftFound
    · rw [lookup_bind_of_name_ne (rightFresh candidateRight rightScoped)]
      exact rightFound

theorem evalArg_eq_of_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : ArgRelated rho leftScope rightScope leftArg rightArg) :
    evalArg leftEnv leftArg = evalArg rightEnv rightArg := by
  rcases related with ⟨leftScoped, rightScoped, related⟩
  cases leftArg with
  | erased =>
      cases rightArg with
      | erased => rfl
      | fvar _ => simp [LCNF.AlphaEqv.eqvArg] at related
      | type _ impossible => nomatch impossible
  | fvar leftId =>
      cases rightArg with
      | erased => simp [LCNF.AlphaEqv.eqvArg] at related
      | fvar rightId =>
          have values := lookupValue_eq_of_related agree leftScoped rightScoped related
          change lookupValue leftEnv leftId = lookupValue rightEnv rightId
          exact values
      | type _ impossible => nomatch impossible
  | type _ impossible => nomatch impossible

theorem evalArgList_eq_of_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : ListRel (ArgRelated rho leftScope rightScope) left right) :
    left.mapM (evalArg leftEnv) = right.mapM (evalArg rightEnv) := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      simp [evalArg_eq_of_related agree head, ih]

theorem evalArgs_eq_of_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
    evalArgs leftEnv leftArgs = evalArgs rightEnv rightArgs := by
  simp only [evalArgs, Array.mapM_eq_mapM_toList]
  rw [evalArgList_eq_of_related agree related]

end Fir.LeanIR.Passes.AlphaEqv
