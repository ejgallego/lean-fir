import Fir.LeanIR.Passes.AlphaEqv
import Std.Data.TreeMap.Lemmas

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure

/-!
Lean 4.32 does not register comparison laws for `Name.quickCmp`. The local
instances below establish exactly the laws needed to reason about the
`FVarIdMap` used by the compiler's alpha-equivalence pass.
-/

private theorem nameQuickCmpAux_eq_swap : ∀ left right : Name,
    Name.quickCmpAux left right = (Name.quickCmpAux right left).swap := by
  intro left right
  induction left generalizing right with
  | anonymous => cases right <;> simp [Name.quickCmpAux]
  | num p n ih =>
      cases right with
      | anonymous => simp [Name.quickCmpAux]
      | str => simp [Name.quickCmpAux]
      | num q m =>
          simp only [Name.quickCmpAux]
          rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := m) (b := n)]
          cases compare n m <;> simp [ih]
  | str p s ih =>
      cases right with
      | anonymous => simp [Name.quickCmpAux]
      | num => simp [Name.quickCmpAux]
      | str q t =>
          simp only [Name.quickCmpAux]
          rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := t) (b := s)]
          cases compare s t <;> simp [ih]

private theorem nameQuickCmpAux_isLE_trans : ∀ {left middle right : Name},
    (Name.quickCmpAux left middle).isLE →
    (Name.quickCmpAux middle right).isLE →
    (Name.quickCmpAux left right).isLE := by
  intro left middle right leftMiddle middleRight
  induction left generalizing middle right <;>
    cases middle <;> cases right <;> simp_all [Name.quickCmpAux]
  case num.num.num p n ih q m r k =>
    change ((compare n m).then (Name.quickCmpAux p q)).isLE at leftMiddle
    change ((compare m k).then (Name.quickCmpAux q r)).isLE at middleRight
    change ((compare n k).then (Name.quickCmpAux p r)).isLE
    simp only [Ordering.isLE_then_iff_and] at leftMiddle middleRight ⊢
    refine ⟨Std.TransCmp.isLE_trans leftMiddle.1 middleRight.1, ?_⟩
    rcases leftMiddle.2 with valueLt | valueEq
    · exact Or.inl (Std.TransCmp.lt_of_lt_of_isLE valueLt middleRight.1)
    · rcases middleRight.2 with valueLt | valueEq'
      · exact Or.inl (Std.TransCmp.lt_of_isLE_of_lt leftMiddle.1 valueLt)
      · exact Or.inr (ih valueEq valueEq')
  case str.str.str p s ih q t r u =>
    change ((compare s t).then (Name.quickCmpAux p q)).isLE at leftMiddle
    change ((compare t u).then (Name.quickCmpAux q r)).isLE at middleRight
    change ((compare s u).then (Name.quickCmpAux p r)).isLE
    simp only [Ordering.isLE_then_iff_and] at leftMiddle middleRight ⊢
    refine ⟨Std.TransCmp.isLE_trans leftMiddle.1 middleRight.1, ?_⟩
    rcases leftMiddle.2 with valueLt | valueEq
    · exact Or.inl (Std.TransCmp.lt_of_lt_of_isLE valueLt middleRight.1)
    · rcases middleRight.2 with valueLt | valueEq'
      · exact Or.inl (Std.TransCmp.lt_of_isLE_of_lt leftMiddle.1 valueLt)
      · exact Or.inr (ih valueEq valueEq')

local instance : Std.TransCmp Name.quickCmpAux where
  eq_swap := nameQuickCmpAux_eq_swap _ _
  isLE_trans := nameQuickCmpAux_isLE_trans

local instance : Std.TransCmp Name.quickCmp := by
  change Std.TransCmp (compareLex (compareOn Name.hash) Name.quickCmpAux)
  infer_instance

local instance : Std.TransCmp
    (fun (left right : FVarId) => Name.quickCmp left.name right.name) where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := Name.quickCmp)
  isLE_trans := Std.TransCmp.isLE_trans (cmp := Name.quickCmp)

private theorem nameQuickCmpAux_eq_iff : ∀ {left right : Name},
    Name.quickCmpAux left right = .eq ↔ left = right
  | .anonymous, right => by cases right <;> simp [Name.quickCmpAux]
  | left, .anonymous => by cases left <;> simp [Name.quickCmpAux]
  | .num .., .str .. => by simp [Name.quickCmpAux]
  | .str .., .num .. => by simp [Name.quickCmpAux]
  | .num p n, .num q m => by
      simp only [Name.quickCmpAux]
      split <;> simp_all [nameQuickCmpAux_eq_iff]
  | .str p s, .str q t => by
      simp only [Name.quickCmpAux]
      split <;> simp_all [nameQuickCmpAux_eq_iff]

private theorem nameQuickCmp_eq_iff {left right : Name} :
    Name.quickCmp left right = .eq ↔ left = right := by
  constructor
  · unfold Name.quickCmp
    intro compared
    split at compared
    · exact nameQuickCmpAux_eq_iff.mp compared
    · contradiction
  · rintro rfl
    unfold Name.quickCmp
    simp [nameQuickCmpAux_eq_iff]

theorem fvarIdMap_get?_insert (rho : FVarIdMap α) (key query : FVarId) (value : α) :
    (rho.insert key value).get? query =
      if key.name = query.name then some value else rho.get? query := by
  change (Std.TreeMap.insert rho key value)[query]? = _
  rw [Std.TreeMap.getElem?_insert]
  by_cases same : key.name = query.name
  · rw [if_pos (nameQuickCmp_eq_iff.mpr same), if_pos same]
  · rw [if_neg (fun compared => same (nameQuickCmp_eq_iff.mp compared)), if_neg same]
    rfl

private theorem fvar_beq_self (fvarId : FVarId) : (fvarId == fvarId) = true := by
  cases fvarId with
  | mk name =>
      change (name == name) = true
      exact Name.beq_iff_eq.mpr rfl

theorem fvar_eq_of_beq {left right : FVarId}
    (equal : (left == right) = true) : left = right := by
  cases left with
  | mk leftName =>
      cases right with
      | mk rightName =>
          congr
          exact Name.beq_iff_eq.mp equal

theorem fVarRelated_insert_self (rho : FVarIdMap FVarId) (left right : FVarId) :
    FVarRelated (rho.insert right left) left right := by
  change (left == ((rho.insert right left).get? right).getD right) = true
  rw [fvarIdMap_get?_insert]
  simpa using fvar_beq_self left

theorem fVarRelated_insert_of_name_ne
    (rho : FVarIdMap FVarId) (newLeft newRight left right : FVarId)
    (different : newRight.name ≠ right.name) :
    FVarRelated (rho.insert newRight newLeft) left right ↔
      FVarRelated rho left right := by
  change (left == ((rho.insert newRight newLeft).get? right).getD right) = true ↔
    (left == (rho.get? right).getD right) = true
  rw [fvarIdMap_get?_insert]
  simp [different]

theorem left_eq_of_fVarRelated_insert_same
    (rho : FVarIdMap FVarId) (leftId rightId candidateLeft : FVarId)
    (related : FVarRelated (rho.insert rightId leftId) candidateLeft rightId) :
    candidateLeft = leftId := by
  change (candidateLeft ==
    ((rho.insert rightId leftId).get? rightId).getD rightId) = true at related
  rw [fvarIdMap_get?_insert] at related
  simpa using fvar_eq_of_beq related

/-- Every right-hand variable tracked by a renaming maps into the left scope. -/
def RenamingScoped (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) : Prop :=
  ∀ left right, rightScope.contains right = true →
    FVarRelated rho left right → leftScope.contains left = true

theorem renamingScoped_empty (scope : List FVarId) :
    RenamingScoped ({} : FVarIdMap FVarId) scope scope := by
  intro left right rightScoped related
  change (left == right) = true at related
  have equal : left = right := fvar_eq_of_beq related
  simpa [equal] using rightScoped

/--
An inserted binder is the only new related pair. Older right-hand variables
retain their previous relation and, by `RenamingScoped`, still point into the
old left scope.
-/
theorem fVarRelated_insert_classify
    {rho : FVarIdMap FVarId} {leftScope rightScope : List FVarId}
    {leftId rightId candidateLeft candidateRight : FVarId}
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (rightFresh : FreshForScope rightId rightScope)
    (candidateRightScoped : (rightId :: rightScope).contains candidateRight = true)
    (related : FVarRelated (rho.insert rightId leftId) candidateLeft candidateRight) :
    (candidateLeft = leftId ∧ candidateRight = rightId) ∨
      (leftScope.contains candidateLeft = true ∧
        rightScope.contains candidateRight = true ∧
        FVarRelated rho candidateLeft candidateRight) := by
  simp only [List.contains_cons, Bool.or_eq_true] at candidateRightScoped
  rcases candidateRightScoped with newRight | oldRight
  · have rightEq : candidateRight = rightId := fvar_eq_of_beq newRight
    subst candidateRight
    exact Or.inl ⟨left_eq_of_fVarRelated_insert_same
      rho leftId rightId candidateLeft related, rfl⟩
  · have different := rightFresh candidateRight oldRight
    have oldRelated := (fVarRelated_insert_of_name_ne
      rho leftId rightId candidateLeft candidateRight different).mp related
    exact Or.inr ⟨renamingScoped candidateLeft candidateRight oldRight oldRelated,
      oldRight, oldRelated⟩

theorem renamingScoped_insert
    {rho : FVarIdMap FVarId} {leftScope rightScope : List FVarId}
    {leftId rightId : FVarId}
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (rightFresh : FreshForScope rightId rightScope) :
    RenamingScoped (rho.insert rightId leftId)
      (leftId :: leftScope) (rightId :: rightScope) := by
  intro candidateLeft candidateRight candidateRightScoped related
  rcases fVarRelated_insert_classify renamingScoped rightFresh
      candidateRightScoped related with newPair | oldPair
  · rcases newPair with ⟨rfl, rfl⟩
    simp only [List.contains_cons, Bool.or_eq_true]
    exact Or.inl (fvar_beq_self candidateLeft)
  · simp only [List.contains_cons, Bool.or_eq_true]
    exact Or.inr oldPair.1

/--
Inserting a binder whose right-hand name is fresh for a scope preserves every
renaming already visible in that scope. Unlike `renamingScoped_insert`, this
lemma does not add the binder to the indexed scope; join installation uses it
to preserve the independent variable-scope invariant, and variable binding
uses it to preserve the independent join-scope invariant.
-/
theorem renamingScoped_insert_preserve
    {rho : FVarIdMap FVarId} {leftScope rightScope : List FVarId}
    {leftId rightId : FVarId}
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (rightFresh : FreshForScope rightId rightScope) :
    RenamingScoped (rho.insert rightId leftId) leftScope rightScope := by
  intro candidateLeft candidateRight candidateRightScoped related
  have different := rightFresh candidateRight candidateRightScoped
  have oldRelated := (fVarRelated_insert_of_name_ne
    rho leftId rightId candidateLeft candidateRight different).mp related
  exact renamingScoped candidateLeft candidateRight candidateRightScoped oldRelated

/-- A fresh insertion preserves environment agreement on an unchanged scope. -/
theorem envsAgree_insert_preserve
    {rho : FVarIdMap FVarId} {leftScope rightScope : List FVarId}
    {leftId rightId : FVarId}
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (rightFresh : FreshForScope rightId rightScope) :
    EnvsAgree (rho.insert rightId leftId) leftScope rightScope leftEnv rightEnv := by
  intro candidateLeft candidateLeftScoped candidateRight candidateRightScoped related
  have different := rightFresh candidateRight candidateRightScoped
  have oldRelated := (fVarRelated_insert_of_name_ne
    rho leftId rightId candidateLeft candidateRight different).mp related
  exact agree candidateLeft candidateLeftScoped candidateRight candidateRightScoped oldRelated

theorem withFVar_run (rho : FVarIdMap FVarId) (left right : FVarId)
    (x : LCNF.AlphaEqv.EqvM α) :
    (LCNF.AlphaEqv.withFVar left right x).run rho =
      x.run (rho.insert right left) := by
  rfl

/--
The environment agreement invariant follows the compiler's concrete
`withFVar` update once the renaming is known to stay within its scopes.
-/
theorem envsAgree_bind
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (leftFresh : FreshForScope leftId leftScope)
    (rightFresh : FreshForScope rightId rightScope) :
    EnvsAgree (rho.insert rightId leftId) (leftId :: leftScope) (rightId :: rightScope)
      (bind leftEnv leftId value) (bind rightEnv rightId value) := by
  apply envsAgree_bind_of_classified agree leftFresh rightFresh
  intro candidateLeft _ candidateRight candidateRightScoped related
  exact fVarRelated_insert_classify
    renamingScoped rightFresh candidateRightScoped related

end Fir.LeanIR.Passes.AlphaEqv
