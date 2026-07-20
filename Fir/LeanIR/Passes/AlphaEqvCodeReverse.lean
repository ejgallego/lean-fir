import Fir.LeanIR.Passes.AlphaEqvLocalTransport

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure

/-!
Bidirectional renaming invariants for reversing the declarative impure-code
relation.  The forward and backward maps are paired explicitly because a
single `FVarIdMap` is directional once alpha-renamed binders are inserted.
-/

/-- The two directional maps are scoped and mutually inverse on the variables
visible at one recursive code position. -/
structure RenamingBijection
    (forward backward : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) : Prop where
  forwardScoped : RenamingScoped forward leftScope rightScope
  backwardScoped : RenamingScoped backward rightScope leftScope
  inverse : ∀ left right,
    leftScope.contains left = true →
    rightScope.contains right = true →
    (FVarRelated forward left right ↔
      FVarRelated backward right left)

private theorem fVarRelated_iff_eq_of_resolverEquivalent_empty
    (empty : ResolverEquivalent rho {}) (left right : FVarId) :
    FVarRelated rho left right ↔ left = right := by
  constructor
  · intro related
    change (left == (rho.get? right).getD right) = true at related
    rw [empty right, emptyResolver_getD] at related
    exact fvar_eq_of_beq related
  · rintro rfl
    change (left == (rho.get? left).getD left) = true
    rw [empty left, emptyResolver_getD]
    cases left with
    | mk name =>
        change (name == name) = true
        exact Name.beq_iff_eq.mpr rfl

/-- Observationally empty maps form a bijection between identical scopes. -/
theorem RenamingBijection.of_resolverEquivalent_empty
    (forwardEmpty : ResolverEquivalent forward {})
    (backwardEmpty : ResolverEquivalent backward {})
    (scopesEq : leftScope = rightScope) :
    RenamingBijection forward backward leftScope rightScope := by
  subst rightScope
  refine {
    forwardScoped := ?_
    backwardScoped := ?_
    inverse := ?_
  }
  · intro left right rightScoped related
    have equal :=
      (fVarRelated_iff_eq_of_resolverEquivalent_empty
        forwardEmpty left right).mp related
    simpa [equal] using rightScoped
  · intro right left leftScoped related
    have equal :=
      (fVarRelated_iff_eq_of_resolverEquivalent_empty
        backwardEmpty right left).mp related
    simpa [equal] using leftScoped
  · intro left right _ _
    rw [fVarRelated_iff_eq_of_resolverEquivalent_empty forwardEmpty,
      fVarRelated_iff_eq_of_resolverEquivalent_empty backwardEmpty,
      eq_comm]

theorem RenamingBijection.symm
    (bijection : RenamingBijection forward backward leftScope rightScope) :
    RenamingBijection backward forward rightScope leftScope := {
  forwardScoped := bijection.backwardScoped
  backwardScoped := bijection.forwardScoped
  inverse := fun right left rightScoped leftScoped =>
    (bijection.inverse left right leftScoped rightScoped).symm
}

/-- Opposite binder insertions preserve the scoped inverse relation when both
new binders are fresh. -/
theorem RenamingBijection.insert
    (bijection : RenamingBijection forward backward leftScope rightScope)
    (leftFresh : FreshForScope leftId leftScope)
    (rightFresh : FreshForScope rightId rightScope) :
    RenamingBijection
      (forward.insert rightId leftId) (backward.insert leftId rightId)
      (leftId :: leftScope) (rightId :: rightScope) := by
  refine {
    forwardScoped := renamingScoped_insert
      bijection.forwardScoped rightFresh
    backwardScoped := renamingScoped_insert
      bijection.backwardScoped leftFresh
    inverse := ?_
  }
  intro left right leftScoped rightScoped
  constructor
  · intro related
    rcases fVarRelated_insert_classify bijection.forwardScoped rightFresh
        rightScoped related with newPair | oldPair
    · rcases newPair with ⟨leftEq, rightEq⟩
      subst left
      subst right
      exact fVarRelated_insert_self backward rightId leftId
    · exact (fVarRelated_insert_of_name_ne
        backward rightId leftId right left
        (leftFresh left oldPair.1)).mpr
        ((bijection.inverse left right oldPair.1 oldPair.2.1).mp oldPair.2.2)
  · intro related
    rcases fVarRelated_insert_classify bijection.backwardScoped leftFresh
        leftScoped related with newPair | oldPair
    · rcases newPair with ⟨rightEq, leftEq⟩
      subst right
      subst left
      exact fVarRelated_insert_self forward leftId rightId
    · exact (fVarRelated_insert_of_name_ne
        forward leftId rightId left right
        (rightFresh right oldPair.1)).mpr
        ((bijection.inverse left right oldPair.2.1 oldPair.1).mpr oldPair.2.2)

/-- A binder fresh for unchanged scopes may update both maps without adding a
visible variable to either side. This is used when variable binders preserve
join scopes and join binders preserve variable scopes. -/
theorem RenamingBijection.insertPreserve
    (bijection : RenamingBijection forward backward leftScope rightScope)
    (leftFresh : FreshForScope leftId leftScope)
    (rightFresh : FreshForScope rightId rightScope) :
    RenamingBijection
      (forward.insert rightId leftId) (backward.insert leftId rightId)
      leftScope rightScope := by
  refine {
    forwardScoped := renamingScoped_insert_preserve
      bijection.forwardScoped rightFresh
    backwardScoped := renamingScoped_insert_preserve
      bijection.backwardScoped leftFresh
    inverse := ?_
  }
  intro left right leftScoped rightScoped
  rw [fVarRelated_insert_of_name_ne forward leftId rightId left right
      (rightFresh right rightScoped),
    fVarRelated_insert_of_name_ne backward rightId leftId right left
      (leftFresh left leftScoped)]
  exact bijection.inverse left right leftScoped rightScoped

theorem RenamingBijection.fVarRelated_symm
    (bijection : RenamingBijection forward backward leftScope rightScope)
    (leftScoped : leftScope.contains left = true)
    (rightScoped : rightScope.contains right = true)
    (related : FVarRelated forward left right) :
    FVarRelated backward right left :=
  (bijection.inverse left right leftScoped rightScoped).mp related

theorem RenamingBijection.scopedFVarRelated_symm
    (bijection : RenamingBijection forward backward leftScope rightScope)
    (related : ScopedFVarRelated forward leftScope rightScope left right) :
    ScopedFVarRelated backward rightScope leftScope right left :=
  ⟨related.2.1, related.1,
    bijection.fVarRelated_symm related.1 related.2.1 related.2.2⟩

theorem RenamingBijection.argRelated_symm
    (bijection : RenamingBijection forward backward leftScope rightScope)
    (related : ArgRelated forward leftScope rightScope left right) :
    ArgRelated backward rightScope leftScope right left := by
  rcases related with ⟨leftScoped, rightScoped, related⟩
  refine ⟨rightScoped, leftScoped, ?_⟩
  cases left with
  | erased =>
      cases right with
      | erased => rfl
      | fvar rightId =>
          simp [LCNF.AlphaEqv.eqvArg] at related
      | type _ impossible => nomatch impossible
  | fvar leftId =>
      cases right with
      | erased =>
          simp [LCNF.AlphaEqv.eqvArg] at related
      | fvar rightId =>
          change leftScope.contains leftId = true at leftScoped
          change rightScope.contains rightId = true at rightScoped
          change FVarRelated forward leftId rightId at related
          change FVarRelated backward rightId leftId
          exact bijection.fVarRelated_symm leftScoped rightScoped related
      | type _ impossible => nomatch impossible
  | type _ impossible => nomatch impossible

theorem RenamingBijection.argsRelated_symm
    (bijection : RenamingBijection forward backward leftScope rightScope)
    (related : ArgsRelated forward leftScope rightScope left right) :
    ArgsRelated backward rightScope leftScope right left := by
  let rec go {left right : List (LCNF.Arg .impure)}
      (related : ListRel (ArgRelated forward leftScope rightScope) left right) :
      ListRel (ArgRelated backward rightScope leftScope) right left :=
    match related with
    | .nil => .nil
    | .cons head tail => .cons (bijection.argRelated_symm head) (go tail)
  exact go related

theorem RenamingBijection.letValueRelated_symm
    (bijection : RenamingBijection forward backward leftScope rightScope)
    (related : LetValueRelated forward leftScope rightScope left right) :
    LetValueRelated backward rightScope leftScope right left := by
  induction related with
  | lit value => exact .lit value
  | erased => exact .erased
  | fvar related args =>
      exact .fvar (bijection.scopedFVarRelated_symm related)
        (bijection.argsRelated_symm args)
  | ctor args => exact .ctor (bijection.argsRelated_symm args)
  | oproj related => exact .oproj (bijection.scopedFVarRelated_symm related)
  | uproj related => exact .uproj (bijection.scopedFVarRelated_symm related)
  | sproj related => exact .sproj (bijection.scopedFVarRelated_symm related)
  | fap args => exact .fap (bijection.argsRelated_symm args)
  | pap args => exact .pap (bijection.argsRelated_symm args)
  | reset related => exact .reset (bijection.scopedFVarRelated_symm related)
  | reuse related args =>
      exact .reuse (bijection.scopedFVarRelated_symm related)
        (bijection.argsRelated_symm args)
  | box related => exact .box (bijection.scopedFVarRelated_symm related)
  | unbox related => exact .unbox (bijection.scopedFVarRelated_symm related)
  | isShared related =>
      exact .isShared (bijection.scopedFVarRelated_symm related)

theorem RenamingBijection.letDeclValueRelated_symm
    (bijection : RenamingBijection forward backward leftScope rightScope)
    (related : LetDeclValueRelated forward leftScope rightScope left right) :
    LetDeclValueRelated backward rightScope leftScope right left :=
  ⟨related.type_eq.symm, bijection.letValueRelated_symm related.value⟩

mutual

  /-- Reverse the declarative code relation using paired inverse renamings for
  the ordinary-variable and join namespaces. -/
  theorem codeRelated_symm
      (variables : RenamingBijection forward backward leftScope rightScope)
      (joins : RenamingBijection forward backward leftJoins rightJoins)
      (related : CodeRelated
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        forward leftScope rightScope left right) :
      CodeRelated
        (leftJoins := rightJoins) (rightJoins := leftJoins)
        backward rightScope leftScope right left :=
    match related with
    | .terminal terminal =>
        match terminal with
        | .ret related =>
            .terminal (.ret (variables.scopedFVarRelated_symm related))
        | .unreachable => .terminal .unreachable
    | .letE declaration leftFresh rightFresh leftJoinFresh rightJoinFresh
        continuation =>
        .letE (variables.letDeclValueRelated_symm declaration)
          rightFresh leftFresh rightJoinFresh leftJoinFresh
          (codeRelated_symm
            (variables.insert leftFresh rightFresh)
            (joins.insertPreserve leftJoinFresh rightJoinFresh)
            continuation)
    | .jp leftFresh rightFresh body continuation =>
        .jp rightFresh leftFresh
          (paramBodyRelated_symm variables joins body)
          (codeRelated_symm
            (variables.insertPreserve
              leftFresh.variables rightFresh.variables)
            (joins.insert leftFresh.joins rightFresh.joins)
            continuation)
    | .jmp target args =>
        .jmp (joins.scopedFVarRelated_symm target)
          (variables.argsRelated_symm args)
    | .cases discr selected =>
        .cases (variables.scopedFVarRelated_symm discr) (fun tag =>
          caseSelectionRelated_symm variables joins (selected tag))
    | .oset object field continuation =>
        .oset (variables.scopedFVarRelated_symm object)
          (variables.argRelated_symm field)
          (codeRelated_symm variables joins continuation)
    | .uset object field continuation =>
        .uset (variables.scopedFVarRelated_symm object)
          (variables.scopedFVarRelated_symm field)
          (codeRelated_symm variables joins continuation)
    | .sset object field continuation =>
        .sset (variables.scopedFVarRelated_symm object)
          (variables.scopedFVarRelated_symm field)
          (codeRelated_symm variables joins continuation)
    | .setTag object continuation =>
        .setTag (variables.scopedFVarRelated_symm object)
          (codeRelated_symm variables joins continuation)
    | .inc object continuation =>
        .inc (variables.scopedFVarRelated_symm object)
          (codeRelated_symm variables joins continuation)
    | .dec object continuation =>
        .dec (variables.scopedFVarRelated_symm object)
          (codeRelated_symm variables joins continuation)
    | .del object continuation =>
        .del (variables.scopedFVarRelated_symm object)
          (codeRelated_symm variables joins continuation)

  /-- Reverse a join/function body while extending the paired maps in the same
  left-to-right parameter order as the checker. -/
  theorem paramBodyRelated_symm
      (variables : RenamingBijection forward backward leftScope rightScope)
      (joins : RenamingBijection forward backward leftJoins rightJoins)
      (related : ParamBodyRelated
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        forward leftScope rightScope leftParams rightParams left right) :
      ParamBodyRelated
        (leftJoins := rightJoins) (rightJoins := leftJoins)
        backward rightScope leftScope rightParams leftParams right left :=
    match related with
    | .nil body => .nil (codeRelated_symm variables joins body)
    | .cons leftFresh rightFresh leftJoinFresh rightJoinFresh rest =>
        .cons rightFresh leftFresh rightJoinFresh leftJoinFresh
          (paramBodyRelated_symm
            (variables.insert leftFresh rightFresh)
            (joins.insertPreserve leftJoinFresh rightJoinFresh)
            rest)

  theorem caseSelectionRelated_symm
      (variables : RenamingBijection forward backward leftScope rightScope)
      (joins : RenamingBijection forward backward leftJoins rightJoins)
      (related : CaseSelectionRelated
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        forward leftScope rightScope left right) :
      CaseSelectionRelated
        (leftJoins := rightJoins) (rightJoins := leftJoins)
        backward rightScope leftScope right left :=
    match related with
    | .none => .none
    | .some code => .some (codeRelated_symm variables joins code)

end

end Fir.LeanIR.Passes.AlphaEqv
