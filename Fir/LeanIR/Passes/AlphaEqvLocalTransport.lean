import Fir.LeanIR.Passes.AlphaEqvLocalSound

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler

/-!
The upstream `Code.alphaEqv` entry point always starts from the empty reader
map, while recursive simpCase proofs compare branch bodies beneath unchanged
outer binders.  This module isolates the axiom-free transport needed between
those two presentations.  Two reader maps are observationally equivalent when
their totalized right-to-left lookup agrees; alpha comparison can observe no
other property of a map.
-/

/-- Extensional equality of the totalized lookup observed by `eqvFVar`. -/
def ResolverEquivalent (left right : FVarIdMap FVarId) : Prop :=
  ∀ fvarId, (left.get? fvarId).getD fvarId =
    (right.get? fvarId).getD fvarId

theorem resolverEquivalent_refl (rho : FVarIdMap FVarId) :
    ResolverEquivalent rho rho := by
  intro fvarId
  rfl

theorem ResolverEquivalent.symm
    (equivalent : ResolverEquivalent left right) :
    ResolverEquivalent right left := by
  intro fvarId
  exact (equivalent fvarId).symm

theorem ResolverEquivalent.trans
    (leftMiddle : ResolverEquivalent left middle)
    (middleRight : ResolverEquivalent middle right) :
    ResolverEquivalent left right := by
  intro fvarId
  exact (leftMiddle fvarId).trans (middleRight fvarId)

/-- Applying the same binder update preserves observational map equality. -/
theorem ResolverEquivalent.insert
    (equivalent : ResolverEquivalent left right)
    (binderLeft binderRight : FVarId) :
    ResolverEquivalent
      (left.insert binderRight binderLeft)
      (right.insert binderRight binderLeft) := by
  intro fvarId
  by_cases same : binderRight.name = fvarId.name
  · rw [fvarIdMap_get?_insert, fvarIdMap_get?_insert,
      if_pos same, if_pos same]
  · rw [fvarIdMap_get?_insert, fvarIdMap_get?_insert,
      if_neg same, if_neg same]
    exact equivalent fvarId

theorem eqvFVar_run_congr
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : FVarId) :
    (LCNF.AlphaEqv.eqvFVar left right).run leftMap =
      (LCNF.AlphaEqv.eqvFVar left right).run rightMap := by
  change (left == (leftMap.get? right).getD right) =
    (left == (rightMap.get? right).getD right)
  rw [equivalent right]

private theorem readerAndM_run_congr
    {left right : ReaderM (FVarIdMap FVarId) Bool}
    {leftMap rightMap : FVarIdMap FVarId}
    (leftEq : left.run leftMap = left.run rightMap)
    (rightEq : right.run leftMap = right.run rightMap) :
    (left <&&> right).run leftMap = (left <&&> right).run rightMap := by
  change left leftMap = left rightMap at leftEq
  change right leftMap = right rightMap at rightEq
  unfold andM
  simp only [ReaderT.run, ReaderT.bind, Bind.bind, Pure.pure]
  rw [leftEq]
  cases value : left rightMap <;>
    simp [ToBool.toBool, ReaderT.pure, rightEq]

theorem eqvType_run_congr
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : Expr) :
    (LCNF.AlphaEqv.eqvType left right).run leftMap =
      (LCNF.AlphaEqv.eqvType left right).run rightMap := by
  induction left generalizing right with
  | app leftFn leftArg fnIH argIH =>
      cases right with
      | app rightFn rightArg =>
          exact readerAndM_run_congr (argIH rightArg) (fnIH rightFn)
      | _ => rfl
  | fvar leftId =>
      cases right with
      | fvar rightId => exact eqvFVar_run_congr equivalent leftId rightId
      | _ => rfl
  | forallE name domain body binderInfo domainIH bodyIH =>
      cases right with
      | forallE rightName rightDomain rightBody rightBinderInfo =>
          exact readerAndM_run_congr
            (domainIH rightDomain) (bodyIH rightBody)
      | _ => rfl
  | _ =>
      cases right <;> rfl

theorem eqvArg_run_congr
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : LCNF.Arg pu) :
    (LCNF.AlphaEqv.eqvArg left right).run leftMap =
      (LCNF.AlphaEqv.eqvArg left right).run rightMap := by
  cases left <;> cases right <;> simp only [LCNF.AlphaEqv.eqvArg]
  all_goals first
    | exact eqvType_run_congr equivalent _ _
    | exact eqvFVar_run_congr equivalent _ _
    | rfl

private theorem argCheckListRelated_of_resolverEquivalent
    (equivalent : ResolverEquivalent leftMap rightMap)
    {left right : List (LCNF.Arg .impure)}
    (related : ListRel (ArgCheckRelated leftMap) left right) :
    ListRel (ArgCheckRelated rightMap) left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      apply ListRel.cons _ ih
      unfold ArgCheckRelated at head ⊢
      rw [← eqvArg_run_congr equivalent]
      exact head

theorem eqvArgs_run_congr
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : Array (LCNF.Arg .impure)) :
    (LCNF.AlphaEqv.eqvArgs left right).run leftMap =
      (LCNF.AlphaEqv.eqvArgs left right).run rightMap := by
  have forward :
      (LCNF.AlphaEqv.eqvArgs left right).run leftMap = true →
      (LCNF.AlphaEqv.eqvArgs left right).run rightMap = true := by
    intro accepted
    have related := eqvArgs_sound accepted
    apply eqvArgs_true_of_checks
    exact argCheckListRelated_of_resolverEquivalent equivalent related
  have backward :
      (LCNF.AlphaEqv.eqvArgs left right).run rightMap = true →
      (LCNF.AlphaEqv.eqvArgs left right).run leftMap = true := by
    intro accepted
    have related := eqvArgs_sound accepted
    apply eqvArgs_true_of_checks
    exact argCheckListRelated_of_resolverEquivalent equivalent.symm related
  cases leftResult : (LCNF.AlphaEqv.eqvArgs left right).run leftMap <;>
    cases rightResult : (LCNF.AlphaEqv.eqvArgs left right).run rightMap <;>
    simp_all

theorem eqvLetValue_run_congr
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : LCNF.LetValue .impure) :
    (LCNF.AlphaEqv.eqvLetValue left right).run leftMap =
      (LCNF.AlphaEqv.eqvLetValue left right).run rightMap := by
  cases left <;> cases right <;>
    simp only [LCNF.AlphaEqv.eqvLetValue]
  all_goals first
    | rfl
    | exact readerAndM_run_congr rfl
        (eqvFVar_run_congr equivalent _ _)
    | exact readerAndM_run_congr rfl
        (eqvArgs_run_congr equivalent _ _)
    | exact readerAndM_run_congr
        (eqvFVar_run_congr equivalent _ _)
        (eqvArgs_run_congr equivalent _ _)
    | exact readerAndM_run_congr
        rfl
        (readerAndM_run_congr
          (eqvFVar_run_congr equivalent _ _)
          (eqvArgs_run_congr equivalent _ _))
    | exact readerAndM_run_congr
        (eqvType_run_congr equivalent _ _)
        (eqvFVar_run_congr equivalent _ _)
    | exact eqvFVar_run_congr equivalent _ _

theorem withParamListsUsing_run_congr
    {recurse : Local.EqvM Bool}
    (recurseCongr : ∀ {leftMap rightMap},
      ResolverEquivalent leftMap rightMap →
      recurse.run leftMap = recurse.run rightMap)
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : List (LCNF.Param .impure)) :
    (Local.withParamListsUsing recurse left right).run leftMap =
      (Local.withParamListsUsing recurse left right).run rightMap := by
  induction left generalizing right leftMap rightMap with
  | nil =>
      cases right with
      | nil => exact recurseCongr equivalent
      | cons _ _ => rfl
  | cons leftParam leftRest ih =>
      cases right with
      | nil => rfl
      | cons rightParam rightRest =>
          simp only [Local.withParamListsUsing]
          apply readerAndM_run_congr
          · exact eqvType_run_congr equivalent _ _
          · rw [withFVar_run, withFVar_run]
            exact ih
              (equivalent.insert leftParam.fvarId rightParam.fvarId) rightRest

theorem withParamsUsing_run_congr
    {recurse : Local.EqvM Bool}
    (recurseCongr : ∀ {leftMap rightMap},
      ResolverEquivalent leftMap rightMap →
      recurse.run leftMap = recurse.run rightMap)
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : Array (LCNF.Param .impure)) :
    (Local.withParamsUsing left right recurse).run leftMap =
      (Local.withParamsUsing left right recurse).run rightMap := by
  exact withParamListsUsing_run_congr recurseCongr equivalent _ _

theorem eqvAltListsUsing_run_congr
    {recurse : LCNF.Code .impure → LCNF.Code .impure → Local.EqvM Bool}
    (recurseCongr : ∀ left right {leftMap rightMap},
      ResolverEquivalent leftMap rightMap →
      (recurse left right).run leftMap = (recurse left right).run rightMap)
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : List (LCNF.Alt .impure)) :
    (Local.eqvAltListsUsing recurse left right).run leftMap =
      (Local.eqvAltListsUsing recurse left right).run rightMap := by
  induction left generalizing right leftMap rightMap with
  | nil => cases right <;> rfl
  | cons leftAlt leftRest ih =>
      cases right with
      | nil => rfl
      | cons rightAlt rightRest =>
          cases leftAlt with
          | alt _ _ _ impossible => contradiction
          | ctorAlt leftInfo leftCode _ =>
              cases rightAlt with
              | alt _ _ _ impossible => contradiction
              | ctorAlt rightInfo rightCode _ =>
                  simp only [Local.eqvAltListsUsing]
                  exact readerAndM_run_congr rfl
                    (readerAndM_run_congr
                      (recurseCongr leftCode rightCode equivalent)
                      (ih equivalent rightRest))
              | default _ => rfl
          | default leftCode =>
              cases rightAlt with
              | alt _ _ _ impossible => contradiction
              | ctorAlt _ _ _ => rfl
              | default rightCode =>
                  simp only [Local.eqvAltListsUsing]
                  exact readerAndM_run_congr
                    (recurseCongr leftCode rightCode equivalent)
                    (ih equivalent rightRest)

theorem eqvAltsUsing_run_congr
    {recurse : LCNF.Code .impure → LCNF.Code .impure → Local.EqvM Bool}
    (recurseCongr : ∀ left right {leftMap rightMap},
      ResolverEquivalent leftMap rightMap →
      (recurse left right).run leftMap = (recurse left right).run rightMap)
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : Array (LCNF.Alt .impure)) :
    (Local.eqvAltsUsing recurse left right).run leftMap =
      (Local.eqvAltsUsing recurse left right).run rightMap := by
  simp only [Local.eqvAltsUsing]
  split
  · exact eqvAltListsUsing_run_congr recurseCongr equivalent _ _
  · rfl

private theorem withFVar_run_congr_of_insert
    {body : Local.EqvM Bool}
    (bodyEq :
      body.run (leftMap.insert rightId leftId) =
        body.run (rightMap.insert rightId leftId)) :
    (LCNF.AlphaEqv.withFVar leftId rightId body).run leftMap =
      (LCNF.AlphaEqv.withFVar leftId rightId body).run rightMap := by
  simpa only [withFVar_run] using bodyEq

set_option maxHeartbeats 800000 in
theorem localEqv_run_congr
    (equivalent : ResolverEquivalent leftMap rightMap)
    (fuel : Nat) (left right : LCNF.Code .impure) :
    (Local.eqv fuel left right).run leftMap =
      (Local.eqv fuel left right).run rightMap := by
  induction fuel generalizing left right leftMap rightMap with
  | zero => rfl
  | succ fuel ih =>
      have recurseCongr : ∀ (left right : LCNF.Code .impure)
          {leftMap rightMap},
          ResolverEquivalent leftMap rightMap →
          (Local.eqv fuel left right).run leftMap =
            (Local.eqv fuel left right).run rightMap := by
        intro left right leftMap rightMap equivalent
        exact ih equivalent left right
      cases left <;> cases right <;> simp only [Local.eqv]
      all_goals first
        | rfl
        | contradiction
        | exact readerAndM_run_congr
            (eqvType_run_congr equivalent _ _)
            (readerAndM_run_congr
              (eqvLetValue_run_congr equivalent _ _)
              (withFVar_run_congr_of_insert
                (recurseCongr _ _
                  (equivalent.insert _ _))))
        | exact readerAndM_run_congr
            (eqvType_run_congr equivalent _ _)
            (readerAndM_run_congr
              (withParamsUsing_run_congr
                (fun equivalent => recurseCongr _ _ equivalent)
                equivalent _ _)
              (withFVar_run_congr_of_insert
                (recurseCongr _ _
                  (equivalent.insert _ _))))
        | exact readerAndM_run_congr
            (eqvFVar_run_congr equivalent _ _)
            (eqvArgs_run_congr equivalent _ _)
        | exact readerAndM_run_congr
            (eqvFVar_run_congr equivalent _ _)
            (readerAndM_run_congr
              (eqvType_run_congr equivalent _ _)
              (eqvAltsUsing_run_congr
                recurseCongr
                equivalent _ _))
        | exact readerAndM_run_congr rfl
            (readerAndM_run_congr
              (eqvFVar_run_congr equivalent _ _)
              (readerAndM_run_congr
                (eqvArg_run_congr equivalent _ _)
                (recurseCongr _ _ equivalent)))
        | exact readerAndM_run_congr rfl
            (readerAndM_run_congr
              (eqvFVar_run_congr equivalent _ _)
              (readerAndM_run_congr
                (eqvFVar_run_congr equivalent _ _)
                (recurseCongr _ _ equivalent)))
        | exact readerAndM_run_congr rfl
            (readerAndM_run_congr rfl
              (readerAndM_run_congr
                (eqvFVar_run_congr equivalent _ _)
                (readerAndM_run_congr
                  (eqvFVar_run_congr equivalent _ _)
                  (readerAndM_run_congr
                    (eqvType_run_congr equivalent _ _)
                    (recurseCongr _ _ equivalent)))))
        | exact readerAndM_run_congr rfl
            (readerAndM_run_congr
              (eqvFVar_run_congr equivalent _ _)
              (recurseCongr _ _ equivalent))
        | exact readerAndM_run_congr rfl
            (readerAndM_run_congr rfl
              (readerAndM_run_congr rfl
                (readerAndM_run_congr
                  (eqvFVar_run_congr equivalent _ _)
                  (recurseCongr _ _ equivalent))))
        | exact readerAndM_run_congr rfl
            (readerAndM_run_congr rfl
              (readerAndM_run_congr rfl
                (readerAndM_run_congr rfl
                  (readerAndM_run_congr
                    (eqvFVar_run_congr equivalent _ _)
                    (recurseCongr _ _ equivalent)))))
        | exact readerAndM_run_congr
            (eqvFVar_run_congr equivalent _ _)
            (recurseCongr _ _ equivalent)
        | exact eqvType_run_congr equivalent _ _
        | exact eqvFVar_run_congr equivalent _ _

theorem localCheckAt_eq_of_resolverEquivalent
    (equivalent : ResolverEquivalent leftMap rightMap)
    (fuel : Nat) (left right : LCNF.Code .impure) :
    Local.checkAt fuel leftMap left right =
      Local.checkAt fuel rightMap left right := by
  exact localEqv_run_congr equivalent fuel left right

theorem localAcceptsAt_iff_of_resolverEquivalent
    (equivalent : ResolverEquivalent leftMap rightMap)
    (left right : LCNF.Code .impure) :
    Local.AcceptsAt leftMap left right ↔
      Local.AcceptsAt rightMap left right := by
  constructor
  · rintro ⟨fuel, accepted⟩
    exact ⟨fuel,
      (localCheckAt_eq_of_resolverEquivalent equivalent fuel left right) ▸
        accepted⟩
  · rintro ⟨fuel, accepted⟩
    exact ⟨fuel,
      (localCheckAt_eq_of_resolverEquivalent equivalent.symm fuel left right) ▸
        accepted⟩

/--
Transport top-level acceptance from Lean's empty initial resolver to an
observationally empty local resolver. This is the bridge recursive simpCase
proofs need beneath hygienic binders.
-/
theorem localAcceptsAt_of_resolverEquivalent_empty
    (equivalent : ResolverEquivalent rho {})
    (left right : LCNF.Code .impure)
    (accepted : Local.Accepts left right) :
    Local.AcceptsAt rho left right :=
  (localAcceptsAt_iff_of_resolverEquivalent equivalent left right).mpr accepted

end Fir.LeanIR.Passes.AlphaEqv
