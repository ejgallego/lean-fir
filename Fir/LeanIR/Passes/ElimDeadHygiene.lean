import Fir.LeanIR.Passes.ElimDeadLiveness
import Fir.LeanIR.Passes.SimpCaseWellFormed

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.ImpureHygiene
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.SimpCaseScopedBridge
open Fir.LeanIR.Passes.SimpCaseWellFormed

/-!
Proof-facing hygiene consequences for `elimDeadVars`.

The backwards traversal can enlarge one subtree's liveness set with facts
collected from a lexically disjoint subtree.  Local scoping proves that such
facts are references to in-scope identifiers; declaration-wide binder
ownership proves that they cannot name a binder owned by the other subtree.
This module keeps those two obligations explicit.
-/

/-- Every parameter binder has a runtime name different from `forbidden`. -/
def ParamBindersAvoidName (forbidden : FVarId)
    (params : List (LCNF.Param .impure)) : Prop :=
  ∀ param, param ∈ params → forbidden.name ≠ param.fvarId.name

/-- Structural negative ownership certificate for every binder in a code
tree.  Runtime references are intentionally absent; they are supplied by the
separate scoped well-formedness tree. -/
inductive CodeBindersAvoidName (forbidden : FVarId) :
    LCNF.Code .impure → Prop where
  | letE
      (binder : forbidden.name ≠ declaration.fvarId.name)
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.let declaration continuation)
  | join
      (binder : forbidden.name ≠ declaration.fvarId.name)
      (params : ParamBindersAvoidName forbidden declaration.params.toList)
      (bodyAvoids : CodeBindersAvoidName forbidden declaration.value)
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.jp declaration continuation)
  | cases
      (alternatives : ∀ alternative,
        alternative ∈ caseInfo.alts.toList →
          CodeBindersAvoidName forbidden alternative.getCode) :
      CodeBindersAvoidName forbidden (.cases caseInfo)
  | jump : CodeBindersAvoidName forbidden (.jmp target arguments)
  | ret : CodeBindersAvoidName forbidden (.return result)
  | unreachable : CodeBindersAvoidName forbidden (.unreach type)
  | objectSet
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.oset object index field continuation)
  | usizeSet
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.uset object index field continuation)
  | scalarSet
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden
        (.sset object width offset field type continuation)
  | tagSet
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.setTag object tag continuation)
  | increment
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden
        (.inc object amount check persistent continuation)
  | decrement
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden
        (.dec object amount check persistent objects continuation)
  | delete
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.del object continuation)

theorem fvarId_ne_of_freshForScope
    (fresh : FreshForScope forbidden scope)
    (inScope : scope.contains candidate = true) :
    candidate ≠ forbidden := by
  intro same
  subst candidate
  exact (fresh forbidden inScope) rfl

theorem freshForScope_cons
    (fresh : FreshForScope forbidden scope)
    (binder : forbidden.name ≠ inserted.name) :
    FreshForScope forbidden (inserted :: scope) := by
  intro old inScope
  simp only [List.contains_cons, Bool.or_eq_true] at inScope
  rcases inScope with same | oldScoped
  · have oldEq : old = inserted := eq_of_beq same
    subst old
    exact binder
  · exact fresh old oldScoped

theorem freshForScope_pushVar
    {index : ScopeIndex} {forbidden inserted : FVarId}
    (fresh : FreshForScope forbidden index.sourceScope)
    (binder : forbidden.name ≠ inserted.name) :
    FreshForScope forbidden
      (index.pushVar inserted).sourceScope := by
  exact freshForScope_cons fresh binder

theorem freshForScope_pushJoin
    {index : ScopeIndex} {forbidden inserted : FVarId}
    (fresh : FreshForScope forbidden index.sourceJoins)
    (binder : forbidden.name ≠ inserted.name) :
    FreshForScope forbidden
      (index.pushJoin inserted).sourceJoins := by
  exact freshForScope_cons fresh binder

theorem freshForScope_pushParamList
    {index : ScopeIndex} {forbidden : FVarId}
    {params : List (LCNF.Param .impure)}
    (fresh : FreshForScope forbidden index.sourceScope)
    (paramsAvoid : ParamBindersAvoidName forbidden params) :
    FreshForScope forbidden
      (index.pushParamList params).sourceScope := by
  induction params generalizing index with
  | nil => exact fresh
  | cons param rest ih =>
      apply ih
      · exact freshForScope_pushVar fresh
          (paramsAvoid param List.mem_cons_self)
      · intro candidate member
        exact paramsAvoid candidate (List.mem_cons_of_mem param member)

theorem freshForScope_pushParams
    {index : ScopeIndex} {forbidden : FVarId}
    {params : Array (LCNF.Param .impure)}
    (fresh : FreshForScope forbidden index.sourceScope)
    (paramsAvoid :
      ParamBindersAvoidName forbidden params.toList) :
    FreshForScope forbidden
      (index.pushParams params).sourceScope :=
  freshForScope_pushParamList fresh paramsAvoid

theorem pushParamList_sourceJoins
    (index : ScopeIndex) (params : List (LCNF.Param .impure)) :
    (index.pushParamList params).sourceJoins = index.sourceJoins := by
  induction params generalizing index with
  | nil => rfl
  | cons param rest rest_ih =>
      simpa [ScopeIndex.pushParamList, ScopeIndex.pushVar] using
        (rest_ih (index := index.pushVar param.fvarId))

theorem pushParams_sourceJoins
    (index : ScopeIndex) (params : Array (LCNF.Param .impure)) :
    (index.pushParams params).sourceJoins = index.sourceJoins := by
  exact pushParamList_sourceJoins index params.toList

theorem argAvoids_of_scoped
    (fresh : FreshForScope forbidden scope)
    (inScope : argScoped scope argument = true) :
    ArgAvoids forbidden argument := by
  cases argument with
  | erased => trivial
  | fvar fvarId =>
      exact fvarId_ne_of_freshForScope fresh inScope
  | type _ impossible => nomatch impossible

theorem argsAvoid_of_scoped
    (fresh : FreshForScope forbidden scope)
    (inScope : argsScoped scope arguments = true) :
    ArgsAvoid forbidden arguments := by
  intro argument member
  apply argAvoids_of_scoped fresh
  have memberArray : argument ∈ arguments := by
    simpa using member
  exact (Array.all_eq_true'.mp inScope) argument memberArray

theorem letValueAvoids_of_scoped
    (fresh : FreshForScope forbidden scope)
    (inScope : letValueScoped scope value = true) :
    LetValueAvoids forbidden value := by
  cases value with
  | lit _ | erased => trivial
  | fvar fvarId arguments | reuse fvarId _ _ arguments =>
      simp only [letValueScoped, Bool.and_eq_true] at inScope
      exact ⟨fvarId_ne_of_freshForScope fresh inScope.1,
        argsAvoid_of_scoped fresh inScope.2⟩
  | ctor _ arguments | fap _ arguments | pap _ arguments =>
      exact argsAvoid_of_scoped fresh inScope
  | oproj _ fvarId | uproj _ fvarId | sproj _ _ fvarId
  | reset _ fvarId | unbox fvarId | isShared fvarId =>
      exact fvarId_ne_of_freshForScope fresh inScope
  | box _ fvarId =>
      simp only [letValueScoped, Bool.and_eq_true] at inScope
      exact fvarId_ne_of_freshForScope fresh inScope.2
  | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible

private theorem codeAvoidance_caseAlts_sizeOf_lt
    (cases : LCNF.Cases .impure) :
    sizeOf cases.alts.toList < sizeOf (LCNF.Code.cases cases) := by
  rcases cases with ⟨typeName, resultType, discr, alts⟩
  rcases alts with ⟨alts⟩
  simp [LCNF.Cases.alts]
  omega

private theorem codeAvoidance_funDeclValue_sizeOf_lt
    (declaration : LCNF.FunDecl .impure)
    (continuation : LCNF.Code .impure) :
    sizeOf declaration.value <
      sizeOf (LCNF.Code.jp declaration continuation) := by
  cases declaration
  simp_wf
  simp only [LCNF.FunDecl.value]
  omega

private theorem codeAvoidance_altCode_sizeOf_lt_cons
    (alternative : LCNF.Alt .impure)
    (rest : List (LCNF.Alt .impure)) :
    sizeOf alternative.getCode < sizeOf (alternative :: rest) := by
  cases alternative with
  | ctorAlt info code =>
      simp [LCNF.Alt.getCode]
      omega
  | default code =>
      simp [LCNF.Alt.getCode]
      omega
  | alt _ _ _ impossible => nomatch impossible

mutual

  /-- Lexical scope plus negative binder ownership imply that no runtime
  identifier collected from this subtree can name `forbidden`. -/
  theorem ScopedCodeWellFormedTree.codeAvoids
      (wellFormed : ScopedCodeWellFormedTree index code)
      (variablesFresh :
        FreshForScope forbidden index.sourceScope)
      (joinsFresh :
        FreshForScope forbidden index.sourceJoins)
      (binders : CodeBindersAvoidName forbidden code) :
      CodeAvoids forbidden code := by
    cases wellFormed with
    | letE valueScoped _ _ _ continuation =>
        cases binders with
        | letE binderAvoid continuationBinders =>
            exact .letE
              (letValueAvoids_of_scoped variablesFresh valueScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                (freshForScope_pushVar variablesFresh binderAvoid)
                (by simpa [ScopeIndex.pushVar] using joinsFresh)
                continuationBinders)
    | jp _ _ body continuation =>
        cases binders with
        | join binderAvoid paramsAvoid bodyBinders continuationBinders =>
            exact .join
              (ScopedCodeWellFormedTree.codeAvoids body
                (freshForScope_pushParams variablesFresh paramsAvoid)
                (by
                  rw [pushParams_sourceJoins]
                  exact joinsFresh)
                bodyBinders)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                (by simpa [ScopeIndex.pushJoin] using variablesFresh)
                (freshForScope_pushJoin joinsFresh binderAvoid)
                continuationBinders)
    | jmp targetScoped argumentsScoped =>
        exact .jump
          (fvarId_ne_of_freshForScope joinsFresh targetScoped)
          (argsAvoid_of_scoped variablesFresh argumentsScoped)
    | cases discrScoped _ alternatives =>
        cases binders with
        | cases alternativeBinders =>
            exact .cases
              (fvarId_ne_of_freshForScope variablesFresh discrScoped)
              (ScopedCodeWellFormedAlts.codeAvoids alternatives
                variablesFresh joinsFresh
                alternativeBinders)
    | ret resultScoped =>
        exact .ret
          (fvarId_ne_of_freshForScope variablesFresh resultScoped)
    | unreach => exact .unreachable _
    | oset objectScoped fieldScoped continuation =>
        cases binders with
        | objectSet continuationBinders =>
            exact .objectSet
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (argAvoids_of_scoped variablesFresh fieldScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | uset objectScoped fieldScoped continuation =>
        cases binders with
        | usizeSet continuationBinders =>
            exact .usizeSet
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (fvarId_ne_of_freshForScope variablesFresh fieldScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | sset objectScoped fieldScoped continuation =>
        cases binders with
        | scalarSet continuationBinders =>
            exact .scalarSet
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (fvarId_ne_of_freshForScope variablesFresh fieldScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | setTag objectScoped continuation =>
        cases binders with
        | tagSet continuationBinders =>
            exact .tagSet
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | inc objectScoped continuation =>
        cases binders with
        | increment continuationBinders =>
            exact .increment
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | dec objectScoped continuation =>
        cases binders with
        | decrement continuationBinders =>
            exact .decrement
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | del objectScoped continuation =>
        cases binders with
        | delete continuationBinders =>
            exact .delete
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)

  termination_by sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply codeAvoidance_caseAlts_sizeOf_lt
      | apply codeAvoidance_funDeclValue_sizeOf_lt

  theorem ScopedCodeWellFormedAlts.codeAvoids
      (wellFormed : ScopedCodeWellFormedAlts index alternatives)
      (variablesFresh :
        FreshForScope forbidden index.sourceScope)
      (joinsFresh :
        FreshForScope forbidden index.sourceJoins)
      (binders : ∀ alternative, alternative ∈ alternatives →
        CodeBindersAvoidName forbidden alternative.getCode) :
      ∀ alternative, alternative ∈ alternatives →
        CodeAvoids forbidden alternative.getCode := by
    intro alternative member
    cases wellFormed with
    | nil => simp at member
    | ctor body rest =>
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ScopedCodeWellFormedTree.codeAvoids body
            variablesFresh joinsFresh
            (binders _ List.mem_cons_self)
        · exact ScopedCodeWellFormedAlts.codeAvoids rest
            variablesFresh joinsFresh
            (fun candidate candidateMember =>
              binders candidate
                (List.mem_cons_of_mem _ candidateMember))
            alternative member
    | default body rest =>
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ScopedCodeWellFormedTree.codeAvoids body
            variablesFresh joinsFresh
            (binders _ List.mem_cons_self)
        · exact ScopedCodeWellFormedAlts.codeAvoids rest
            variablesFresh joinsFresh
            (fun candidate candidateMember =>
              binders candidate
                (List.mem_cons_of_mem _ candidateMember))
            alternative member

  termination_by sizeOf alternatives
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply codeAvoidance_altCode_sizeOf_lt_cons
      | (simp_wf; omega)

end

/-- Direct checked-hygiene form of the backwards-liveness freshness theorem.
It is the reusable boundary for proving that liveness threaded in from a
disjoint subtree cannot reintroduce a binder owned by the current subtree. -/
theorem shadowCode_preserves_absent_of_wellFormed
    (wellFormed : ScopedCodeWellFormedTree index source)
    (variablesFresh :
      FreshForScope forbidden index.sourceScope)
    (joinsFresh :
      FreshForScope forbidden index.sourceJoins)
    (binders : CodeBindersAvoidName forbidden source)
    (absent : initial.contains forbidden = false)
    (result : shadowCode? fuel initial source = some output) :
    output.2.contains forbidden = false :=
  shadowCode_preserves_absent absent
    (ScopedCodeWellFormedTree.codeAvoids wellFormed variablesFresh
      joinsFresh binders)
    result

end Fir.LeanIR.Passes.ElimDead
