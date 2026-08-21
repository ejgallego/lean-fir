import Lean.Compiler.LCNF.PassManager
import Lean.Util.CollectFVars
import Std.Data.HashSet.Lemmas

namespace Fir.LeanIR.ImpureHygiene

open Lean
open Lean.Compiler

/-- The two namespaces that matter operationally in impure LCNF. -/
structure Scope where
  vars : List FVarId := []
  joins : List FVarId := []

def exprScoped (scope : List FVarId) (expr : Expr) : Bool :=
  (collectFVars {} expr).fvarIds.all scope.contains

def argScoped (scope : List FVarId) : LCNF.Arg .impure → Bool
  | .erased => true
  | .fvar fvarId => scope.contains fvarId
  | .type _ impossible => nomatch impossible

def argsScoped (scope : List FVarId) (args : Array (LCNF.Arg .impure)) : Bool :=
  args.all (argScoped scope)

def letValueScoped (scope : List FVarId) : LCNF.LetValue .impure → Bool
  | .lit _ | .erased => true
  | .proj _ _ _ impossible | .const _ _ _ impossible => nomatch impossible
  | .fvar fvarId args => scope.contains fvarId && argsScoped scope args
  | .ctor _ args => argsScoped scope args
  | .oproj _ fvarId | .uproj _ fvarId | .sproj _ _ fvarId => scope.contains fvarId
  | .fap _ args | .pap _ args => argsScoped scope args
  | .reset _ fvarId => scope.contains fvarId
  | .reuse fvarId _ _ args => scope.contains fvarId && argsScoped scope args
  | .box type fvarId => exprScoped scope type && scope.contains fvarId
  | .unbox fvarId | .isShared fvarId => scope.contains fvarId

def paramIds (params : Array (LCNF.Param .impure)) : List FVarId :=
  params.toList.map (fun param => param.fvarId)

private theorem hygieneCaseAlts_sizeOf_lt (cases : LCNF.Cases .impure) :
    sizeOf cases.alts.toList < sizeOf (LCNF.Code.cases cases) := by
  rcases cases with ⟨typeName, resultType, discr, alts⟩
  rcases alts with ⟨alts⟩
  simp [LCNF.Cases.alts]
  omega

private theorem hygieneFunDeclValue_sizeOf_lt
    (declaration : LCNF.FunDecl .impure)
    (continuation : LCNF.Code .impure) :
    sizeOf declaration.value <
      sizeOf (LCNF.Code.jp declaration continuation) := by
  cases declaration
  simp_wf
  simp only [LCNF.FunDecl.value]
  omega

private theorem hygieneAltCode_sizeOf_lt_cons
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

/-- Transparent executable lexical-scope checker for impure LCNF code. -/
def codeScoped (scope : Scope) : LCNF.Code .impure → Bool
  | .let decl continuation =>
      exprScoped scope.vars decl.type &&
        letValueScoped scope.vars decl.value &&
        codeScoped { scope with vars := decl.fvarId :: scope.vars } continuation
  | .fun _ _ impossible => nomatch impossible
  | .jp decl continuation =>
      let vars := paramIds decl.params ++ scope.vars
      decl.params.all (fun param => exprScoped vars param.type) &&
        exprScoped vars decl.type &&
        codeScoped { scope with vars } decl.value &&
        codeScoped { scope with joins := decl.fvarId :: scope.joins } continuation
  | .jmp fvarId args => scope.joins.contains fvarId && argsScoped scope.vars args
  | .cases cases =>
      exprScoped scope.vars cases.resultType &&
        scope.vars.contains cases.discr &&
        altsScoped scope cases.alts.toList
  | .return fvarId => scope.vars.contains fvarId
  | .unreach type => exprScoped scope.vars type
  | .oset fvarId _ arg continuation =>
      scope.vars.contains fvarId &&
        argScoped scope.vars arg &&
        codeScoped scope continuation
  | .uset fvarId _ fieldId continuation =>
      scope.vars.contains fvarId &&
        scope.vars.contains fieldId &&
        codeScoped scope continuation
  | .sset fvarId _ _ fieldId type continuation =>
      scope.vars.contains fvarId &&
        scope.vars.contains fieldId &&
        exprScoped scope.vars type &&
        codeScoped scope continuation
  | .setTag fvarId _ continuation
  | .inc fvarId _ _ _ continuation
  | .dec fvarId _ _ _ _ continuation
  | .del fvarId continuation =>
      scope.vars.contains fvarId && codeScoped scope continuation

  termination_by code => sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply hygieneCaseAlts_sizeOf_lt
      | apply hygieneFunDeclValue_sizeOf_lt

def altsScoped (scope : Scope) : List (LCNF.Alt .impure) → Bool
  | [] => true
  | .ctorAlt _ code :: alternatives
  | .default code :: alternatives =>
      codeScoped scope code && altsScoped scope alternatives

  termination_by alternatives => sizeOf alternatives
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals apply hygieneAltCode_sizeOf_lt_cons

end

/-- One-alternative compatibility surface backed by the total code checker. -/
def altScoped (scope : Scope) : LCNF.Alt .impure → Bool
  | .alt _ _ _ impossible => nomatch impossible
  | .ctorAlt _ code | .default code => codeScoped scope code

/-- Join-declaration compatibility surface backed by the total code checker. -/
def funDeclScoped (scope : Scope) (decl : LCNF.FunDecl .impure) : Bool :=
  let vars := paramIds decl.params ++ scope.vars
  decl.params.all (fun param => exprScoped vars param.type) &&
    exprScoped vars decl.type &&
    codeScoped { scope with vars } decl.value

mutual

/-- Transparent declaration-wide binder enumeration for impure LCNF code. -/
def codeBinders : LCNF.Code .impure → List FVarId
  | .let decl continuation => decl.fvarId :: codeBinders continuation
  | .fun _ _ impossible => nomatch impossible
  | .jp decl continuation =>
      decl.fvarId :: (paramIds decl.params ++ codeBinders decl.value ++ codeBinders continuation)
  | .cases cases => altsBinders cases.alts.toList
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation => codeBinders continuation
  | .jmp _ _ | .return _ | .unreach _ => []

  termination_by code => sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply hygieneCaseAlts_sizeOf_lt
      | apply hygieneFunDeclValue_sizeOf_lt

def altsBinders : List (LCNF.Alt .impure) → List FVarId
  | [] => []
  | alternative :: alternatives =>
      codeBinders alternative.getCode ++ altsBinders alternatives

  termination_by alternatives => sizeOf alternatives
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals apply hygieneAltCode_sizeOf_lt_cons

end

/-- One-alternative compatibility surface backed by the total enumeration. -/
def altBinders : LCNF.Alt .impure → List FVarId
  | .alt _ _ _ impossible => nomatch impossible
  | .ctorAlt _ code | .default code => codeBinders code

def bindersUnique (binders : List FVarId) : Bool :=
  go {} binders
where
  go (seen : Std.HashSet Name) : List FVarId → Bool
    | [] => true
    | fvarId :: rest =>
        !seen.contains fvarId.name && go (seen.insert fvarId.name) rest

/-- Proof-facing spelling of the executable binder-name uniqueness check. -/
def BinderNamesUnique (binders : List FVarId) : Prop :=
  binders.Pairwise fun left right => left.name ≠ right.name

private def BinderNamesAvoidSet (seen : Std.HashSet Name)
    (binders : List FVarId) : Prop :=
  ∀ binder, binder ∈ binders → binder.name ∉ seen

private theorem bindersUnique_go_sound
    (seen : Std.HashSet Name) (binders : List FVarId)
    (accepted : bindersUnique.go seen binders = true) :
    BinderNamesAvoidSet seen binders ∧ BinderNamesUnique binders := by
  induction binders generalizing seen with
  | nil =>
      simp [BinderNamesAvoidSet, BinderNamesUnique]
  | cons binder rest ih =>
      simp only [bindersUnique.go, Bool.and_eq_true] at accepted
      rcases ih (seen := seen.insert binder.name) accepted.2 with
        ⟨restAvoids, restUnique⟩
      constructor
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · simpa [Std.HashSet.contains_eq_false_iff_not_mem] using accepted.1
        · have notInInserted := restAvoids candidate member
          exact fun inSeen => notInInserted (by simp [inSeen])
      · rw [BinderNamesUnique, List.pairwise_cons]
        constructor
        · intro candidate member equalNames
          exact restAvoids candidate member (by simp [equalNames])
        · exact restUnique

theorem bindersUnique_sound
    (accepted : bindersUnique binders = true) :
    BinderNamesUnique binders :=
  (bindersUnique_go_sound {} binders accepted).2

theorem BinderNamesUnique.left_of_append
    (unique : BinderNamesUnique (left ++ right)) :
    BinderNamesUnique left :=
  (List.pairwise_append.mp unique).1

theorem BinderNamesUnique.right_of_append
    (unique : BinderNamesUnique (left ++ right)) :
    BinderNamesUnique right :=
  (List.pairwise_append.mp unique).2.1

theorem BinderNamesUnique.of_cons
    {head : FVarId} {rest : List FVarId}
    (unique : BinderNamesUnique (head :: rest)) :
    BinderNamesUnique rest :=
  List.Pairwise.of_cons unique

/-- Parameters followed by the complete body traversal used by hygiene. -/
def declBinders (decl : LCNF.Decl .impure) : List FVarId :=
  let params := paramIds decl.params
  match decl.value with
  | .extern _ => params
  | .code code => params ++ codeBinders code

def declHygienic (decl : LCNF.Decl .impure) : Bool :=
  let params := paramIds decl.params
  let scope : Scope := { vars := params }
  let signatureScoped :=
    decl.params.all (fun param => exprScoped params param.type) && exprScoped params decl.type
  match decl.value with
  | .extern _ => bindersUnique params && signatureScoped
  | .code code =>
      bindersUnique (params ++ codeBinders code) && signatureScoped && codeScoped scope code

/-- Successful phase hygiene exposes declaration-wide structural freshness. -/
theorem declHygienic_binderNamesUnique
    (accepted : declHygienic decl = true) :
    BinderNamesUnique (declBinders decl) := by
  cases decl with
  | mk signature value recursive inlineAttr =>
      cases value with
      | extern metadata =>
          simp only [declHygienic, Bool.and_eq_true] at accepted
          exact bindersUnique_sound accepted.1
      | code code =>
          simp only [declHygienic, Bool.and_eq_true] at accepted
          exact bindersUnique_sound accepted.1.1

end Fir.LeanIR.ImpureHygiene
