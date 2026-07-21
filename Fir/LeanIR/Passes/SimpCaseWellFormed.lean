import Fir.LeanIR.Phase
import Fir.LeanIR.Passes.SimpCaseScopedBridge

namespace Fir.LeanIR.Passes.SimpCaseWellFormed

open Lean
open Lean.Compiler
open Fir.LeanIR.ImpureHygiene
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.NonLockstep.Structural
open Fir.LeanIR.Passes.SimpCaseRelation
open Fir.LeanIR.Passes.SimpCaseScopedBridge

/-!
This module is the compiler-facing entry point for the `simpCase` proof.
The recursive certificates consumed by `SimpCaseScopedBridge` are deliberately
absent from the definitions below.  Instead, a source program records the
three independent invariants that the compiler can check or preserve:

* ordinary phase well-formedness (unique declaration names and impure LCNF
  hygiene);
* deterministic selector normalization at every case node;
* canonical runtime-observed type metadata.

The next layer proves that these invariants synthesize the proof-facing scoped
certificate tree.  Keeping this boundary separate prevents callers from
having to construct those certificates by hand.
-/

/-- Recursive case-table normalization for a declaration value. External
declarations have no executable body and therefore no case table. -/
def DeclValueNormalizationTree : LCNF.DeclValue .impure → Prop
  | .code code => CodeNormalizationTree code
  | .extern _ => True

def DeclNormalizationTree (declaration : LCNF.Decl .impure) : Prop :=
  DeclValueNormalizationTree declaration.value

def DeclListNormalizationTree
    (declarations : List (LCNF.Decl .impure)) : Prop :=
  ∀ declaration, declaration ∈ declarations →
    DeclNormalizationTree declaration

def ProgramNormalizationTree (program : ImpureProgram) : Prop :=
  DeclListNormalizationTree program.decls.toList

/-- The minimal declaration-local compiler invariant.  This contains no
alpha, structural, semantic, or pass-specific certificate. -/
structure DeclWellFormed (declaration : LCNF.Decl .impure) : Prop where
  hygienic : ImpureHygiene.declHygienic declaration = true
  normalization : DeclNormalizationTree declaration
  canonical : DeclRuntimeTypesCanonical declaration

/-- Compiler-shaped source premise for the preferred whole-program theorem.
`phase` is the shared LeanIR invariant; the two remaining fields are the
independent invariants used only by the `simpCase` alpha-fold proof. -/
structure ProgramWellFormed (program : ImpureProgram) : Prop where
  phase : WellFormedAt .impure program
  normalization : ProgramNormalizationTree program
  canonical : ProgramRuntimeTypesCanonical program

/-! ## Executable scoping to declarative self-relations -/

/-- A resolver observationally equivalent to the empty resolver maps every
unchanged free variable to itself. -/
theorem fVarRelated_self_of_resolverEquivalent_empty
    (empty : ResolverEquivalent rho {}) (fvarId : FVarId) :
    FVarRelated rho fvarId fvarId := by
  change (fvarId == (rho.get? fvarId).getD fvarId) = true
  rw [empty fvarId, emptyResolver_getD]
  cases fvarId with
  | mk name => exact Name.beq_iff_eq.mpr rfl

theorem scopedFVarRelated_self_of_resolverEquivalent_empty
    (empty : ResolverEquivalent rho {})
    (inScope : scope.contains fvarId = true) :
    ScopedFVarRelated rho scope scope fvarId fvarId :=
  ⟨inScope, inScope,
    fVarRelated_self_of_resolverEquivalent_empty empty fvarId⟩

theorem argRelated_self_of_resolverEquivalent_empty
    (empty : ResolverEquivalent rho {})
    (inScope : argScoped scope arg = true) :
    ArgRelated rho scope scope arg arg := by
  cases arg with
  | erased => exact ⟨rfl, rfl, rfl⟩
  | fvar fvarId =>
      exact ⟨inScope, inScope,
        fVarRelated_self_of_resolverEquivalent_empty empty fvarId⟩
  | type _ impossible => nomatch impossible

theorem argsRelated_self_of_resolverEquivalent_empty
    (empty : ResolverEquivalent rho {})
    (inScope : argsScoped scope args = true) :
    ArgsRelated rho scope scope args args := by
  have scopedList : args.toList.all (argScoped scope) = true := by
    simpa [argsScoped] using inScope
  let rec go (arguments : List (LCNF.Arg .impure))
      (allScoped : arguments.all (argScoped scope) = true) :
      ListRel (ArgRelated rho scope scope) arguments arguments :=
    match arguments with
    | [] => .nil
    | argument :: rest => by
        simp only [List.all_cons, Bool.and_eq_true] at allScoped
        exact .cons
          (argRelated_self_of_resolverEquivalent_empty empty allScoped.1)
          (go rest allScoped.2)
  exact go args.toList scopedList

/-- The impure let-value scoping check contains exactly the variable and
argument facts needed by the declarative self-relation. -/
theorem letValueRelated_self_of_resolverEquivalent_empty
    (empty : ResolverEquivalent rho {})
    (inScope : letValueScoped scope value = true) :
    LetValueRelated rho scope scope value value := by
  cases value with
  | lit literal => exact .lit literal
  | erased => exact .erased
  | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible
  | fvar fvarId args =>
      simp only [letValueScoped, Bool.and_eq_true] at inScope
      exact .fvar
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope.1)
        (argsRelated_self_of_resolverEquivalent_empty empty inScope.2)
  | ctor info args =>
      exact .ctor (argsRelated_self_of_resolverEquivalent_empty empty inScope)
  | oproj index fvarId =>
      exact .oproj
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope)
  | uproj index fvarId =>
      exact .uproj
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope)
  | sproj width offset fvarId =>
      exact .sproj
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope)
  | fap name args =>
      exact .fap (argsRelated_self_of_resolverEquivalent_empty empty inScope)
  | pap name args =>
      exact .pap (argsRelated_self_of_resolverEquivalent_empty empty inScope)
  | reset count fvarId =>
      exact .reset
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope)
  | reuse fvarId info updateHeader args =>
      simp only [letValueScoped, Bool.and_eq_true] at inScope
      exact .reuse
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope.1)
        (argsRelated_self_of_resolverEquivalent_empty empty inScope.2)
  | box type fvarId =>
      simp only [letValueScoped, Bool.and_eq_true] at inScope
      exact .box
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope.2)
  | unbox fvarId =>
      exact .unbox
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope)
  | isShared fvarId =>
      exact .isShared
        (scopedFVarRelated_self_of_resolverEquivalent_empty empty inScope)

theorem letDeclValueRelated_self_of_resolverEquivalent_empty
    (empty : ResolverEquivalent rho {})
    (inScope : letValueScoped scope declaration.value = true) :
    LetDeclValueRelated rho scope scope declaration declaration :=
  ⟨rfl, letValueRelated_self_of_resolverEquivalent_empty empty inScope⟩

theorem letValueBoxTypesEq_self (value : LCNF.LetValue .impure) :
    LetValueBoxTypesEq value value := by
  cases value <;> simp [LetValueBoxTypesEq]

/-! ## Minimal scoped well-formedness tree -/

/-- Binder freshness for a parameter list, accumulated in the same order as
`ScopeIndex.pushParams`. Parameter type expressions are already covered by
the phase hygiene checker and are not duplicated here. -/
inductive ScopedParamsWellFormed :
    ScopeIndex → List (LCNF.Param .impure) → Prop where
  | nil : ScopedParamsWellFormed index []
  | cons
      (variableFresh : FreshForScope param.fvarId index.sourceScope)
      (joinFresh : FreshForScope param.fvarId index.sourceJoins)
      (rest : ScopedParamsWellFormed (index.pushVar param.fvarId) params) :
      ScopedParamsWellFormed index (param :: params)

mutual

  /-- Proof-relevant view of precisely the local facts extracted from impure
  hygiene, case normalization, and runtime-type canonicality.  Unlike
  `ScopedCodeTargetCertificateTree`, its constructors mention no pass
  relation or semantic certificate. -/
  inductive ScopedCodeWellFormedTree :
      ScopeIndex → LCNF.Code .impure → Prop where
    | letE
        (valueScoped : letValueScoped index.sourceScope declaration.value = true)
        (variableFresh : FreshForScope declaration.fvarId index.sourceScope)
        (joinFresh : FreshForScope declaration.fvarId index.sourceJoins)
        (runtimeTypes : LetDeclRuntimeTypesCanonical declaration)
        (continuation : ScopedCodeWellFormedTree
          (index.pushVar declaration.fvarId) rest) :
        ScopedCodeWellFormedTree index (.let declaration rest)
    | jp
        (binderFresh : FreshJoinBinder fvarId
          index.sourceScope index.sourceJoins)
        (paramsFresh : ScopedParamsWellFormed index params.toList)
        (bodyTree : ScopedCodeWellFormedTree (index.pushParams params) body)
        (continuation : ScopedCodeWellFormedTree
          (index.pushJoin fvarId) rest) :
        ScopedCodeWellFormedTree index
          (.jp (.mk fvarId binderName params type body) rest)
    | jmp
        (targetScoped : index.sourceJoins.contains target = true)
        (argumentsScoped : argsScoped index.sourceScope args = true) :
        ScopedCodeWellFormedTree index (.jmp target args)
    | cases
        (discrScoped : index.sourceScope.contains cases.discr = true)
        (normalization : CaseTableNormalizationInvariant cases.alts)
        (alternatives : ScopedCodeWellFormedAlts index cases.alts.toList) :
        ScopedCodeWellFormedTree index (.cases cases)
    | ret
        (resultScoped : index.sourceScope.contains result = true) :
        ScopedCodeWellFormedTree index (.return result)
    | unreach : ScopedCodeWellFormedTree index (.unreach type)
    | oset
        (objectScoped : index.sourceScope.contains object = true)
        (fieldScoped : argScoped index.sourceScope field = true)
        (continuation : ScopedCodeWellFormedTree index rest) :
        ScopedCodeWellFormedTree index (.oset object fieldIndex field rest)
    | uset
        (objectScoped : index.sourceScope.contains object = true)
        (fieldScoped : index.sourceScope.contains field = true)
        (continuation : ScopedCodeWellFormedTree index rest) :
        ScopedCodeWellFormedTree index (.uset object fieldIndex field rest)
    | sset
        (objectScoped : index.sourceScope.contains object = true)
        (fieldScoped : index.sourceScope.contains field = true)
        (continuation : ScopedCodeWellFormedTree index rest) :
        ScopedCodeWellFormedTree index
          (.sset object width offset field type rest)
    | setTag
        (objectScoped : index.sourceScope.contains object = true)
        (continuation : ScopedCodeWellFormedTree index rest) :
        ScopedCodeWellFormedTree index (.setTag object tag rest)
    | inc
        (objectScoped : index.sourceScope.contains object = true)
        (continuation : ScopedCodeWellFormedTree index rest) :
        ScopedCodeWellFormedTree index
          (.inc object amount check persistent rest)
    | dec
        (objectScoped : index.sourceScope.contains object = true)
        (continuation : ScopedCodeWellFormedTree index rest) :
        ScopedCodeWellFormedTree index
          (.dec object amount check persistent objects rest)
    | del
        (objectScoped : index.sourceScope.contains object = true)
        (continuation : ScopedCodeWellFormedTree index rest) :
        ScopedCodeWellFormedTree index (.del object rest)

  /-- Pointwise well-formedness for every alternative array entry, including
  entries shadowed by an earlier duplicate selector. -/
  inductive ScopedCodeWellFormedAlts :
      ScopeIndex → List (LCNF.Alt .impure) → Prop where
    | nil : ScopedCodeWellFormedAlts index []
    | ctor
        (body : ScopedCodeWellFormedTree index code)
        (rest : ScopedCodeWellFormedAlts index alts) :
        ScopedCodeWellFormedAlts index (.ctorAlt info code :: alts)
    | default
        (body : ScopedCodeWellFormedTree index code)
        (rest : ScopedCodeWellFormedAlts index alts) :
        ScopedCodeWellFormedAlts index (.default code :: alts)

end

theorem ScopeIndex.freshTargetScope
    (index : ScopeIndex)
    (fresh : FreshForScope fvarId index.sourceScope) :
    FreshForScope fvarId index.targetScope := by
  rw [← index.scopesEq]
  exact fresh

theorem ScopeIndex.freshTargetJoins
    (index : ScopeIndex)
    (fresh : FreshForScope fvarId index.sourceJoins) :
    FreshForScope fvarId index.targetJoins := by
  rw [← index.joinsEq]
  exact fresh

theorem scopeIndex_scopedFVarForward
    (index : ScopeIndex)
    (inScope : index.sourceScope.contains fvarId = true) :
    ScopedFVarRelated index.forwardRho index.sourceScope index.targetScope
      fvarId fvarId := by
  rw [← index.scopesEq]
  exact scopedFVarRelated_self_of_resolverEquivalent_empty
    index.forwardEmpty inScope

theorem scopeIndex_scopedJoinForward
    (index : ScopeIndex)
    (inScope : index.sourceJoins.contains fvarId = true) :
    ScopedFVarRelated index.forwardRho index.sourceJoins index.targetJoins
      fvarId fvarId := by
  rw [← index.joinsEq]
  exact scopedFVarRelated_self_of_resolverEquivalent_empty
    index.forwardEmpty inScope

theorem scopeIndex_argForward
    (index : ScopeIndex)
    (inScope : argScoped index.sourceScope arg = true) :
    ArgRelated index.forwardRho index.sourceScope index.targetScope arg arg := by
  rw [← index.scopesEq]
  exact argRelated_self_of_resolverEquivalent_empty index.forwardEmpty inScope

theorem scopeIndex_argsForward
    (index : ScopeIndex)
    (inScope : argsScoped index.sourceScope args = true) :
    ArgsRelated index.forwardRho index.sourceScope index.targetScope args args := by
  rw [← index.scopesEq]
  exact argsRelated_self_of_resolverEquivalent_empty index.forwardEmpty inScope

theorem scopeIndex_letDeclValueForward
    (index : ScopeIndex)
    (inScope : letValueScoped index.sourceScope declaration.value = true) :
    LetDeclValueRelated index.forwardRho index.sourceScope index.targetScope
      declaration declaration := by
  rw [← index.scopesEq]
  exact letDeclValueRelated_self_of_resolverEquivalent_empty
    index.forwardEmpty inScope

theorem ScopedParamsWellFormed.paramBodyRelated
    (wellFormed : ScopedParamsWellFormed index params)
    (body : CodeRelated
      (leftJoins := (index.pushParamList params).sourceJoins)
      (rightJoins := (index.pushParamList params).targetJoins)
      (index.pushParamList params).forwardRho
      (index.pushParamList params).sourceScope
      (index.pushParamList params).targetScope code code) :
    ParamBodyRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope
      params params code code := by
  cases wellFormed with
  | nil => exact .nil body
  | @cons restParams innerIndex param variableFresh joinFresh rest =>
      apply ParamBodyRelated.cons variableFresh
        (ScopeIndex.freshTargetScope index variableFresh) joinFresh
        (ScopeIndex.freshTargetJoins index joinFresh)
      apply rest.paramBodyRelated
      simpa [ScopeIndex.pushParamList] using body

theorem ScopedParamsWellFormed.paramBodySideConditions
    (wellFormed : ScopedParamsWellFormed index params)
    (body : CodeSideConditions
      (leftJoins := (index.pushParamList params).sourceJoins)
      (rightJoins := (index.pushParamList params).sourceJoins)
      (index.pushParamList params).forwardRho
      (index.pushParamList params).sourceScope
      (index.pushParamList params).sourceScope code code) :
    ParamBodySideConditions
      (leftJoins := index.sourceJoins) (rightJoins := index.sourceJoins)
      index.forwardRho index.sourceScope index.sourceScope
      params params code code := by
  cases wellFormed with
  | nil => exact .nil body
  | @cons restParams innerIndex param variableFresh joinFresh rest =>
      apply ParamBodySideConditions.cons variableFresh variableFresh
        joinFresh joinFresh
      apply rest.paramBodySideConditions
      simpa [ScopeIndex.pushParamList] using body

theorem certificateAlts_structural
    (certificates : ScopedCodeTargetCertificateAlts validCase index alts) :
    StructuralAltsRelated validCase alts alts :=
  match certificates with
  | .nil => .nil
  | .ctor body rest =>
      .cons (.ctor body.root.structural) (certificateAlts_structural rest)
  | .default body rest =>
      .cons (.default body.root.structural) (certificateAlts_structural rest)

theorem certificateAlts_alphaForward
    (certificates : ScopedCodeTargetCertificateAlts validCase index alts) :
    AltsRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope alts alts :=
  match certificates with
  | .nil => .nil
  | .ctor body rest =>
      .cons (.ctor body.root.alpha.forward) (certificateAlts_alphaForward rest)
  | .default body rest =>
      .cons (.default body.root.alpha.forward) (certificateAlts_alphaForward rest)

theorem certificateAlts_side
    (certificates : ScopedCodeTargetCertificateAlts validCase index alts)
    (member : alt ∈ alts) :
    ScopedCodeSideReflexive index alt.getCode := by
  cases certificates with
  | nil => simp at member
  | ctor body rest =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact body.root.side
      · exact certificateAlts_side rest member
  | default body rest =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact body.root.side
      · exact certificateAlts_side rest member
termination_by sizeOf alts
decreasing_by all_goals simp_all <;> omega

theorem certificateAlts_canonical
    (certificates : ScopedCodeTargetCertificateAlts validCase index alts)
    (member : alt ∈ alts) :
    CodeRuntimeTypesCanonical alt.getCode := by
  cases certificates with
  | nil => simp at member
  | ctor body rest =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact body.root.canonical
      · exact certificateAlts_canonical rest member
  | default body rest =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact body.root.canonical
      · exact certificateAlts_canonical rest member
termination_by sizeOf alts
decreasing_by all_goals simp_all <;> omega

theorem certificateAlts_ctorSide
    (certificates : ScopedCodeTargetCertificateAlts validCase index alts)
    (deterministic : CaseTableDeterministic alts) :
    ∀ tag leftCode rightCode,
      HasCtorAlt tag leftCode alts → HasCtorAlt tag rightCode alts →
      CodeSideConditions
        (leftJoins := index.sourceJoins)
        (rightJoins := index.sourceJoins)
        index.forwardRho index.sourceScope index.sourceScope
        leftCode rightCode := by
  intro tag leftCode rightCode leftHas rightHas
  have equal := deterministic.ctor tag leftCode rightCode leftHas rightHas
  subst rightCode
  rcases leftHas with ⟨info, member, _⟩
  exact certificateAlts_side certificates member

theorem certificateAlts_defaultSide
    (certificates : ScopedCodeTargetCertificateAlts validCase index alts)
    (deterministic : CaseTableDeterministic alts) :
    ∀ leftCode rightCode,
      HasDefaultAlt leftCode alts → HasDefaultAlt rightCode alts →
      CodeSideConditions
        (leftJoins := index.sourceJoins)
        (rightJoins := index.sourceJoins)
        index.forwardRho index.sourceScope index.sourceScope
        leftCode rightCode := by
  intro leftCode rightCode leftHas rightHas
  have equal := deterministic.default leftCode rightCode leftHas rightHas
  subst rightCode
  exact certificateAlts_side certificates leftHas

theorem certificateAlts_structuralCases
    (certificates : ScopedCodeTargetCertificateAlts
      validCase index cases.alts.toList) :
    CodeRel validCase (.cases cases) (.cases cases) := by
  rcases cases with ⟨typeName, resultType, discr, alts⟩
  exact .aligned (.cases typeName resultType discr alts alts
    (fun _ _ => structuralChooseAlt_related
      (certificateAlts_structural certificates)))

/-- The two scope-independent invariants carried by a well-formed code tree. -/
structure CodeStaticWellFormed (code : LCNF.Code .impure) : Prop where
  normalization : CodeNormalizationTree code
  canonical : CodeRuntimeTypesCanonical code

private theorem caseAlts_sizeOf_lt (cases : LCNF.Cases .impure) :
    sizeOf cases.alts.toList < sizeOf (LCNF.Code.cases cases) := by
  rcases cases with ⟨typeName, resultType, discr, alts⟩
  rcases alts with ⟨alts⟩
  simp [LCNF.Cases.alts]
  omega

mutual

  theorem ScopedCodeWellFormedTree.static
      (wellFormed : ScopedCodeWellFormedTree index code) :
      CodeStaticWellFormed code := by
    cases wellFormed with
    | letE _ _ _ runtimeTypes continuation =>
        exact {
          normalization := .letE continuation.static.normalization
          canonical := .letE runtimeTypes continuation.static.canonical
        }
    | jp _ _ body continuation =>
        exact {
          normalization := .jp body.static.normalization
            continuation.static.normalization
          canonical := .jp body.static.canonical continuation.static.canonical
        }
    | jmp _ _ => exact ⟨.jmp, .jmp⟩
    | cases _ normalization alternatives =>
        exact {
          normalization := .cases normalization
            (fun alt member =>
              (alternatives.static alt member).normalization)
          canonical := .cases
            (fun alt member =>
              (alternatives.static alt member).canonical)
        }
    | ret _ => exact ⟨.ret, .ret⟩
    | unreach => exact ⟨.unreach, .unreach⟩
    | oset _ _ continuation =>
        exact ⟨.oset continuation.static.normalization,
          .oset continuation.static.canonical⟩
    | uset _ _ continuation =>
        exact ⟨.uset continuation.static.normalization,
          .uset continuation.static.canonical⟩
    | sset _ _ continuation =>
        exact ⟨.sset continuation.static.normalization,
          .sset continuation.static.canonical⟩
    | setTag _ continuation =>
        exact ⟨.setTag continuation.static.normalization,
          .setTag continuation.static.canonical⟩
    | inc _ continuation =>
        exact ⟨.inc continuation.static.normalization,
          .inc continuation.static.canonical⟩
    | dec _ continuation =>
        exact ⟨.dec continuation.static.normalization,
          .dec continuation.static.canonical⟩
    | del _ continuation =>
        exact ⟨.del continuation.static.normalization,
          .del continuation.static.canonical⟩

  termination_by sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals apply caseAlts_sizeOf_lt

  theorem ScopedCodeWellFormedAlts.static
      (wellFormed : ScopedCodeWellFormedAlts index alts) :
      ∀ alt, alt ∈ alts → CodeStaticWellFormed alt.getCode := by
    intro alt member
    cases wellFormed with
    | nil => simp at member
    | ctor body rest =>
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact body.static
        · exact rest.static alt member
    | default body rest =>
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact body.static
        · exact rest.static alt member

  termination_by sizeOf alts
  decreasing_by all_goals simp_all <;> omega

end

/-! ## Synthesis of proof-facing certificates -/

mutual

  /-- A minimal compiler-facing tree contains all data needed by the existing
  proof-facing certificate traversal.  The structural and alpha identities
  below are derived facts; callers never construct them. -/
  theorem ScopedCodeWellFormedTree.certificateTree
      (wellFormed : ScopedCodeWellFormedTree index code) :
      ScopedCodeTargetCertificateTree validCase index code := by
    cases wellFormed with
    | letE valueScoped variableFresh joinFresh runtimeTypes continuation =>
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            _ _ :=
          .letE
            (scopeIndex_letDeclValueForward index valueScoped)
            variableFresh (ScopeIndex.freshTargetScope index variableFresh)
            joinFresh (ScopeIndex.freshTargetJoins index joinFresh)
            continuationTree.root.alpha.forward
        exact .letE {
          structural := .aligned (.let _
            continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .letE rfl valueScoped valueScoped
            (letValueBoxTypesEq_self _)
            variableFresh variableFresh joinFresh joinFresh
            continuationTree.root.side
          canonical := .letE runtimeTypes continuationTree.root.canonical
        } continuationTree
    | @jp fvarId index params bodyCode rest binderName type
        binderFresh paramsFresh body continuation =>
        have bodyTree := body.certificateTree (validCase := validCase)
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have bodyForward :=
          paramsFresh.paramBodyRelated bodyTree.root.alpha.forward
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.jp (.mk fvarId binderName params type bodyCode) rest)
            (.jp (.mk fvarId binderName params type bodyCode) rest) :=
          .jp binderFresh {
            variables := ScopeIndex.freshTargetScope index binderFresh.variables
            joins := ScopeIndex.freshTargetJoins index binderFresh.joins
          } bodyForward continuationTree.root.alpha.forward
        exact .jp {
          structural := .aligned (.jp fvarId binderName params type
            bodyTree.root.structural continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .jp binderFresh binderFresh
            (paramsFresh.paramBodySideConditions bodyTree.root.side)
            continuationTree.root.side
          canonical := .jp bodyTree.root.canonical
            continuationTree.root.canonical
        } bodyTree continuationTree
    | jmp targetScoped argumentsScoped =>
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            _ _ :=
          .jmp (scopeIndex_scopedJoinForward index targetScoped)
            (scopeIndex_argsForward index argumentsScoped)
        exact .jmp {
          structural := .aligned (.jmp _ _)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .jmp targetScoped targetScoped
            argumentsScoped argumentsScoped
          canonical := .jmp
        }
    | @cases index cases discrScoped normalization alternatives =>
        have alternativesTree :=
          alternatives.certificateAlts (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            _ _ :=
          .cases (scopeIndex_scopedFVarForward index discrScoped)
            (fun _ => chooseAlt_related
              (certificateAlts_alphaForward alternativesTree))
        exact .cases {
          structural := certificateAlts_structuralCases alternativesTree
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .cases discrScoped discrScoped normalization normalization
            (certificateAlts_ctorSide alternativesTree
              normalization.deterministic)
            (certificateAlts_defaultSide alternativesTree
              normalization.deterministic)
          canonical := .cases
            (fun alt member =>
              certificateAlts_canonical alternativesTree member)
        } alternativesTree
    | ret resultScoped =>
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            _ _ :=
          .terminal (.ret (scopeIndex_scopedFVarForward index resultScoped))
        exact .ret {
          structural := .aligned (.return _)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .ret resultScoped resultScoped
          canonical := .ret
        }
    | @unreach index type =>
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.unreach type) (.unreach type) :=
          .terminal .unreachable
        exact .unreach {
          structural := .aligned (.unreach _)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .unreachable
          canonical := .unreach
        }
    | @oset field index rest object fieldIndex
        objectScoped fieldScoped continuation =>
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.oset object fieldIndex field rest)
            (.oset object fieldIndex field rest) :=
          .oset (scopeIndex_scopedFVarForward index objectScoped)
            (scopeIndex_argForward index fieldScoped)
            continuationTree.root.alpha.forward
        exact .oset {
          structural := .aligned (.oset _ _ _
            continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .oset objectScoped objectScoped fieldScoped fieldScoped
            continuationTree.root.side
          canonical := .oset continuationTree.root.canonical
        } continuationTree
    | @uset index rest object fieldIndex field
        objectScoped fieldScoped continuation =>
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.uset object fieldIndex field rest)
            (.uset object fieldIndex field rest) :=
          .uset (scopeIndex_scopedFVarForward index objectScoped)
            (scopeIndex_scopedFVarForward index fieldScoped)
            continuationTree.root.alpha.forward
        exact .uset {
          structural := .aligned (.uset _ _ _
            continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .uset objectScoped objectScoped fieldScoped fieldScoped
            continuationTree.root.side
          canonical := .uset continuationTree.root.canonical
        } continuationTree
    | @sset index rest object width offset field type
        objectScoped fieldScoped continuation =>
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.sset object width offset field type rest)
            (.sset object width offset field type rest) :=
          .sset (scopeIndex_scopedFVarForward index objectScoped)
            (scopeIndex_scopedFVarForward index fieldScoped)
            continuationTree.root.alpha.forward
        exact .sset {
          structural := .aligned (.sset _ _ _ _ _
            continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .sset objectScoped objectScoped fieldScoped fieldScoped
            continuationTree.root.side
          canonical := .sset continuationTree.root.canonical
        } continuationTree
    | @setTag index rest object tag objectScoped continuation =>
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.setTag object tag rest) (.setTag object tag rest) :=
          .setTag (scopeIndex_scopedFVarForward index objectScoped)
            continuationTree.root.alpha.forward
        exact .setTag {
          structural := .aligned (.setTag _ _
            continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .setTag objectScoped objectScoped continuationTree.root.side
          canonical := .setTag continuationTree.root.canonical
        } continuationTree
    | @inc index rest object amount check persistent
        objectScoped continuation =>
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.inc object amount check persistent rest)
            (.inc object amount check persistent rest) :=
          .inc (scopeIndex_scopedFVarForward index objectScoped)
            continuationTree.root.alpha.forward
        exact .inc {
          structural := .aligned (.inc _ _ _ _
            continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .inc objectScoped objectScoped continuationTree.root.side
          canonical := .inc continuationTree.root.canonical
        } continuationTree
    | @dec index rest object amount check persistent objects
        objectScoped continuation =>
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.dec object amount check persistent objects rest)
            (.dec object amount check persistent objects rest) :=
          .dec (scopeIndex_scopedFVarForward index objectScoped)
            continuationTree.root.alpha.forward
        exact .dec {
          structural := .aligned (.dec _ _ _ _ _
            continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .dec objectScoped objectScoped continuationTree.root.side
          canonical := .dec continuationTree.root.canonical
        } continuationTree
    | @del index rest object objectScoped continuation =>
        have continuationTree :=
          continuation.certificateTree (validCase := validCase)
        have forward : CodeRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (.del object rest) (.del object rest) :=
          .del (scopeIndex_scopedFVarForward index objectScoped)
            continuationTree.root.alpha.forward
        exact .del {
          structural := .aligned (.del _ continuationTree.root.structural)
          alpha := {
            forward
            backward := index.codeRelated_symm forward
          }
          side := .del objectScoped objectScoped continuationTree.root.side
          canonical := .del continuationTree.root.canonical
        } continuationTree

  termination_by sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals apply caseAlts_sizeOf_lt

  theorem ScopedCodeWellFormedAlts.certificateAlts
      (wellFormed : ScopedCodeWellFormedAlts index alts) :
      ScopedCodeTargetCertificateAlts validCase index alts := by
    cases wellFormed with
    | nil => exact .nil
    | ctor body rest =>
        exact .ctor (body.certificateTree (validCase := validCase))
          (rest.certificateAlts (validCase := validCase))
    | default body rest =>
        exact .default (body.certificateTree (validCase := validCase))
          (rest.certificateAlts (validCase := validCase))

  termination_by sizeOf alts
  decreasing_by all_goals simp_all <;> omega

end

theorem ProgramWellFormed.namesUnique
    (wellFormed : ProgramWellFormed program) : program.NamesUnique := by
  cases wellFormed.phase with
  | impure namesUnique _ => exact namesUnique

theorem ProgramWellFormed.hygienic
    (wellFormed : ProgramWellFormed program) : program.ImpureHygienic := by
  cases wellFormed.phase with
  | impure _ hygienic => exact hygienic

theorem ProgramWellFormed.declarationHygienic
    (wellFormed : ProgramWellFormed program)
    {declaration : LCNF.Decl .impure}
    (member : declaration ∈ program.decls.toList) :
    ImpureHygiene.declHygienic declaration = true := by
  have allHygienic := wellFormed.hygienic
  unfold Program.ImpureHygienic at allHygienic
  rw [Array.all_eq_true'] at allHygienic
  exact allHygienic declaration (Array.mem_def.mpr member)

theorem ProgramWellFormed.declaration
    (wellFormed : ProgramWellFormed program)
    {declaration : LCNF.Decl .impure}
    (member : declaration ∈ program.decls.toList) :
    DeclWellFormed declaration := {
  hygienic := wellFormed.declarationHygienic member
  normalization := wellFormed.normalization declaration member
  canonical := wellFormed.canonical declaration member
}

/-- Assemble the public premise from the shared phase checker and the two
pass-specific compiler-output invariants. -/
theorem ProgramWellFormed.ofCompilerInvariants
    (phase : WellFormedAt .impure program)
    (normalization : ProgramNormalizationTree program)
    (canonical : ProgramRuntimeTypesCanonical program) :
    ProgramWellFormed program := {
  phase
  normalization
  canonical
}

end Fir.LeanIR.Passes.SimpCaseWellFormed
