import Fir.LeanIR.Passes.SimpCaseAlphaBridge
import Fir.LeanIR.Passes.AlphaEqvSideConditions

namespace Fir.LeanIR.Passes.SimpCaseScopedBridge

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.SimpCaseCompilerBridge
open Fir.LeanIR.Passes.SimpCaseRelation

/-!
The original `CaseBoundarySound` is intentionally scope-free because its
target is the structural `CodeRel`. Alpha-equivalent case folding needs more
information: the executable checker and `AlphaEqv.CodeRelated` interpret a
right-to-left renaming under separate variable and join scopes.

This module supplies that missing recursive-traversal interface. It does not
change `CodeRel`; instead, clients choose a scope-indexed relation and prove
the ordinary constructor laws plus the case-node boundary they need.
-/

/-- Bidirectional alpha indices at one recursive code position. The source is
also the structural intermediate's side of the later alpha relation. -/
structure ScopeIndex where
  forwardRho : FVarIdMap FVarId
  backwardRho : FVarIdMap FVarId
  forwardEmpty : ResolverEquivalent forwardRho {}
  backwardEmpty : ResolverEquivalent backwardRho {}
  sourceScope : List FVarId
  targetScope : List FVarId
  scopesEq : sourceScope = targetScope
  sourceJoins : List FVarId
  targetJoins : List FVarId
  joinsEq : sourceJoins = targetJoins

/-- Empty declaration-body index. -/
def ScopeIndex.empty : ScopeIndex where
  forwardRho := {}
  backwardRho := {}
  forwardEmpty := resolverEquivalent_refl {}
  backwardEmpty := resolverEquivalent_refl {}
  sourceScope := []
  targetScope := []
  scopesEq := rfl
  sourceJoins := []
  targetJoins := []
  joinsEq := rfl

/-- Descend through an unchanged ordinary binder. -/
def ScopeIndex.pushVar (index : ScopeIndex) (fvarId : FVarId) : ScopeIndex := {
  index with
  forwardRho := index.forwardRho.insert fvarId fvarId
  backwardRho := index.backwardRho.insert fvarId fvarId
  forwardEmpty := index.forwardEmpty.insertSelf_of_empty fvarId
  backwardEmpty := index.backwardEmpty.insertSelf_of_empty fvarId
  sourceScope := fvarId :: index.sourceScope
  targetScope := fvarId :: index.targetScope
  scopesEq := congrArg (fun scope => fvarId :: scope) index.scopesEq
}

/-- Descend through an unchanged join binder. -/
def ScopeIndex.pushJoin (index : ScopeIndex) (fvarId : FVarId) : ScopeIndex := {
  index with
  forwardRho := index.forwardRho.insert fvarId fvarId
  backwardRho := index.backwardRho.insert fvarId fvarId
  forwardEmpty := index.forwardEmpty.insertSelf_of_empty fvarId
  backwardEmpty := index.backwardEmpty.insertSelf_of_empty fvarId
  sourceJoins := fvarId :: index.sourceJoins
  targetJoins := fvarId :: index.targetJoins
  joinsEq := congrArg (fun joins => fvarId :: joins) index.joinsEq
}

/-- Function and join-body parameters enter scope from left to right. -/
def ScopeIndex.pushParamList :
    ScopeIndex → List (LCNF.Param .impure) → ScopeIndex
  | index, [] => index
  | index, param :: rest =>
      (index.pushVar param.fvarId).pushParamList rest

def ScopeIndex.pushParams (index : ScopeIndex)
    (params : Array (LCNF.Param .impure)) : ScopeIndex :=
  index.pushParamList params.toList

/-- Swap source and target and select the reverse renaming as the forward
direction. This lets directional helper lemmas serve both alpha orientations. -/
def ScopeIndex.reverse (index : ScopeIndex) : ScopeIndex where
  forwardRho := index.backwardRho
  backwardRho := index.forwardRho
  forwardEmpty := index.backwardEmpty
  backwardEmpty := index.forwardEmpty
  sourceScope := index.targetScope
  targetScope := index.sourceScope
  scopesEq := index.scopesEq.symm
  sourceJoins := index.targetJoins
  targetJoins := index.sourceJoins
  joinsEq := index.joinsEq.symm

@[simp] theorem ScopeIndex.reverse_pushVar
    (index : ScopeIndex) (fvarId : FVarId) :
    (index.pushVar fvarId).reverse = (index.reverse).pushVar fvarId := by
  rfl

@[simp] theorem ScopeIndex.reverse_pushJoin
    (index : ScopeIndex) (fvarId : FVarId) :
    (index.pushJoin fvarId).reverse = (index.reverse).pushJoin fvarId := by
  rfl

@[simp] theorem ScopeIndex.reverse_pushParamList
    (index : ScopeIndex) (params : List (LCNF.Param .impure)) :
    (index.pushParamList params).reverse =
      (index.reverse).pushParamList params := by
  induction params generalizing index with
  | nil => rfl
  | cons param rest ih =>
      simp [ScopeIndex.pushParamList, ih]

@[simp] theorem ScopeIndex.reverse_pushParams
    (index : ScopeIndex) (params : Array (LCNF.Param .impure)) :
    (index.pushParams params).reverse = (index.reverse).pushParams params := by
  simp [ScopeIndex.pushParams]

/-- The audited upstream comparison can be replayed under the forward resolver
at every recursive scope index because self-renamings are observationally
empty. The bridge remains an explicit parameter here. -/
theorem ScopeIndex.localAcceptsAtForward_of_upstream
    (index : ScopeIndex) (bridge : UpstreamBridge)
    (left right : LCNF.Code .impure)
    (accepted : left.alphaEqv right = true) :
    Local.AcceptsAt index.forwardRho left right :=
  localAcceptsAt_of_resolverEquivalent_empty index.forwardEmpty left right
    (bridge.accepted left right accepted)

/-- The same audited comparison is valid under the reverse outer resolver.
This does not reverse the compared code; reversal is a separate relational
obligation. -/
theorem ScopeIndex.localAcceptsAtBackward_of_upstream
    (index : ScopeIndex) (bridge : UpstreamBridge)
    (left right : LCNF.Code .impure)
    (accepted : left.alphaEqv right = true) :
    Local.AcceptsAt index.backwardRho left right :=
  localAcceptsAt_of_resolverEquivalent_empty index.backwardEmpty left right
    (bridge.accepted left right accepted)

theorem ScopeIndex.variableBijection (index : ScopeIndex) :
    RenamingBijection index.forwardRho index.backwardRho
      index.sourceScope index.targetScope :=
  RenamingBijection.of_resolverEquivalent_empty
    index.forwardEmpty index.backwardEmpty index.scopesEq

theorem ScopeIndex.joinBijection (index : ScopeIndex) :
    RenamingBijection index.forwardRho index.backwardRho
      index.sourceJoins index.targetJoins :=
  RenamingBijection.of_resolverEquivalent_empty
    index.forwardEmpty index.backwardEmpty index.joinsEq

/-- Every forward scoped alpha relation at a traversal index has the required
reverse orientation; binder freshness inside `CodeRelated` preserves the
paired inverse maps recursively. -/
theorem ScopeIndex.codeRelated_symm
    (index : ScopeIndex)
    (related : CodeRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope left right) :
    CodeRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope right left :=
  AlphaEqv.codeRelated_symm index.variableBijection index.joinBijection related

/-- Full reflexive side-condition certificate at one scoped endpoint. Unlike
`ScopedAlphaBireflexive`, this records nested case normalization and the exact
runtime-observed type metadata required by local alpha soundness. -/
def ScopedCodeSideReflexive (index : ScopeIndex)
    (code : LCNF.Code .impure) : Prop :=
  CodeSideConditions
    (leftJoins := index.sourceJoins) (rightJoins := index.sourceJoins)
    index.forwardRho index.sourceScope index.sourceScope code code

/-- The equal source/target scope invariant lets one endpoint certificate be
viewed at the target side of a cross-code comparison. -/
theorem ScopedCodeSideReflexive.target
    (side : ScopedCodeSideReflexive index code) :
    CodeSideConditions
      (leftJoins := index.targetJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.targetScope index.targetScope code code := by
  rw [← index.scopesEq, ← index.joinsEq]
  exact side

/-- Selector determinism is inherited by any subtable. -/
theorem caseTableDeterministic_of_subset
    (deterministic : CaseTableDeterministic source)
    (subset : ∀ alt, alt ∈ target → alt ∈ source) :
    CaseTableDeterministic target where
  ctor := by
    intro tag left right leftHas rightHas
    rcases leftHas with ⟨leftInfo, leftMember, leftTag⟩
    rcases rightHas with ⟨rightInfo, rightMember, rightTag⟩
    exact deterministic.ctor tag left right
      ⟨leftInfo, subset _ leftMember, leftTag⟩
      ⟨rightInfo, subset _ rightMember, rightTag⟩
  default := by
    intro left right leftHas rightHas
    exact deterministic.default left right
      (subset _ leftHas) (subset _ rightHas)

/-- Array filtering preserves selector determinism. -/
theorem caseTableDeterministic_filter
    (alts : Array (LCNF.Alt .impure))
    (predicate : LCNF.Alt .impure → Bool)
    (deterministic : CaseTableDeterministic alts.toList) :
    CaseTableDeterministic (alts.filter predicate).toList :=
  caseTableDeterministic_of_subset deterministic (by
    intro alt member
    exact Array.mem_def.mp
      (Array.mem_of_mem_filter (Array.mem_def.mpr member)))

/-- Appending the sole default to a table that had none preserves selector
determinism. -/
theorem caseTableDeterministic_pushDefault
    (alts : Array (LCNF.Alt .impure))
    (body : LCNF.Code .impure)
    (deterministic : CaseTableDeterministic alts.toList)
    (noDefault : ∀ code, ¬HasDefaultAlt code alts.toList) :
    CaseTableDeterministic (alts.push (.default body)).toList where
  ctor := by
    intro tag left right leftHas rightHas
    apply deterministic.ctor tag left right
    · rcases leftHas with ⟨info, member, selected⟩
      refine ⟨info, ?_, selected⟩
      simpa [Array.toList_push] using member
    · rcases rightHas with ⟨info, member, selected⟩
      refine ⟨info, ?_, selected⟩
      simpa [Array.toList_push] using member
  default := by
    intro left right leftHas rightHas
    have leftEq : left = body := by
      unfold HasDefaultAlt at leftHas
      rw [Array.toList_push] at leftHas
      simp only [List.mem_append, List.mem_singleton] at leftHas
      rcases leftHas with old | appended
      · exact False.elim (noDefault left old)
      · exact LCNF.Alt.default.inj appended
    have rightEq : right = body := by
      unfold HasDefaultAlt at rightHas
      rw [Array.toList_push] at rightHas
      simp only [List.mem_append, List.mem_singleton] at rightHas
      rcases rightHas with old | appended
      · exact False.elim (noDefault right old)
      · exact LCNF.Alt.default.inj appended
    exact leftEq.trans rightEq.symm

/-- The compiler's default-fold calculation preserves the selector
determinism needed by executable alpha equivalence. -/
theorem caseTableNormalization_shadowAddDefaultAlt
    (normalization : CaseTableNormalizationInvariant alts) :
    CaseTableNormalizationInvariant (shadowAddDefaultAlt alts) := by
  constructor
  unfold shadowAddDefaultAlt
  split
  · exact normalization.deterministic
  · rename_i active
    rw [Bool.or_eq_true] at active
    split
    rename_i pair representative occurrences selectedPair
    split
    · exact normalization.deterministic
    · rename_i folded
      have noDefaultSource : ∀ code,
          ¬HasDefaultAlt code alts.toList := by
        intro code hasDefault
        have member : (.default code : LCNF.Alt .impure) ∈ alts :=
          Array.mem_def.mpr hasDefault
        apply active
        exact Or.inr (Array.any_eq_true'.mpr
          ⟨.default code, member, rfl⟩)
      have filteredDeterministic : CaseTableDeterministic
          (alts.filter fun alt =>
            !alt.getCode.alphaEqv representative.getCode).toList :=
        caseTableDeterministic_filter _ _ normalization.deterministic
      have noFilteredDefault : ∀ code,
          ¬HasDefaultAlt code
            (alts.filter fun alt =>
              !alt.getCode.alphaEqv representative.getCode).toList := by
        intro code hasDefault
        apply noDefaultSource code
        exact Array.mem_def.mp
          (Array.mem_of_mem_filter (Array.mem_def.mpr hasDefault))
      exact caseTableDeterministic_pushDefault _ _ filteredDeterministic
        noFilteredDefault

/-- Unreachable-arm filtering and default folding preserve table
normalization together. -/
theorem caseTableNormalization_shadowPrepareAlts
    (normalization : CaseTableNormalizationInvariant cases.alts) :
    CaseTableNormalizationInvariant (shadowPrepareAlts cases) :=
  caseTableNormalization_shadowAddDefaultAlt {
    deterministic := caseTableDeterministic_filter _ _
      normalization.deterministic
  }

/-- A constructor body in a successful pointwise traversal has a source body
with the same selector metadata and the exact recursive run equation. -/
theorem exists_source_ctor_of_mem_mapM_shadowAltUsing
    {recurse : LCNF.Code .impure → Option (LCNF.Code .impure)}
    {source target : List (LCNF.Alt .impure)}
    (run : source.mapM (shadowAltUsing? recurse) = some target)
    (member : (.ctorAlt info targetCode : LCNF.Alt .impure) ∈ target) :
    ∃ sourceCode,
      (.ctorAlt info sourceCode : LCNF.Alt .impure) ∈ source ∧
      recurse sourceCode = some targetCode := by
  induction source generalizing target with
  | nil =>
      simp at run
      subst target
      simp at member
  | cons alt rest ih =>
      cases alt with
      | ctorAlt sourceInfo sourceCode =>
          cases bodyRun : recurse sourceCode with
          | none => simp [shadowAltUsing?, bodyRun] at run
          | some transformed =>
              cases restRun : rest.mapM (shadowAltUsing? recurse) with
              | none => simp [shadowAltUsing?, bodyRun, restRun] at run
              | some transformedRest =>
                  simp [shadowAltUsing?, bodyRun, restRun] at run
                  subst target
                  simp only [List.mem_cons] at member
                  rcases member with head | tail
                  · cases head
                    exact ⟨sourceCode, List.mem_cons_self, bodyRun⟩
                  · rcases ih restRun tail with ⟨code, codeMem, codeRun⟩
                    exact ⟨code, List.mem_cons_of_mem _ codeMem, codeRun⟩
      | default sourceCode =>
          cases bodyRun : recurse sourceCode with
          | none => simp [shadowAltUsing?, bodyRun] at run
          | some transformed =>
              cases restRun : rest.mapM (shadowAltUsing? recurse) with
              | none => simp [shadowAltUsing?, bodyRun, restRun] at run
              | some transformedRest =>
                  simp [shadowAltUsing?, bodyRun, restRun] at run
                  subst target
                  simp only [List.mem_cons] at member
                  rcases member with head | tail
                  · cases head
                  · rcases ih restRun tail with ⟨code, codeMem, codeRun⟩
                    exact ⟨code, List.mem_cons_of_mem _ codeMem, codeRun⟩
      | alt _ _ _ impossible => nomatch impossible

/-- Default-body counterpart of
`exists_source_ctor_of_mem_mapM_shadowAltUsing`. -/
theorem exists_source_default_of_mem_mapM_shadowAltUsing
    {recurse : LCNF.Code .impure → Option (LCNF.Code .impure)}
    {source target : List (LCNF.Alt .impure)}
    (run : source.mapM (shadowAltUsing? recurse) = some target)
    (member : (.default targetCode : LCNF.Alt .impure) ∈ target) :
    ∃ sourceCode,
      (.default sourceCode : LCNF.Alt .impure) ∈ source ∧
      recurse sourceCode = some targetCode := by
  induction source generalizing target with
  | nil =>
      simp at run
      subst target
      simp at member
  | cons alt rest ih =>
      cases alt with
      | ctorAlt sourceInfo sourceCode =>
          cases bodyRun : recurse sourceCode with
          | none => simp [shadowAltUsing?, bodyRun] at run
          | some transformed =>
              cases restRun : rest.mapM (shadowAltUsing? recurse) with
              | none => simp [shadowAltUsing?, bodyRun, restRun] at run
              | some transformedRest =>
                  simp [shadowAltUsing?, bodyRun, restRun] at run
                  subst target
                  simp only [List.mem_cons] at member
                  rcases member with head | tail
                  · cases head
                  · rcases ih restRun tail with ⟨code, codeMem, codeRun⟩
                    exact ⟨code, List.mem_cons_of_mem _ codeMem, codeRun⟩
      | default sourceCode =>
          cases bodyRun : recurse sourceCode with
          | none => simp [shadowAltUsing?, bodyRun] at run
          | some transformed =>
              cases restRun : rest.mapM (shadowAltUsing? recurse) with
              | none => simp [shadowAltUsing?, bodyRun, restRun] at run
              | some transformedRest =>
                  simp [shadowAltUsing?, bodyRun, restRun] at run
                  subst target
                  simp only [List.mem_cons] at member
                  rcases member with head | tail
                  · cases head
                    exact ⟨sourceCode, List.mem_cons_self, bodyRun⟩
                  · rcases ih restRun tail with ⟨code, codeMem, codeRun⟩
                    exact ⟨code, List.mem_cons_of_mem _ codeMem, codeRun⟩
      | alt _ _ _ impossible => nomatch impossible

/-- Deterministic recursive syntax transformation preserves selector
determinism. Equal source bodies are passed to the same pure `recurse`
function, so duplicate selectors still select definitionally equal targets. -/
theorem caseTableNormalization_mapM_shadowAltUsing
    {recurse : LCNF.Code .impure → Option (LCNF.Code .impure)}
    {source target : List (LCNF.Alt .impure)}
    (run : source.mapM (shadowAltUsing? recurse) = some target)
    (normalization : CaseTableNormalizationInvariant source.toArray) :
    CaseTableNormalizationInvariant target.toArray := by
  constructor
  change CaseTableDeterministic target
  constructor
  · intro tag left right leftHas rightHas
    rcases leftHas with ⟨leftInfo, leftMember, leftTag⟩
    rcases rightHas with ⟨rightInfo, rightMember, rightTag⟩
    rcases exists_source_ctor_of_mem_mapM_shadowAltUsing run leftMember with
      ⟨leftSource, leftSourceMember, leftRun⟩
    rcases exists_source_ctor_of_mem_mapM_shadowAltUsing run rightMember with
      ⟨rightSource, rightSourceMember, rightRun⟩
    have sourceEq := normalization.deterministic.ctor tag
      leftSource rightSource
      ⟨leftInfo, leftSourceMember, leftTag⟩
      ⟨rightInfo, rightSourceMember, rightTag⟩
    subst rightSource
    rw [leftRun] at rightRun
    exact Option.some.inj rightRun
  · intro left right leftHas rightHas
    rcases exists_source_default_of_mem_mapM_shadowAltUsing run leftHas with
      ⟨leftSource, leftSourceMember, leftRun⟩
    rcases exists_source_default_of_mem_mapM_shadowAltUsing run rightHas with
      ⟨rightSource, rightSourceMember, rightRun⟩
    have sourceEq := normalization.deterministic.default
      leftSource rightSource leftSourceMember rightSourceMember
    subst rightSource
    rw [leftRun] at rightRun
    exact Option.some.inj rightRun

abbrev ScopedCodeRelation :=
  ScopeIndex → LCNF.Code .impure → LCNF.Code .impure → Prop

/-- Closure laws needed to lift a relation through every non-case constructor
of the transparent recursive traversal. Binder cases expose their updated
scope indices to recursive premises. -/
structure ScopedTraversalLaws (relation : ScopedCodeRelation) : Prop where
  letE : ∀ {index declaration left right},
    relation (index.pushVar declaration.fvarId) left right →
      relation index (.let declaration left) (.let declaration right)
  jp : ∀ {index fvarId binderName params type
      leftBody rightBody leftContinuation rightContinuation},
    relation (index.pushParams params) leftBody rightBody →
    relation (index.pushJoin fvarId) leftContinuation rightContinuation →
      relation index
        (.jp (.mk fvarId binderName params type leftBody) leftContinuation)
        (.jp (.mk fvarId binderName params type rightBody) rightContinuation)
  jmp : ∀ index fvarId args,
    relation index (.jmp fvarId args) (.jmp fvarId args)
  ret : ∀ index fvarId,
    relation index (.return fvarId) (.return fvarId)
  unreach : ∀ index type,
    relation index (.unreach type) (.unreach type)
  oset : ∀ {index fvarId fieldIndex value left right},
    relation index left right →
      relation index (.oset fvarId fieldIndex value left)
        (.oset fvarId fieldIndex value right)
  uset : ∀ {index fvarId fieldIndex value left right},
    relation index left right →
      relation index (.uset fvarId fieldIndex value left)
        (.uset fvarId fieldIndex value right)
  sset : ∀ {index fvarId width offset value type left right},
    relation index left right →
      relation index (.sset fvarId width offset value type left)
        (.sset fvarId width offset value type right)
  setTag : ∀ {index fvarId tag left right},
    relation index left right →
      relation index (.setTag fvarId tag left) (.setTag fvarId tag right)
  inc : ∀ {index fvarId amount check persistent left right},
    relation index left right →
      relation index (.inc fvarId amount check persistent left)
        (.inc fvarId amount check persistent right)
  dec : ∀ {index fvarId amount check persistent objects left right},
    relation index left right →
      relation index (.dec fvarId amount check persistent objects left)
        (.dec fvarId amount check persistent objects right)
  del : ∀ {index fvarId left right},
    relation index left right →
      relation index (.del fvarId left) (.del fvarId right)

/-- Scope-aware replacement for the case-node premise. -/
def ScopedCaseBoundarySound (relation : ScopedCodeRelation) : Prop :=
  ∀ fuel index cases target,
    shadowCode? (fuel + 1) (.cases cases) = some target →
      relation index (.cases cases) target

/-- One concrete scoped case result, useful as a regression boundary without
claiming the universal compiler contract. -/
def ScopedCaseBoundaryAt (relation : ScopedCodeRelation)
    (index : ScopeIndex) (fuel : Nat) (cases : LCNF.Cases .impure)
    (target : LCNF.Code .impure) : Prop :=
  shadowCode? (fuel + 1) (.cases cases) = some target →
    relation index (.cases cases) target

/-- The transparent recursive traversal lifts any scope-indexed relation that
is closed under ordinary constructors and supplied at case nodes. -/
theorem shadowCode_scopedRelated
    (laws : ScopedTraversalLaws relation)
    (caseSound : ScopedCaseBoundarySound relation)
    (run : shadowCode? fuel source = some target) :
    relation index source target := by
  induction fuel generalizing index source target with
  | zero =>
      cases source <;> simp [shadowCode?] at run
      · subst target
        exact laws.jmp index _ _
      · subst target
        exact laws.ret index _
      · subst target
        exact laws.unreach index _
  | succ fuel ih =>
      cases source with
      | «let» declaration continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.letE (ih continuationRun)
      | «fun» declaration continuation impossible => nomatch impossible
      | jp declaration continuation =>
          cases declaration with
          | mk fvarId binderName params type body =>
              simp only [shadowCode?] at run
              cases bodyRun : shadowCode? fuel body with
              | none => simp [bodyRun] at run
              | some transformedBody =>
                  cases continuationRun : shadowCode? fuel continuation with
                  | none => simp [bodyRun, continuationRun] at run
                  | some transformedContinuation =>
                      simp [bodyRun, continuationRun] at run
                      subst target
                      exact laws.jp (ih bodyRun) (ih continuationRun)
      | jmp fvarId args =>
          simp [shadowCode?] at run
          subst target
          exact laws.jmp index fvarId args
      | cases cases => exact caseSound fuel index cases target run
      | «return» fvarId =>
          simp [shadowCode?] at run
          subst target
          exact laws.ret index fvarId
      | unreach type =>
          simp [shadowCode?] at run
          subst target
          exact laws.unreach index type
      | oset fvarId fieldIndex value continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.oset (ih continuationRun)
      | uset fvarId fieldIndex value continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.uset (ih continuationRun)
      | sset fvarId width offset value type continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.sset (ih continuationRun)
      | setTag fvarId tag continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.setTag (ih continuationRun)
      | inc fvarId amount check persistent continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.inc (ih continuationRun)
      | dec fvarId amount check persistent objects continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.dec (ih continuationRun)
      | del fvarId continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.del (ih continuationRun)

/-- One recursively transformed alternative. Constructor metadata is
unchanged by `shadowCode?`; only the alternative body follows the selected
scoped relation. -/
inductive ScopedAltRelated (relation : ScopedCodeRelation)
    (index : ScopeIndex) :
    LCNF.Alt .impure → LCNF.Alt .impure → Prop where
  | ctor (body : relation index left right) :
      ScopedAltRelated relation index
        (.ctorAlt info left) (.ctorAlt info right)
  | default (body : relation index left right) :
      ScopedAltRelated relation index (.default left) (.default right)

abbrev ScopedAltsRelated (relation : ScopedCodeRelation)
    (index : ScopeIndex) :=
  ListRel (ScopedAltRelated relation index)

/-- The nonrecursive case-kernel obligation. Its first premise is the exact
successful recursive alternative traversal; its second premise exposes the
proof relation already established for every branch. Unlike
`ScopedCaseBoundarySound`, this interface contains no recursive proof
obligation of its own. -/
structure ScopedCaseKernelLaws (relation : ScopedCodeRelation) : Prop where
  simplify : ∀ {fuel : Nat} {index : ScopeIndex} {typeName : Name}
      {resultType : Expr} {discr : FVarId}
      {sourceAlts : Array (LCNF.Alt .impure)}
      {targetAlts : List (LCNF.Alt .impure)},
    sourceAlts.toList.mapM (shadowAltUsing? (shadowCode? fuel)) =
        some targetAlts →
    ScopedAltsRelated relation index sourceAlts.toList targetAlts →
    relation index
      (.cases (.mk typeName resultType discr sourceAlts))
      (shadowSimplifyCases
        (.mk typeName resultType discr targetAlts.toArray))

/-- Successful pointwise alternative traversal lifts body relations without
inspecting the case simplifier. -/
theorem scopedAltsRelated_of_mapM
    {recurse : LCNF.Code .impure → Option (LCNF.Code .impure)}
    {relation : ScopedCodeRelation} {index : ScopeIndex}
    {left right : List (LCNF.Alt .impure)}
    (body : ∀ {left right}, recurse left = some right →
      relation index left right)
    (run : left.mapM (shadowAltUsing? recurse) = some right) :
    ScopedAltsRelated relation index left right := by
  induction left generalizing right with
  | nil =>
      simp at run
      subst right
      exact .nil
  | cons alt rest ih =>
      cases alt with
      | ctorAlt info code =>
          cases bodyRun : recurse code with
          | none => simp [shadowAltUsing?, bodyRun] at run
          | some transformed =>
              cases restRun : rest.mapM (shadowAltUsing? recurse) with
              | none =>
                  simp [shadowAltUsing?, bodyRun, restRun] at run
              | some transformedRest =>
                  simp [shadowAltUsing?, bodyRun, restRun] at run
                  subst right
                  exact .cons (.ctor (body bodyRun)) (ih restRun)
      | default code =>
          cases bodyRun : recurse code with
          | none => simp [shadowAltUsing?, bodyRun] at run
          | some transformed =>
              cases restRun : rest.mapM (shadowAltUsing? recurse) with
              | none =>
                  simp [shadowAltUsing?, bodyRun, restRun] at run
              | some transformedRest =>
                  simp [shadowAltUsing?, bodyRun, restRun] at run
                  subst right
                  exact .cons (.default (body bodyRun)) (ih restRun)
      | alt _ _ _ impossible => nomatch impossible

/-- Recursive shadow traversal from a genuinely local case-kernel law. This
is the admissibility-correct replacement for trying to prove an unconditional
case boundary from hygiene alone. -/
theorem shadowCode_scopedRelated_of_caseKernel
    (laws : ScopedTraversalLaws relation)
    (caseKernel : ScopedCaseKernelLaws relation)
    (run : shadowCode? fuel source = some target) :
    relation index source target := by
  induction fuel generalizing index source target with
  | zero =>
      cases source <;> simp [shadowCode?] at run
      · subst target
        exact laws.jmp index _ _
      · subst target
        exact laws.ret index _
      · subst target
        exact laws.unreach index _
  | succ fuel ih =>
      cases source with
      | «let» declaration continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.letE (ih continuationRun)
      | «fun» declaration continuation impossible => nomatch impossible
      | jp declaration continuation =>
          cases declaration with
          | mk fvarId binderName params type body =>
              simp only [shadowCode?] at run
              cases bodyRun : shadowCode? fuel body with
              | none => simp [bodyRun] at run
              | some transformedBody =>
                  cases continuationRun : shadowCode? fuel continuation with
                  | none => simp [bodyRun, continuationRun] at run
                  | some transformedContinuation =>
                      simp [bodyRun, continuationRun] at run
                      subst target
                      exact laws.jp (ih bodyRun) (ih continuationRun)
      | jmp fvarId args =>
          simp [shadowCode?] at run
          subst target
          exact laws.jmp index fvarId args
      | cases cases =>
          cases cases with
          | mk typeName resultType discr alts =>
              simp only [shadowCode?] at run
              cases altsRun : alts.toList.mapM
                  (shadowAltUsing? (shadowCode? fuel)) with
              | none => simp [altsRun] at run
              | some transformedAlts =>
                  simp [altsRun] at run
                  subst target
                  exact caseKernel.simplify altsRun
                    (scopedAltsRelated_of_mapM
                      (fun bodyRun => ih bodyRun) altsRun)
      | «return» fvarId =>
          simp [shadowCode?] at run
          subst target
          exact laws.ret index fvarId
      | unreach type =>
          simp [shadowCode?] at run
          subst target
          exact laws.unreach index type
      | oset fvarId fieldIndex value continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.oset (ih continuationRun)
      | uset fvarId fieldIndex value continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.uset (ih continuationRun)
      | sset fvarId width offset value type continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.sset (ih continuationRun)
      | setTag fvarId tag continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.setTag (ih continuationRun)
      | inc fvarId amount check persistent continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.inc (ih continuationRun)
      | dec fvarId amount check persistent objects continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.dec (ih continuationRun)
      | del fvarId continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact laws.del (ih continuationRun)

/-- The old recursive boundary implies the local kernel law. This direction
does not use the pointwise branch proof; the boundary already hides it. -/
theorem scopedCaseKernelLaws_of_boundary
    (caseSound : ScopedCaseBoundarySound relation) :
    ScopedCaseKernelLaws relation where
  simplify := by
    intro fuel index typeName resultType discr sourceAlts targetAlts
      altsRun branchRelations
    apply caseSound fuel index (.mk typeName resultType discr sourceAlts)
    simp [shadowCode?, altsRun]

/-- Conversely, ordinary traversal closure lifts the nonrecursive kernel law
to the universal recursive case boundary. -/
theorem scopedCaseBoundarySound_of_kernel
    (laws : ScopedTraversalLaws relation)
    (caseKernel : ScopedCaseKernelLaws relation) :
    ScopedCaseBoundarySound relation := by
  intro fuel index cases target run
  exact shadowCode_scopedRelated_of_caseKernel laws caseKernel run

theorem scopedCaseBoundarySound_iff_kernel
    (laws : ScopedTraversalLaws relation) :
    ScopedCaseBoundarySound relation ↔ ScopedCaseKernelLaws relation := by
  constructor
  · exact scopedCaseKernelLaws_of_boundary
  · exact scopedCaseBoundarySound_of_kernel laws

/-- The old structural relation is one scope-insensitive instance of the new
recursive traversal interface. -/
def StructuralScopedRelation
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun _ source target => CodeRel validCase source target

theorem structuralScopedTraversalLaws :
    ScopedTraversalLaws (StructuralScopedRelation validCase) where
  letE related := .aligned (.let _ related)
  jp body continuation := .aligned (.jp _ _ _ _ body continuation)
  jmp _ fvarId args := .aligned (.jmp fvarId args)
  ret _ fvarId := .aligned (.return fvarId)
  unreach _ type := .aligned (.unreach type)
  oset related := .aligned (.oset _ _ _ related)
  uset related := .aligned (.uset _ _ _ related)
  sset related := .aligned (.sset _ _ _ _ _ related)
  setTag related := .aligned (.setTag _ _ related)
  inc related := .aligned (.inc _ _ _ _ related)
  dec related := .aligned (.dec _ _ _ _ _ related)
  del related := .aligned (.del _ related)

theorem structuralScopedCaseBoundarySound
    (caseSound : CaseBoundarySound validCase) :
    ScopedCaseBoundarySound (StructuralScopedRelation validCase) := by
  intro fuel index cases target run
  exact caseSound fuel cases target run

/-- Conservative recovery of the existing structural traversal theorem. -/
theorem shadowCode_structuralRelated
    (caseSound : CaseBoundarySound validCase)
    (run : shadowCode? fuel source = some target) :
    StructuralScopedRelation validCase index source target :=
  shadowCode_scopedRelated structuralScopedTraversalLaws
    (structuralScopedCaseBoundarySound caseSound) run

/-- Semantic payload for a scoped case edge: first a non-lockstep structural
rewrite, then alpha equivalence in both orientations under the exact active
variable and join scopes. -/
structure ScopedCodeBifactor
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : LCNF.Code .impure) where
  middle : LCNF.Code .impure
  structural : CodeRel validCase source middle
  alphaForward : CodeRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope middle target
  alphaBackward : CodeRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope target middle

/-- Three-phase payload for compiler paths that perform a structural rewrite,
an alpha-changing rewrite, and another structural rewrite in one local
kernel call. The second structural leg is necessary when `addDefaultAlt`
creates a singleton which `simplifyCases` immediately eliminates. -/
structure ScopedCodeTrifactor
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : LCNF.Code .impure) where
  structuralMiddle : LCNF.Code .impure
  alphaMiddle : LCNF.Code .impure
  structuralBefore : CodeRel validCase source structuralMiddle
  alphaForward : CodeRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope
    structuralMiddle alphaMiddle
  alphaBackward : CodeRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope
    alphaMiddle structuralMiddle
  structuralAfter : CodeRel validCase alphaMiddle target

/-- Proposition-valued presentation of the corrected three-phase payload.
It is deliberately separate from `ScopedCodeFactored` until the generic
traversal and semantic composition layers consume the final structural leg. -/
def ScopedCodeThreePhased
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    Nonempty (ScopedCodeTrifactor validCase index source target)

theorem ScopedCodeTrifactor.threePhased
    (factor : ScopedCodeTrifactor validCase index source target) :
    ScopedCodeThreePhased validCase index source target :=
  ⟨factor⟩

/-- Honest local phase classification. Existing case paths remain the
two-phase structural/alpha factor; combined fold-and-eliminate paths carry
the additional final structural leg. -/
inductive ScopedCodePhaseFactor
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : LCNF.Code .impure) : Type where
  | twoPhase (factor : ScopedCodeBifactor validCase index source target)
  | threePhase (factor : ScopedCodeTrifactor validCase index source target)

def ScopedCodePhaseFactored
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    Nonempty (ScopedCodePhaseFactor validCase index source target)

theorem ScopedCodeBifactor.phaseFactored
    (factor : ScopedCodeBifactor validCase index source target) :
    ScopedCodePhaseFactored validCase index source target :=
  ⟨.twoPhase factor⟩

theorem ScopedCodeTrifactor.phaseFactored
    (factor : ScopedCodeTrifactor validCase index source target) :
    ScopedCodePhaseFactored validCase index source target :=
  ⟨.threePhase factor⟩

/-- Pad a two-phase result with an explicit final structural identity. A
genuine three-phase result is already normalized. -/
def ScopedCodePhaseFactor.toTrifactor
    (factor : ScopedCodePhaseFactor validCase index source target)
    (targetRefl : CodeRel validCase target target) :
    ScopedCodeTrifactor validCase index source target :=
  match factor with
  | .twoPhase factor => {
      structuralMiddle := factor.middle
      alphaMiddle := target
      structuralBefore := factor.structural
      alphaForward := factor.alphaForward
      alphaBackward := factor.alphaBackward
      structuralAfter := targetRefl
    }
  | .threePhase factor => factor

/-- Forget the final structural leg and expose the prefix consumed by the
existing structural/alpha constructor lifting proof. -/
def ScopedCodeTrifactor.beforeAlpha
    (factor : ScopedCodeTrifactor validCase index source target) :
    ScopedCodeBifactor validCase index source factor.alphaMiddle := {
  middle := factor.structuralMiddle
  structural := factor.structuralBefore
  alphaForward := factor.alphaForward
  alphaBackward := factor.alphaBackward
}

/-- A structural relation cannot rename the declaration at a leading value
binding. This small inversion lemma makes factor-order counterexamples
independent of dependent elimination over a larger evidence structure. -/
theorem codeRel_let_target_shape
    (related : CodeRel validCase (.let declaration continuation) target) :
    ∃ right, target = .let declaration right := by
  cases related with
  | aligned head =>
      cases head with
      | «let» declaration continuation => exact ⟨_, rfl⟩

/-- Proposition-valued presentation suitable for the generic scoped traversal
interface, with the structural intermediate existentially hidden. -/
def ScopedCodeFactored
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    Nonempty (ScopedCodeBifactor validCase index source target)

theorem ScopedCodeBifactor.factored
    (factor : ScopedCodeBifactor validCase index source target) :
    ScopedCodeFactored validCase index source target :=
  ⟨factor⟩

/-- Explicit lexical/hygiene evidence for one source code position. Both
directions are required because `ScopedCodeBifactor` records alpha equivalence
in both orientations. -/
structure ScopedAlphaBireflexive (index : ScopeIndex)
    (code : LCNF.Code .impure) : Prop where
  forward : CodeRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope code code
  backward : CodeRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope code code

/-- A phase factor together with the structural and alpha identities needed
to align its schedule with sibling subtrees and append later case rounds. -/
structure ScopedCodePhaseResult
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : LCNF.Code .impure) where
  factor : ScopedCodePhaseFactor validCase index source target
  targetRefl : CodeRel validCase target target
  targetAlpha : ScopedAlphaBireflexive index target

/-- Explicit endpoint identities needed to turn a local phase factor into a
traversal result. They are kept as evidence because neither structural nor
scoped alpha reflexivity is globally valid for arbitrary selectors/scopes. -/
structure ScopedCodeTargetIdentities
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (target : LCNF.Code .impure) : Prop where
  structural : CodeRel validCase target target
  alpha : ScopedAlphaBireflexive index target

/-- Endpoint identities together with the full side-condition certificate
needed by a later alpha-fold comparison. This parallel certificate keeps the
existing phase API stable while the stronger recursive path is threaded. -/
structure ScopedCodeTargetCertificate
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (target : LCNF.Code .impure) : Prop
    extends ScopedCodeTargetIdentities validCase index target where
  side : ScopedCodeSideReflexive index target

theorem ScopedCodePhaseResult.identities
    (result : ScopedCodePhaseResult validCase index source target) :
    ScopedCodeTargetIdentities validCase index target := {
  structural := result.targetRefl
  alpha := result.targetAlpha
}

/-- One ordinary phase result whose target retains the stronger endpoint
certificate instead of dropping normalization/runtime metadata. -/
structure ScopedCodePhaseCertifiedResult
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : LCNF.Code .impure) where
  result : ScopedCodePhaseResult validCase index source target
  targetSide : ScopedCodeSideReflexive index target

theorem ScopedCodePhaseCertifiedResult.certificate
    (result : ScopedCodePhaseCertifiedResult validCase index source target) :
    ScopedCodeTargetCertificate validCase index target := {
  structural := result.result.targetRefl
  alpha := result.result.targetAlpha
  side := result.targetSide
}

def ScopedCodePhaseResult.certify
    (result : ScopedCodePhaseResult validCase index source target)
    (side : ScopedCodeSideReflexive index target) :
    ScopedCodePhaseCertifiedResult validCase index source target := {
  result
  targetSide := side
}

def ScopedCodeBifactor.phaseResult
    (factor : ScopedCodeBifactor validCase index source target)
    (identities : ScopedCodeTargetIdentities validCase index target) :
    ScopedCodePhaseResult validCase index source target := {
  factor := .twoPhase factor
  targetRefl := identities.structural
  targetAlpha := identities.alpha
}

def ScopedCodeTrifactor.phaseResult
    (factor : ScopedCodeTrifactor validCase index source target)
    (identities : ScopedCodeTargetIdentities validCase index target) :
    ScopedCodePhaseResult validCase index source target := {
  factor := .threePhase factor
  targetRefl := identities.structural
  targetAlpha := identities.alpha
}

def ScopedCodePhaseResult.trifactor
    (result : ScopedCodePhaseResult validCase index source target) :
    ScopedCodeTrifactor validCase index source target :=
  result.factor.toTrifactor result.targetRefl

/-- Traversal-facing phase relation. Besides source hygiene it returns a
structural identity for the target, allowing independently transformed
children to be padded to the common structural/alpha/structural schedule. -/
def ScopedCodePhaseResultOnAlphaReflexive
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedAlphaBireflexive index source →
      Nonempty (ScopedCodePhaseResult validCase index source target)

theorem ScopedCodePhaseResult.phaseFactored
    (result : ScopedCodePhaseResult validCase index source target) :
    ScopedCodePhaseFactored validCase index source target :=
  ⟨result.factor⟩

/-- Identity phase round used to pad a shorter sibling trace. Both identity
proofs are explicit because neither selector-indexed structural reflexivity
nor scoped alpha reflexivity is valid without evidence. -/
def ScopedCodePhaseResult.identity
    (structural : CodeRel validCase code code)
    (alpha : ScopedAlphaBireflexive index code) :
    ScopedCodePhaseResult validCase index code code := {
  factor := .twoPhase {
    middle := code
    structural := structural
    alphaForward := alpha.forward
    alphaBackward := alpha.backward
  }
  targetRefl := structural
  targetAlpha := alpha
}

def ScopedCodeTargetCertificate.identity
    (certificate : ScopedCodeTargetCertificate validCase index code) :
    ScopedCodePhaseCertifiedResult validCase index code code := {
  result := .identity certificate.structural certificate.alpha
  targetSide := certificate.side
}

theorem scopedUnreachTargetIdentities
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (type : Expr) :
    ScopedCodeTargetIdentities validCase index (.unreach type) := {
  structural := .aligned (.unreach type)
  alpha := {
    forward := .terminal .unreachable
    backward := .terminal .unreachable
  }
}

theorem scopedUnreachTargetCertificate
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (type : Expr) :
    ScopedCodeTargetCertificate validCase index (.unreach type) := {
  structural := .aligned (.unreach type)
  alpha := {
    forward := .terminal .unreachable
    backward := .terminal .unreachable
  }
  side := .unreachable
}

/-- Nonempty sequence of local phase rounds. Nested case simplifiers append
rounds instead of trying to compress an unbounded trace back into one
two/three-phase factor. -/
inductive ScopedCodePhaseTrace
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :
    LCNF.Code .impure → LCNF.Code .impure → Type where
  | single (round : ScopedCodePhaseResult validCase index source target) :
      ScopedCodePhaseTrace validCase index source target
  | trans (round : ScopedCodePhaseResult validCase index source middle)
      (rest : ScopedCodePhaseTrace validCase index middle target) :
      ScopedCodePhaseTrace validCase index source target

theorem ScopedCodePhaseTrace.targetRefl
    (trace : ScopedCodePhaseTrace validCase index source target) :
    CodeRel validCase target target :=
  match trace with
  | .single round => round.targetRefl
  | .trans _ rest => rest.targetRefl

theorem ScopedCodePhaseTrace.targetAlpha
    (trace : ScopedCodePhaseTrace validCase index source target) :
    ScopedAlphaBireflexive index target :=
  match trace with
  | .single round => round.targetAlpha
  | .trans _ rest => rest.targetAlpha

def ScopedCodePhaseTrace.rounds
    (trace : ScopedCodePhaseTrace validCase index source target) : Nat :=
  match trace with
  | .single _ => 1
  | .trans _ rest => 1 + rest.rounds

/-- Sequential composition retains every intermediate phase round. -/
def ScopedCodePhaseTrace.append
    (left : ScopedCodePhaseTrace validCase index source middle)
    (right : ScopedCodePhaseTrace validCase index middle target) :
    ScopedCodePhaseTrace validCase index source target :=
  match left with
  | .single round => .trans round right
  | .trans round rest => .trans round (rest.append right)

/-- Append a semantically inert round, making endpoint padding explicit. -/
def ScopedCodePhaseTrace.pad
    (trace : ScopedCodePhaseTrace validCase index source target) :
    ScopedCodePhaseTrace validCase index source target :=
  trace.append (.single
    (.identity trace.targetRefl trace.targetAlpha))

theorem ScopedCodePhaseTrace.rounds_append
    (left : ScopedCodePhaseTrace validCase index source middle)
    (right : ScopedCodePhaseTrace validCase index middle target) :
    (left.append right).rounds = left.rounds + right.rounds := by
  induction left with
  | single round => rfl
  | trans round rest ih =>
      simp [ScopedCodePhaseTrace.append, ScopedCodePhaseTrace.rounds, ih,
        Nat.add_assoc]

@[simp] theorem ScopedCodePhaseTrace.rounds_pad
    (trace : ScopedCodePhaseTrace validCase index source target) :
    trace.pad.rounds = trace.rounds + 1 := by
  rw [ScopedCodePhaseTrace.pad, ScopedCodePhaseTrace.rounds_append]
  rfl

/-- Nonempty phase trace retaining the endpoint side certificate of every
round. This is the invariant-carrying counterpart of `ScopedCodePhaseTrace`. -/
inductive ScopedCodePhaseCertifiedTrace
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :
    LCNF.Code .impure → LCNF.Code .impure → Type where
  | single
      (round : ScopedCodePhaseCertifiedResult validCase index source target) :
      ScopedCodePhaseCertifiedTrace validCase index source target
  | trans
      (round : ScopedCodePhaseCertifiedResult validCase index source middle)
      (rest : ScopedCodePhaseCertifiedTrace validCase index middle target) :
      ScopedCodePhaseCertifiedTrace validCase index source target

def ScopedCodePhaseCertifiedTrace.forget
    (trace : ScopedCodePhaseCertifiedTrace validCase index source target) :
    ScopedCodePhaseTrace validCase index source target :=
  match trace with
  | .single round => .single round.result
  | .trans round rest => .trans round.result rest.forget

theorem ScopedCodePhaseCertifiedTrace.targetCertificate
    (trace : ScopedCodePhaseCertifiedTrace validCase index source target) :
    ScopedCodeTargetCertificate validCase index target :=
  match trace with
  | .single round => round.certificate
  | .trans _ rest => rest.targetCertificate

/-- A non-lockstep phase trace with a certified executable endpoint. Proof
intermediates remain ordinary phase rounds: independently chosen alpha
witnesses need not preserve duplicate-selector normalization, while the
actual deterministic compiler endpoint does. -/
structure ScopedCodePhaseEndpointCertifiedTrace
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : LCNF.Code .impure) : Type where
  trace : ScopedCodePhaseTrace validCase index source target
  targetSide : ScopedCodeSideReflexive index target

theorem ScopedCodePhaseEndpointCertifiedTrace.targetCertificate
    (trace : ScopedCodePhaseEndpointCertifiedTrace
      validCase index source target) :
    ScopedCodeTargetCertificate validCase index target := {
  structural := trace.trace.targetRefl
  alpha := trace.trace.targetAlpha
  side := trace.targetSide
}

/-- Append a certified local round while retaining every ordinary phase edge
and replacing the endpoint side certificate with the local result's one. -/
def ScopedCodePhaseEndpointCertifiedTrace.append
    (left : ScopedCodePhaseEndpointCertifiedTrace
      validCase index source middle)
    (right : ScopedCodePhaseCertifiedResult validCase index middle target) :
    ScopedCodePhaseEndpointCertifiedTrace validCase index source target := {
  trace := left.trace.append (.single right.result)
  targetSide := right.targetSide
}

def ScopedCodePhaseCertifiedTrace.rounds
    (trace : ScopedCodePhaseCertifiedTrace validCase index source target) : Nat :=
  match trace with
  | .single _ => 1
  | .trans _ rest => 1 + rest.rounds

def ScopedCodePhaseCertifiedTrace.append
    (left : ScopedCodePhaseCertifiedTrace validCase index source middle)
    (right : ScopedCodePhaseCertifiedTrace validCase index middle target) :
    ScopedCodePhaseCertifiedTrace validCase index source target :=
  match left with
  | .single round => .trans round right
  | .trans round rest => .trans round (rest.append right)

def ScopedCodePhaseCertifiedTrace.pad
    (trace : ScopedCodePhaseCertifiedTrace validCase index source target) :
    ScopedCodePhaseCertifiedTrace validCase index source target :=
  trace.append (.single trace.targetCertificate.identity)

def ScopedCodePhaseCertifiedResult.trace
    (result : ScopedCodePhaseCertifiedResult validCase index source target) :
    ScopedCodePhaseCertifiedTrace validCase index source target :=
  .single result

@[simp] theorem ScopedCodePhaseCertifiedTrace.rounds_forget
    (trace : ScopedCodePhaseCertifiedTrace validCase index source target) :
    trace.forget.rounds = trace.rounds := by
  induction trace with
  | single round => rfl
  | trans round rest ih =>
      simp [ScopedCodePhaseCertifiedTrace.forget,
        ScopedCodePhaseCertifiedTrace.rounds, ScopedCodePhaseTrace.rounds, ih]

def ScopedCodePhaseResult.trace
    (result : ScopedCodePhaseResult validCase index source target) :
    ScopedCodePhaseTrace validCase index source target :=
  .single result

def ScopedCodePhaseTraced
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    Nonempty (ScopedCodePhaseTrace validCase index source target)

theorem ScopedCodePhaseResult.traced
    (result : ScopedCodePhaseResult validCase index source target) :
    ScopedCodePhaseTraced validCase index source target :=
  ⟨result.trace⟩

theorem ScopedCodePhaseTrace.traced
    (trace : ScopedCodePhaseTrace validCase index source target) :
    ScopedCodePhaseTraced validCase index source target :=
  ⟨trace⟩

theorem scopedCodePhaseTraced_trans
    (left : ScopedCodePhaseTraced validCase index source middle)
    (right : ScopedCodePhaseTraced validCase index middle target) :
    ScopedCodePhaseTraced validCase index source target := by
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  exact (left.append right).traced

theorem scopedCodePhaseTraced_pad
    (related : ScopedCodePhaseTraced validCase index source target) :
    ScopedCodePhaseTraced validCase index source target := by
  rcases related with ⟨trace⟩
  exact trace.pad.traced

/-- Root-hygiene presentation used by one-round traversal laws. -/
def ScopedCodePhaseTracedOnAlphaReflexive
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedAlphaBireflexive index source →
      ScopedCodePhaseTraced validCase index source target

theorem scopedCodePhaseTracedOnAlphaReflexive_of_result
    (related : ScopedCodePhaseResultOnAlphaReflexive
      validCase index source target) :
    ScopedCodePhaseTracedOnAlphaReflexive
      validCase index source target := by
  intro reflexive
  rcases related reflexive with ⟨result⟩
  exact result.traced

/-- Lift every round of a trace through one syntactic context. The target
alpha identity produced by one lifted round supplies the source hygiene for
the next, so no global alpha reflexivity theorem is needed. -/
theorem ScopedCodePhaseTrace.lift
    (wrap : LCNF.Code .impure → LCNF.Code .impure)
    (roundLift : ∀ {left right},
      ScopedCodePhaseResult validCase childIndex left right →
      ScopedAlphaBireflexive parentIndex (wrap left) →
      Nonempty (ScopedCodePhaseResult validCase parentIndex
        (wrap left) (wrap right)))
    (trace : ScopedCodePhaseTrace validCase childIndex source target)
    (parent : ScopedAlphaBireflexive parentIndex (wrap source)) :
    ScopedCodePhaseTraced validCase parentIndex
      (wrap source) (wrap target) := by
  induction trace with
  | single round =>
      rcases roundLift round parent with ⟨lifted⟩
      exact lifted.traced
  | trans round rest ih =>
      rcases roundLift round parent with ⟨liftedRound⟩
      rcases ih liftedRound.targetAlpha with ⟨liftedRest⟩
      exact (ScopedCodePhaseTrace.trans liftedRound liftedRest).traced

/-- Lift two independently transformed children through one binary context.
If one trace ends first, its explicit endpoint identities generate inert
rounds while the other trace continues. -/
theorem ScopedCodePhaseTrace.zip
    (wrap : LCNF.Code .impure → LCNF.Code .impure →
      LCNF.Code .impure)
    (roundLift : ∀ {leftSource leftTarget rightSource rightTarget},
      ScopedCodePhaseResult validCase leftIndex leftSource leftTarget →
      ScopedCodePhaseResult validCase rightIndex rightSource rightTarget →
      ScopedAlphaBireflexive parentIndex
        (wrap leftSource rightSource) →
      Nonempty (ScopedCodePhaseResult validCase parentIndex
        (wrap leftSource rightSource) (wrap leftTarget rightTarget)))
    (leftTrace : ScopedCodePhaseTrace validCase leftIndex
      leftSource leftTarget)
    (rightTrace : ScopedCodePhaseTrace validCase rightIndex
      rightSource rightTarget)
    (parent : ScopedAlphaBireflexive parentIndex
      (wrap leftSource rightSource)) :
    ScopedCodePhaseTraced validCase parentIndex
      (wrap leftSource rightSource) (wrap leftTarget rightTarget) := by
  induction leftTrace generalizing rightSource rightTarget with
  | single leftRound =>
      cases rightTrace with
      | single rightRound =>
          rcases roundLift leftRound rightRound parent with ⟨lifted⟩
          exact lifted.traced
      | trans rightRound rightRest =>
          rcases roundLift leftRound rightRound parent with ⟨liftedRound⟩
          rcases rightRest.lift
              (wrap := fun right => wrap _ right)
              (roundLift := fun nextRound nextParent =>
                roundLift
                  (.identity leftRound.targetRefl leftRound.targetAlpha)
                  nextRound nextParent)
              liftedRound.targetAlpha with ⟨liftedRest⟩
          exact (ScopedCodePhaseTrace.trans liftedRound liftedRest).traced
  | trans leftRound leftRest ih =>
      cases rightTrace with
      | single rightRound =>
          rcases roundLift leftRound rightRound parent with ⟨liftedRound⟩
          rcases leftRest.lift
              (wrap := fun left => wrap left _)
              (roundLift := fun nextRound nextParent =>
                roundLift nextRound
                  (.identity rightRound.targetRefl rightRound.targetAlpha)
                  nextParent)
              liftedRound.targetAlpha with ⟨liftedRest⟩
          exact (ScopedCodePhaseTrace.trans liftedRound liftedRest).traced
      | trans rightRound rightRest =>
          rcases roundLift leftRound rightRound parent with ⟨liftedRound⟩
          rcases ih rightRest liftedRound.targetAlpha with ⟨liftedRest⟩
          exact (ScopedCodePhaseTrace.trans liftedRound liftedRest).traced

/-- One synchronized phase round over an alternative list. Constructor
metadata is unchanged; every body carries its own scoped phase result. -/
inductive ScopedAltsPhaseResult
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :
    List (LCNF.Alt .impure) → List (LCNF.Alt .impure) → Type where
  | nil : ScopedAltsPhaseResult validCase index [] []
  | ctor
      (body : ScopedCodePhaseResult validCase index left right)
      (rest : ScopedAltsPhaseResult validCase index leftRest rightRest) :
      ScopedAltsPhaseResult validCase index
        (.ctorAlt info left :: leftRest) (.ctorAlt info right :: rightRest)
  | default
      (body : ScopedCodePhaseResult validCase index left right)
      (rest : ScopedAltsPhaseResult validCase index leftRest rightRest) :
      ScopedAltsPhaseResult validCase index
        (.default left :: leftRest) (.default right :: rightRest)

/-- Pointwise endpoint identity for any target alternative in a synchronized
round. Unlike selector-based case-root alpha evidence, this also exposes
shadowed array entries. -/
theorem ScopedAltsPhaseResult.targetBodyIdentity_of_mem
    (result : ScopedAltsPhaseResult validCase index source target)
    (member : alt ∈ target) :
    Nonempty (ScopedCodePhaseResult validCase index
      alt.getCode alt.getCode) := by
  induction result with
  | nil => simp at member
  | ctor body rest ih =>
      simp at member
      rcases member with rfl | member
      · exact ⟨.identity body.targetRefl body.targetAlpha⟩
      · exact ih member
  | default body rest ih =>
      simp at member
      rcases member with rfl | member
      · exact ⟨.identity body.targetRefl body.targetAlpha⟩
      · exact ih member

theorem ScopedAltsPhaseResult.targetBodyIdentities_of_mem
    (result : ScopedAltsPhaseResult validCase index source target)
    (member : alt ∈ target) :
    Nonempty (ScopedCodeTargetIdentities validCase index alt.getCode) := by
  rcases result.targetBodyIdentity_of_mem member with ⟨identity⟩
  exact ⟨identity.identities⟩

/-- Endpoint identity round for a synchronized alternative result. -/
def ScopedAltsPhaseResult.targetIdentity
    (result : ScopedAltsPhaseResult validCase index source target) :
    ScopedAltsPhaseResult validCase index target target :=
  match result with
  | .nil => .nil
  | .ctor body rest =>
      .ctor (.identity body.targetRefl body.targetAlpha) rest.targetIdentity
  | .default body rest =>
      .default (.identity body.targetRefl body.targetAlpha)
        rest.targetIdentity

/-- Pointwise phase round that retains the complete endpoint certificate for
every alternative body, including selector-shadowed entries. -/
inductive ScopedAltsPhaseCertifiedResult
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :
    List (LCNF.Alt .impure) → List (LCNF.Alt .impure) → Type where
  | nil : ScopedAltsPhaseCertifiedResult validCase index [] []
  | ctor
      (body : ScopedCodePhaseCertifiedResult validCase index left right)
      (rest : ScopedAltsPhaseCertifiedResult
        validCase index leftRest rightRest) :
      ScopedAltsPhaseCertifiedResult validCase index
        (.ctorAlt info left :: leftRest) (.ctorAlt info right :: rightRest)
  | default
      (body : ScopedCodePhaseCertifiedResult validCase index left right)
      (rest : ScopedAltsPhaseCertifiedResult
        validCase index leftRest rightRest) :
      ScopedAltsPhaseCertifiedResult validCase index
        (.default left :: leftRest) (.default right :: rightRest)

def ScopedAltsPhaseCertifiedResult.forget
    (result : ScopedAltsPhaseCertifiedResult validCase index source target) :
    ScopedAltsPhaseResult validCase index source target :=
  match result with
  | .nil => .nil
  | .ctor body rest => .ctor body.result rest.forget
  | .default body rest => .default body.result rest.forget

/-- Complete endpoint certificate for any target alternative in one
synchronized certified round. -/
theorem ScopedAltsPhaseCertifiedResult.targetBodyCertificate_of_mem
    (result : ScopedAltsPhaseCertifiedResult validCase index source target)
    (member : alt ∈ target) :
    Nonempty (ScopedCodeTargetCertificate
      validCase index alt.getCode) := by
  induction result with
  | nil => simp at member
  | ctor body rest ih =>
      simp at member
      rcases member with rfl | member
      · exact ⟨body.certificate⟩
      · exact ih member
  | default body rest ih =>
      simp at member
      rcases member with rfl | member
      · exact ⟨body.certificate⟩
      · exact ih member

/-- The concrete body selected by a prepared singleton inherits the complete
certificate of one recursively transformed source alternative. This covers
both direct filtering and a singleton created by default folding. -/
theorem ScopedAltsPhaseCertifiedResult.preparedSingletonCertificate
    (result : ScopedAltsPhaseCertifiedResult validCase index
      sourceAlts.toList sourceAlts.toList)
    (singleton : (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1) :
    Nonempty (ScopedCodeTargetCertificate validCase index
      (shadowPrepareAlts
        (.mk typeName resultType discr sourceAlts))[0]!.getCode) := by
  rcases exists_source_alt_of_shadowPrepareAlts_singleton singleton with
    ⟨alt, member, bodyEq⟩
  rcases result.targetBodyCertificate_of_mem (Array.mem_def.mp member) with
    ⟨certificate⟩
  exact ⟨by simpa [bodyEq] using certificate⟩

/-- Every syntactic prepared alternative inherits the certificate of a
source alternative with the same body. This also covers the representative
whose selector is changed to `default` by genuine folding. -/
theorem ScopedAltsPhaseCertifiedResult.preparedBodyCertificate_of_mem
    (result : ScopedAltsPhaseCertifiedResult validCase index
      cases.alts.toList cases.alts.toList)
    (member : alt ∈ shadowPrepareAlts cases) :
    Nonempty (ScopedCodeTargetCertificate validCase index alt.getCode) := by
  rcases exists_source_alt_of_mem_shadowPrepareAlts member with
    ⟨sourceAlt, sourceMember, bodyEq⟩
  rcases result.targetBodyCertificate_of_mem
      (Array.mem_def.mp sourceMember) with ⟨certificate⟩
  exact ⟨by simpa [bodyEq] using certificate⟩

/-- Certificate for a concrete runtime selection from the prepared table. -/
theorem ScopedAltsPhaseCertifiedResult.preparedSelectionCertificate
    (result : ScopedAltsPhaseCertifiedResult validCase index
      cases.alts.toList cases.alts.toList)
    (selected : chooseAlt tag (shadowPrepareAlts cases).toList = some code) :
    Nonempty (ScopedCodeTargetCertificate validCase index code) := by
  rcases exists_mem_getCode_eq_of_chooseAlt selected with
    ⟨alt, member, bodyEq⟩
  rcases result.preparedBodyCertificate_of_mem
      (Array.mem_def.mpr member) with ⟨certificate⟩
  exact ⟨by simpa [bodyEq] using certificate⟩

/-- Rebuild the complete endpoint certificate for a retained prepared case.
Root scope facts come from the incoming case certificate; normalization is
preserved by the transparent table algorithm; every selected or syntactic
branch body comes from the certified recursive alternative result. -/
theorem scopedPreparedCaseTargetCertificate
    {typeName : Name} {resultType : Expr} {discr : FVarId}
    {alts : Array (LCNF.Alt .impure)}
    (root : ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr alts)))
    (alternatives : ScopedAltsPhaseCertifiedResult validCase index
      alts.toList alts.toList) :
    ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr
        (shadowPrepareAlts (.mk typeName resultType discr alts)))) := by
  let source : LCNF.Cases .impure :=
    .mk typeName resultType discr alts
  let prepared := shadowPrepareAlts source
  have alternativesSource : ScopedAltsPhaseCertifiedResult validCase index
      source.alts.toList source.alts.toList := by
    change ScopedAltsPhaseCertifiedResult validCase index
      alts.toList alts.toList
    exact alternatives
  have selectedCertificate : ∀ tag code,
      chooseAlt tag prepared.toList = some code →
      Nonempty (ScopedCodeTargetCertificate validCase index code) := by
    intro tag code selected
    exact alternativesSource.preparedSelectionCertificate (by
      simpa [prepared] using selected)
  have structural : CodeRel validCase
      (.cases (.mk typeName resultType discr prepared))
      (.cases (.mk typeName resultType discr prepared)) :=
    .aligned (.cases typeName resultType discr prepared prepared (by
      intro tag valid
      change SelectionRel validCase
        (chooseAlt tag prepared.toList) (chooseAlt tag prepared.toList)
      cases selected : chooseAlt tag prepared.toList with
      | none => exact .none
      | some code =>
          rcases selectedCertificate tag code selected with ⟨certificate⟩
          exact .some certificate.structural))
  have discrForward : ScopedFVarRelated index.forwardRho
      index.sourceScope index.targetScope discr discr := by
    cases root.alpha.forward with
    | terminal impossible => cases impossible
    | cases discrRelated selected => exact discrRelated
  have alphaForward : CodeRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope
      (.cases (.mk typeName resultType discr prepared))
      (.cases (.mk typeName resultType discr prepared)) :=
    .cases discrForward (by
      intro tag
      change CaseSelectionRelated
        (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
        index.forwardRho index.sourceScope index.targetScope
        (chooseAlt tag prepared.toList) (chooseAlt tag prepared.toList)
      cases selected : chooseAlt tag prepared.toList with
      | none => exact .none
      | some code =>
          rcases selectedCertificate tag code selected with ⟨certificate⟩
          exact .some certificate.alpha.forward)
  have discrBackward : ScopedFVarRelated index.backwardRho
      index.targetScope index.sourceScope discr discr := by
    cases root.alpha.backward with
    | terminal impossible => cases impossible
    | cases discrRelated selected => exact discrRelated
  have alphaBackward : CodeRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope
      (.cases (.mk typeName resultType discr prepared))
      (.cases (.mk typeName resultType discr prepared)) :=
    .cases discrBackward (by
      intro tag
      change CaseSelectionRelated
        (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
        index.backwardRho index.targetScope index.sourceScope
        (chooseAlt tag prepared.toList) (chooseAlt tag prepared.toList)
      cases selected : chooseAlt tag prepared.toList with
      | none => exact .none
      | some code =>
          rcases selectedCertificate tag code selected with ⟨certificate⟩
          exact .some certificate.alpha.backward)
  have side : ScopedCodeSideReflexive index
      (.cases (.mk typeName resultType discr prepared)) := by
    cases root.side with
    | cases leftDiscrScoped rightDiscrScoped leftNormalization
        rightNormalization ctorBranches defaultBranches =>
      have preparedNormalization :
          CaseTableNormalizationInvariant prepared := by
        simpa [prepared, source] using
          caseTableNormalization_shadowPrepareAlts leftNormalization
      exact .cases leftDiscrScoped rightDiscrScoped
        preparedNormalization preparedNormalization
        (by
          intro tag leftCode rightCode leftHas rightHas
          have same := preparedNormalization.deterministic.ctor
            tag leftCode rightCode leftHas rightHas
          subst rightCode
          rcases leftHas with ⟨info, member, selected⟩
          rcases alternativesSource.preparedBodyCertificate_of_mem
              (Array.mem_def.mpr member) with ⟨certificate⟩
          exact certificate.side)
        (by
          intro leftCode rightCode leftHas rightHas
          have same := preparedNormalization.deterministic.default
            leftCode rightCode leftHas rightHas
          subst rightCode
          rcases alternativesSource.preparedBodyCertificate_of_mem
              (Array.mem_def.mpr leftHas) with ⟨certificate⟩
          exact certificate.side)
  exact {
    structural := by simpa [prepared, source] using structural
    alpha := {
      forward := by simpa [prepared, source] using alphaForward
      backward := by simpa [prepared, source] using alphaBackward
    }
    side := by simpa [prepared, source] using side
  }

/-- Rebuild a case certificate from normalized selector metadata and complete
body certificates. The source root is used only for the unchanged
discriminant's scope and alpha facts. -/
theorem scopedCaseTargetCertificate_of_normalized
    {sourceAlts targetAlts : Array (LCNF.Alt .impure)}
    (root : ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr sourceAlts)))
    (normalization : CaseTableNormalizationInvariant targetAlts)
    (bodies : ∀ alt, alt ∈ targetAlts →
      Nonempty (ScopedCodeTargetCertificate validCase index alt.getCode)) :
    ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr targetAlts)) := by
  have selectedCertificate : ∀ tag code,
      chooseAlt tag targetAlts.toList = some code →
      Nonempty (ScopedCodeTargetCertificate validCase index code) := by
    intro tag code selected
    rcases exists_mem_getCode_eq_of_chooseAlt selected with
      ⟨alt, member, bodyEq⟩
    rcases bodies alt (Array.mem_def.mpr member) with ⟨certificate⟩
    exact ⟨by simpa [bodyEq] using certificate⟩
  have structural : CodeRel validCase
      (.cases (.mk typeName resultType discr targetAlts))
      (.cases (.mk typeName resultType discr targetAlts)) :=
    .aligned (.cases typeName resultType discr targetAlts targetAlts (by
      intro tag valid
      change SelectionRel validCase
        (chooseAlt tag targetAlts.toList) (chooseAlt tag targetAlts.toList)
      cases selected : chooseAlt tag targetAlts.toList with
      | none => exact .none
      | some code =>
          rcases selectedCertificate tag code selected with ⟨certificate⟩
          exact .some certificate.structural))
  have discrForward : ScopedFVarRelated index.forwardRho
      index.sourceScope index.targetScope discr discr := by
    cases root.alpha.forward with
    | terminal impossible => cases impossible
    | cases discrRelated selected => exact discrRelated
  have alphaForward : CodeRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope
      (.cases (.mk typeName resultType discr targetAlts))
      (.cases (.mk typeName resultType discr targetAlts)) :=
    .cases discrForward (by
      intro tag
      change CaseSelectionRelated
        (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
        index.forwardRho index.sourceScope index.targetScope
        (chooseAlt tag targetAlts.toList) (chooseAlt tag targetAlts.toList)
      cases selected : chooseAlt tag targetAlts.toList with
      | none => exact .none
      | some code =>
          rcases selectedCertificate tag code selected with ⟨certificate⟩
          exact .some certificate.alpha.forward)
  have discrBackward : ScopedFVarRelated index.backwardRho
      index.targetScope index.sourceScope discr discr := by
    cases root.alpha.backward with
    | terminal impossible => cases impossible
    | cases discrRelated selected => exact discrRelated
  have alphaBackward : CodeRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope
      (.cases (.mk typeName resultType discr targetAlts))
      (.cases (.mk typeName resultType discr targetAlts)) :=
    .cases discrBackward (by
      intro tag
      change CaseSelectionRelated
        (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
        index.backwardRho index.targetScope index.sourceScope
        (chooseAlt tag targetAlts.toList) (chooseAlt tag targetAlts.toList)
      cases selected : chooseAlt tag targetAlts.toList with
      | none => exact .none
      | some code =>
          rcases selectedCertificate tag code selected with ⟨certificate⟩
          exact .some certificate.alpha.backward)
  have side : ScopedCodeSideReflexive index
      (.cases (.mk typeName resultType discr targetAlts)) := by
    cases root.side with
    | cases leftDiscrScoped rightDiscrScoped leftNormalization
        rightNormalization ctorBranches defaultBranches =>
      exact .cases leftDiscrScoped rightDiscrScoped
        normalization normalization
        (by
          intro tag leftCode rightCode leftHas rightHas
          have same := normalization.deterministic.ctor
            tag leftCode rightCode leftHas rightHas
          subst rightCode
          rcases leftHas with ⟨info, member, selected⟩
          rcases bodies (.ctorAlt info leftCode)
              (Array.mem_def.mpr member) with ⟨certificate⟩
          exact certificate.side)
        (by
          intro leftCode rightCode leftHas rightHas
          have same := normalization.deterministic.default
            leftCode rightCode leftHas rightHas
          subst rightCode
          rcases bodies (.default leftCode)
              (Array.mem_def.mpr leftHas) with ⟨certificate⟩
          exact certificate.side)
  exact {
    structural := structural
    alpha := {
      forward := alphaForward
      backward := alphaBackward
    }
    side := side
  }

/-- The actual deterministic recursive alternative run has a certified case
endpoint. This theorem deliberately certifies the executable endpoint, not
arbitrary proof-only intermediate tables in a synchronized trace. -/
theorem scopedTransformedCaseTargetCertificate
    (run : sourceAlts.toList.mapM
      (shadowAltUsing? (shadowCode? fuel)) = some targetAlts)
    (root : ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr sourceAlts)))
    (alternatives : ScopedAltsPhaseCertifiedResult validCase index
      targetAlts targetAlts) :
    ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr targetAlts.toArray)) := by
  have sourceNormalization : CaseTableNormalizationInvariant sourceAlts := by
    cases root.side with
    | cases leftDiscrScoped rightDiscrScoped leftNormalization
        rightNormalization ctorBranches defaultBranches =>
      exact leftNormalization
  apply scopedCaseTargetCertificate_of_normalized root
    (caseTableNormalization_mapM_shadowAltUsing run (by
      simpa using sourceNormalization))
  intro alt member
  exact alternatives.targetBodyCertificate_of_mem (by simpa using member)

/-- Certified endpoint identity round for a synchronized alternative result. -/
def ScopedAltsPhaseCertifiedResult.targetIdentity
    (result : ScopedAltsPhaseCertifiedResult validCase index source target) :
    ScopedAltsPhaseCertifiedResult validCase index target target :=
  match result with
  | .nil => .nil
  | .ctor body rest =>
      .ctor body.certificate.identity rest.targetIdentity
  | .default body rest =>
      .default body.certificate.identity rest.targetIdentity

/-- Synchronized alternative trace retaining endpoint certificates at every
round and for every syntactic body. -/
inductive ScopedAltsPhaseCertifiedTrace
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :
    List (LCNF.Alt .impure) → List (LCNF.Alt .impure) → Type where
  | single
      (round : ScopedAltsPhaseCertifiedResult validCase index source target) :
      ScopedAltsPhaseCertifiedTrace validCase index source target
  | trans
      (round : ScopedAltsPhaseCertifiedResult validCase index source middle)
      (rest : ScopedAltsPhaseCertifiedTrace validCase index middle target) :
      ScopedAltsPhaseCertifiedTrace validCase index source target

def ScopedAltsPhaseCertifiedTrace.targetIdentity
    (trace : ScopedAltsPhaseCertifiedTrace validCase index source target) :
    ScopedAltsPhaseCertifiedResult validCase index target target :=
  match trace with
  | .single round => round.targetIdentity
  | .trans _ rest => rest.targetIdentity

def ScopedAltsPhaseCertifiedTrace.rounds
    (trace : ScopedAltsPhaseCertifiedTrace validCase index source target) : Nat :=
  match trace with
  | .single _ => 1
  | .trans _ rest => 1 + rest.rounds

def ScopedAltsPhaseCertifiedTrace.prependCtorIdentity
    (trace : ScopedAltsPhaseCertifiedTrace validCase index source target)
    (certificate : ScopedCodeTargetCertificate validCase index code) :
    ScopedAltsPhaseCertifiedTrace validCase index
      (.ctorAlt info code :: source) (.ctorAlt info code :: target) :=
  match trace with
  | .single round =>
      .single (.ctor certificate.identity round)
  | .trans round rest =>
      .trans (.ctor certificate.identity round)
        (rest.prependCtorIdentity certificate)

def ScopedAltsPhaseCertifiedTrace.prependDefaultIdentity
    (trace : ScopedAltsPhaseCertifiedTrace validCase index source target)
    (certificate : ScopedCodeTargetCertificate validCase index code) :
    ScopedAltsPhaseCertifiedTrace validCase index
      (.default code :: source) (.default code :: target) :=
  match trace with
  | .single round =>
      .single (.default certificate.identity round)
  | .trans round rest =>
      .trans (.default certificate.identity round)
        (rest.prependDefaultIdentity certificate)

def ScopedCodePhaseCertifiedTrace.withCtorTailIdentity
    (trace : ScopedCodePhaseCertifiedTrace validCase index source target)
    (tail : ScopedAltsPhaseCertifiedResult validCase index rest rest) :
    ScopedAltsPhaseCertifiedTrace validCase index
      (.ctorAlt info source :: rest) (.ctorAlt info target :: rest) :=
  match trace with
  | .single round => .single (.ctor round tail)
  | .trans round later =>
      .trans (.ctor round tail)
        (later.withCtorTailIdentity tail)

def ScopedCodePhaseCertifiedTrace.withDefaultTailIdentity
    (trace : ScopedCodePhaseCertifiedTrace validCase index source target)
    (tail : ScopedAltsPhaseCertifiedResult validCase index rest rest) :
    ScopedAltsPhaseCertifiedTrace validCase index
      (.default source :: rest) (.default target :: rest) :=
  match trace with
  | .single round => .single (.default round tail)
  | .trans round later =>
      .trans (.default round tail)
        (later.withDefaultTailIdentity tail)

def ScopedCodePhaseCertifiedTrace.consCtor
    (body : ScopedCodePhaseCertifiedTrace validCase index source target)
    (rest : ScopedAltsPhaseCertifiedTrace
      validCase index sourceRest targetRest) :
    ScopedAltsPhaseCertifiedTrace validCase index
      (.ctorAlt info source :: sourceRest)
      (.ctorAlt info target :: targetRest) :=
  match body, rest with
  | .single bodyRound, .single restRound =>
      .single (.ctor bodyRound restRound)
  | .single bodyRound, .trans restRound restLater =>
      .trans (.ctor bodyRound restRound)
        (restLater.prependCtorIdentity bodyRound.certificate)
  | .trans bodyRound bodyLater, .single restRound =>
      .trans (.ctor bodyRound restRound)
        (bodyLater.withCtorTailIdentity restRound.targetIdentity)
  | .trans bodyRound bodyLater, .trans restRound restLater =>
      .trans (.ctor bodyRound restRound)
        (bodyLater.consCtor restLater)

def ScopedCodePhaseCertifiedTrace.consDefault
    (body : ScopedCodePhaseCertifiedTrace validCase index source target)
    (rest : ScopedAltsPhaseCertifiedTrace
      validCase index sourceRest targetRest) :
    ScopedAltsPhaseCertifiedTrace validCase index
      (.default source :: sourceRest) (.default target :: targetRest) :=
  match body, rest with
  | .single bodyRound, .single restRound =>
      .single (.default bodyRound restRound)
  | .single bodyRound, .trans restRound restLater =>
      .trans (.default bodyRound restRound)
        (restLater.prependDefaultIdentity bodyRound.certificate)
  | .trans bodyRound bodyLater, .single restRound =>
      .trans (.default bodyRound restRound)
        (bodyLater.withDefaultTailIdentity restRound.targetIdentity)
  | .trans bodyRound bodyLater, .trans restRound restLater =>
      .trans (.default bodyRound restRound)
        (bodyLater.consDefault restLater)

/-- A nonempty sequence of synchronized alternative rounds. -/
inductive ScopedAltsPhaseTrace
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :
    List (LCNF.Alt .impure) → List (LCNF.Alt .impure) → Type where
  | single (round : ScopedAltsPhaseResult validCase index source target) :
      ScopedAltsPhaseTrace validCase index source target
  | trans (round : ScopedAltsPhaseResult validCase index source middle)
      (rest : ScopedAltsPhaseTrace validCase index middle target) :
      ScopedAltsPhaseTrace validCase index source target

/-- The pointwise identity round at the final synchronized endpoint. -/
def ScopedAltsPhaseTrace.targetIdentity
    (trace : ScopedAltsPhaseTrace validCase index source target) :
    ScopedAltsPhaseResult validCase index target target :=
  match trace with
  | .single round => round.targetIdentity
  | .trans _ rest => rest.targetIdentity

def ScopedAltsPhaseTrace.rounds
    (trace : ScopedAltsPhaseTrace validCase index source target) : Nat :=
  match trace with
  | .single _ => 1
  | .trans _ rest => 1 + rest.rounds

def ScopedAltsPhaseCertifiedTrace.forget
    (trace : ScopedAltsPhaseCertifiedTrace validCase index source target) :
    ScopedAltsPhaseTrace validCase index source target :=
  match trace with
  | .single round => .single round.forget
  | .trans round rest => .trans round.forget rest.forget

/-- Synchronized non-lockstep alternative trace with complete certificates
for the actual endpoint bodies. Intermediate tables remain ordinary for the
same normalization-coherence reason as the enclosing code trace. -/
structure ScopedAltsPhaseEndpointCertifiedTrace
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : List (LCNF.Alt .impure)) : Type where
  trace : ScopedAltsPhaseTrace validCase index source target
  targetIdentity : ScopedAltsPhaseCertifiedResult validCase index target target

@[simp] theorem ScopedAltsPhaseCertifiedTrace.rounds_forget
    (trace : ScopedAltsPhaseCertifiedTrace validCase index source target) :
    trace.forget.rounds = trace.rounds := by
  induction trace with
  | single round => rfl
  | trans round rest ih =>
      simp [ScopedAltsPhaseCertifiedTrace.forget,
        ScopedAltsPhaseCertifiedTrace.rounds, ScopedAltsPhaseTrace.rounds, ih]

/-- Pad an already-finished constructor body while the remaining alternatives
continue through later rounds. -/
def ScopedAltsPhaseTrace.prependCtorIdentity
    (trace : ScopedAltsPhaseTrace validCase index source target)
    (structural : CodeRel validCase code code)
    (alpha : ScopedAlphaBireflexive index code) :
    ScopedAltsPhaseTrace validCase index
      (.ctorAlt info code :: source) (.ctorAlt info code :: target) :=
  match trace with
  | .single round =>
      .single (.ctor (.identity structural alpha) round)
  | .trans round rest =>
      .trans (.ctor (.identity structural alpha) round)
        (rest.prependCtorIdentity structural alpha)

/-- Default-alternative counterpart of `prependCtorIdentity`. -/
def ScopedAltsPhaseTrace.prependDefaultIdentity
    (trace : ScopedAltsPhaseTrace validCase index source target)
    (structural : CodeRel validCase code code)
    (alpha : ScopedAlphaBireflexive index code) :
    ScopedAltsPhaseTrace validCase index
      (.default code :: source) (.default code :: target) :=
  match trace with
  | .single round =>
      .single (.default (.identity structural alpha) round)
  | .trans round rest =>
      .trans (.default (.identity structural alpha) round)
        (rest.prependDefaultIdentity structural alpha)

/-- Pad an already-finished alternative tail while a constructor body keeps
transforming. -/
def ScopedCodePhaseTrace.withCtorTailIdentity
    (trace : ScopedCodePhaseTrace validCase index source target)
    (tail : ScopedAltsPhaseResult validCase index rest rest) :
    ScopedAltsPhaseTrace validCase index
      (.ctorAlt info source :: rest) (.ctorAlt info target :: rest) :=
  match trace with
  | .single round => .single (.ctor round tail)
  | .trans round later =>
      .trans (.ctor round tail)
        (later.withCtorTailIdentity tail)

/-- Default-alternative counterpart of `withCtorTailIdentity`. -/
def ScopedCodePhaseTrace.withDefaultTailIdentity
    (trace : ScopedCodePhaseTrace validCase index source target)
    (tail : ScopedAltsPhaseResult validCase index rest rest) :
    ScopedAltsPhaseTrace validCase index
      (.default source :: rest) (.default target :: rest) :=
  match trace with
  | .single round => .single (.default round tail)
  | .trans round later =>
      .trans (.default round tail)
        (later.withDefaultTailIdentity tail)

/-- Synchronize a constructor-body trace with the trace for the remaining
alternatives, padding whichever side finishes first. -/
def ScopedCodePhaseTrace.consCtor
    (body : ScopedCodePhaseTrace validCase index source target)
    (rest : ScopedAltsPhaseTrace validCase index sourceRest targetRest) :
    ScopedAltsPhaseTrace validCase index
      (.ctorAlt info source :: sourceRest)
      (.ctorAlt info target :: targetRest) :=
  match body, rest with
  | .single bodyRound, .single restRound =>
      .single (.ctor bodyRound restRound)
  | .single bodyRound, .trans restRound restLater =>
      .trans (.ctor bodyRound restRound)
        (restLater.prependCtorIdentity
          bodyRound.targetRefl bodyRound.targetAlpha)
  | .trans bodyRound bodyLater, .single restRound =>
      .trans (.ctor bodyRound restRound)
        (bodyLater.withCtorTailIdentity restRound.targetIdentity)
  | .trans bodyRound bodyLater, .trans restRound restLater =>
      .trans (.ctor bodyRound restRound)
        (bodyLater.consCtor restLater)

/-- Synchronize a default-body trace with the trace for the remaining
alternatives. -/
def ScopedCodePhaseTrace.consDefault
    (body : ScopedCodePhaseTrace validCase index source target)
    (rest : ScopedAltsPhaseTrace validCase index sourceRest targetRest) :
    ScopedAltsPhaseTrace validCase index
      (.default source :: sourceRest) (.default target :: targetRest) :=
  match body, rest with
  | .single bodyRound, .single restRound =>
      .single (.default bodyRound restRound)
  | .single bodyRound, .trans restRound restLater =>
      .trans (.default bodyRound restRound)
        (restLater.prependDefaultIdentity
          bodyRound.targetRefl bodyRound.targetAlpha)
  | .trans bodyRound bodyLater, .single restRound =>
      .trans (.default bodyRound restRound)
        (bodyLater.withDefaultTailIdentity restRound.targetIdentity)
  | .trans bodyRound bodyLater, .trans restRound restLater =>
      .trans (.default bodyRound restRound)
        (bodyLater.consDefault restLater)

mutual

  /-- Alpha reflexivity plus lexical evidence for every syntactic recursive
  child. `CodeRelated.cases` is selector-based and therefore cannot by itself
  expose shadowed alternatives, while the compiler traverses and compares
  every array entry. -/
  inductive ScopedAlphaBireflexiveTree :
      (index : ScopeIndex) → LCNF.Code .impure → Prop where
    | letE
        (root : ScopedAlphaBireflexive index (.let declaration continuation))
        (continuationTree : ScopedAlphaBireflexiveTree
          (index.pushVar declaration.fvarId) continuation) :
        ScopedAlphaBireflexiveTree index (.let declaration continuation)
    | jp
        (root : ScopedAlphaBireflexive index
          (.jp (.mk fvarId binderName params type body) continuation))
        (bodyTree : ScopedAlphaBireflexiveTree (index.pushParams params) body)
        (continuationTree : ScopedAlphaBireflexiveTree
          (index.pushJoin fvarId) continuation) :
        ScopedAlphaBireflexiveTree index
          (.jp (.mk fvarId binderName params type body) continuation)
    | jmp
        (root : ScopedAlphaBireflexive index (.jmp fvarId args)) :
        ScopedAlphaBireflexiveTree index (.jmp fvarId args)
    | cases
        (root : ScopedAlphaBireflexive index (.cases cases))
        (alternativesTree : ScopedAlphaBireflexiveAlts index cases.alts.toList) :
        ScopedAlphaBireflexiveTree index (.cases cases)
    | ret
        (root : ScopedAlphaBireflexive index (.return fvarId)) :
        ScopedAlphaBireflexiveTree index (.return fvarId)
    | unreach
        (root : ScopedAlphaBireflexive index (.unreach type)) :
        ScopedAlphaBireflexiveTree index (.unreach type)
    | oset
        (root : ScopedAlphaBireflexive index
          (.oset fvarId fieldIndex value continuation))
        (continuationTree : ScopedAlphaBireflexiveTree index continuation) :
        ScopedAlphaBireflexiveTree index
          (.oset fvarId fieldIndex value continuation)
    | uset
        (root : ScopedAlphaBireflexive index
          (.uset fvarId fieldIndex value continuation))
        (continuationTree : ScopedAlphaBireflexiveTree index continuation) :
        ScopedAlphaBireflexiveTree index
          (.uset fvarId fieldIndex value continuation)
    | sset
        (root : ScopedAlphaBireflexive index
          (.sset fvarId width offset value type continuation))
        (continuationTree : ScopedAlphaBireflexiveTree index continuation) :
        ScopedAlphaBireflexiveTree index
          (.sset fvarId width offset value type continuation)
    | setTag
        (root : ScopedAlphaBireflexive index
          (.setTag fvarId tag continuation))
        (continuationTree : ScopedAlphaBireflexiveTree index continuation) :
        ScopedAlphaBireflexiveTree index (.setTag fvarId tag continuation)
    | inc
        (root : ScopedAlphaBireflexive index
          (.inc fvarId amount check persistent continuation))
        (continuationTree : ScopedAlphaBireflexiveTree index continuation) :
        ScopedAlphaBireflexiveTree index
          (.inc fvarId amount check persistent continuation)
    | dec
        (root : ScopedAlphaBireflexive index
          (.dec fvarId amount check persistent objects continuation))
        (continuationTree : ScopedAlphaBireflexiveTree index continuation) :
        ScopedAlphaBireflexiveTree index
          (.dec fvarId amount check persistent objects continuation)
    | del
        (root : ScopedAlphaBireflexive index (.del fvarId continuation))
        (continuationTree : ScopedAlphaBireflexiveTree index continuation) :
        ScopedAlphaBireflexiveTree index (.del fvarId continuation)

  /-- Pointwise hygiene/reflexivity for the complete alternative array,
  including entries hidden by an earlier duplicate selector. -/
  inductive ScopedAlphaBireflexiveAlts :
      (index : ScopeIndex) → List (LCNF.Alt .impure) → Prop where
    | nil : ScopedAlphaBireflexiveAlts index []
    | ctor
        (bodyTree : ScopedAlphaBireflexiveTree index code)
        (rest : ScopedAlphaBireflexiveAlts index alts) :
        ScopedAlphaBireflexiveAlts index (.ctorAlt info code :: alts)
    | default
        (bodyTree : ScopedAlphaBireflexiveTree index code)
        (rest : ScopedAlphaBireflexiveAlts index alts) :
        ScopedAlphaBireflexiveAlts index (.default code :: alts)

end

theorem ScopedAlphaBireflexiveTree.root
    (evidence : ScopedAlphaBireflexiveTree index code) :
    ScopedAlphaBireflexive index code := by
  cases evidence <;> assumption

mutual

  /-- Complete source certificates for every recursive position. This is the
  certified traversal input corresponding to `ScopedAlphaBireflexiveTree`;
  in particular, case alternatives hidden by duplicate selectors remain
  available pointwise. -/
  inductive ScopedCodeTargetCertificateTree
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      (index : ScopeIndex) → LCNF.Code .impure → Prop where
    | letE
        (root : ScopedCodeTargetCertificate validCase index
          (.let declaration continuation))
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          (index.pushVar declaration.fvarId) continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.let declaration continuation)
    | jp
        (root : ScopedCodeTargetCertificate validCase index
          (.jp (.mk fvarId binderName params type body) continuation))
        (bodyTree : ScopedCodeTargetCertificateTree validCase
          (index.pushParams params) body)
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          (index.pushJoin fvarId) continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.jp (.mk fvarId binderName params type body) continuation)
    | jmp
        (root : ScopedCodeTargetCertificate validCase index
          (.jmp fvarId args)) :
        ScopedCodeTargetCertificateTree validCase index (.jmp fvarId args)
    | cases
        (root : ScopedCodeTargetCertificate validCase index (.cases cases))
        (alternativesTree : ScopedCodeTargetCertificateAlts validCase
          index cases.alts.toList) :
        ScopedCodeTargetCertificateTree validCase index (.cases cases)
    | ret
        (root : ScopedCodeTargetCertificate validCase index
          (.return fvarId)) :
        ScopedCodeTargetCertificateTree validCase index (.return fvarId)
    | unreach
        (root : ScopedCodeTargetCertificate validCase index
          (.unreach type)) :
        ScopedCodeTargetCertificateTree validCase index (.unreach type)
    | oset
        (root : ScopedCodeTargetCertificate validCase index
          (.oset fvarId fieldIndex value continuation))
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          index continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.oset fvarId fieldIndex value continuation)
    | uset
        (root : ScopedCodeTargetCertificate validCase index
          (.uset fvarId fieldIndex value continuation))
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          index continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.uset fvarId fieldIndex value continuation)
    | sset
        (root : ScopedCodeTargetCertificate validCase index
          (.sset fvarId width offset value type continuation))
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          index continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.sset fvarId width offset value type continuation)
    | setTag
        (root : ScopedCodeTargetCertificate validCase index
          (.setTag fvarId tag continuation))
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          index continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.setTag fvarId tag continuation)
    | inc
        (root : ScopedCodeTargetCertificate validCase index
          (.inc fvarId amount check persistent continuation))
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          index continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.inc fvarId amount check persistent continuation)
    | dec
        (root : ScopedCodeTargetCertificate validCase index
          (.dec fvarId amount check persistent objects continuation))
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          index continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.dec fvarId amount check persistent objects continuation)
    | del
        (root : ScopedCodeTargetCertificate validCase index
          (.del fvarId continuation))
        (continuationTree : ScopedCodeTargetCertificateTree validCase
          index continuation) :
        ScopedCodeTargetCertificateTree validCase index
          (.del fvarId continuation)

  /-- Pointwise complete certificates for an alternative list. -/
  inductive ScopedCodeTargetCertificateAlts
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      (index : ScopeIndex) → List (LCNF.Alt .impure) → Prop where
    | nil : ScopedCodeTargetCertificateAlts validCase index []
    | ctor
        (bodyTree : ScopedCodeTargetCertificateTree validCase index code)
        (rest : ScopedCodeTargetCertificateAlts validCase index alts) :
        ScopedCodeTargetCertificateAlts validCase index
          (.ctorAlt info code :: alts)
    | default
        (bodyTree : ScopedCodeTargetCertificateTree validCase index code)
        (rest : ScopedCodeTargetCertificateAlts validCase index alts) :
        ScopedCodeTargetCertificateAlts validCase index
          (.default code :: alts)

end

theorem ScopedCodeTargetCertificateTree.root
    (tree : ScopedCodeTargetCertificateTree validCase index code) :
    ScopedCodeTargetCertificate validCase index code := by
  cases tree <;> assumption

/-- Full-tree trace presentation used by the recursive case kernel. The tree
supplies hygiene for every alternative, including syntactically shadowed
entries that root alpha selection cannot expose. -/
def ScopedCodePhaseTracedOnAlphaTree
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedAlphaBireflexiveTree index source →
      ScopedCodePhaseTraced validCase index source target

/-- Strong full-tree presentation whose phase trace retains side certificates
at every round boundary. -/
def ScopedCodePhaseCertifiedTracedOnAlphaTree
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedAlphaBireflexiveTree index source →
      Nonempty (ScopedCodePhaseCertifiedTrace
        validCase index source target)

/-- Recursive non-lockstep relation driven by complete source certificates
and returning a certified actual endpoint. -/
def ScopedCodePhaseEndpointCertifiedOnCertificateTree
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedCodeTargetCertificateTree validCase index source →
      Nonempty (ScopedCodePhaseEndpointCertifiedTrace
        validCase index source target)

theorem ScopedAlphaBireflexiveAlts.forward
    (evidence : ScopedAlphaBireflexiveAlts index alts) :
    AltsRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope alts alts := by
  let rec go {index alts}
      (evidence : ScopedAlphaBireflexiveAlts index alts) :
      AltsRelated
        (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
        index.forwardRho index.sourceScope index.targetScope alts alts :=
    match evidence with
    | .nil => .nil
    | .ctor bodyTree rest =>
        .cons (.ctor bodyTree.root.forward) (go rest)
    | .default bodyTree rest =>
        .cons (.default bodyTree.root.forward) (go rest)
  exact go evidence

theorem ScopedAlphaBireflexiveAlts.backward
    (evidence : ScopedAlphaBireflexiveAlts index alts) :
    AltsRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope alts alts := by
  let rec go {index alts}
      (evidence : ScopedAlphaBireflexiveAlts index alts) :
      AltsRelated
        (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
        index.backwardRho index.targetScope index.sourceScope alts alts :=
    match evidence with
    | .nil => .nil
    | .ctor bodyTree rest =>
        .cons (.ctor bodyTree.root.backward) (go rest)
    | .default bodyTree rest =>
        .cons (.default bodyTree.root.backward) (go rest)
  exact go evidence

theorem scopedAlphaBireflexiveTree_cases
    (forwardDiscr : ScopedFVarRelated index.forwardRho
      index.sourceScope index.targetScope cases.discr cases.discr)
    (backwardDiscr : ScopedFVarRelated index.backwardRho
      index.targetScope index.sourceScope cases.discr cases.discr)
    (alternatives : ScopedAlphaBireflexiveAlts index cases.alts.toList) :
    ScopedAlphaBireflexiveTree index (.cases cases) :=
  .cases {
    forward := .cases forwardDiscr fun _ => chooseAlt_related alternatives.forward
    backward := .cases backwardDiscr fun _ => chooseAlt_related alternatives.backward
  } alternatives

/-- Project the discriminator relation from a case-to-case alpha proof. The
`terminal` branch is index-impossible but must be discharged explicitly when
eliminating `CodeRelated`. -/
theorem codeRelated_cases_discr
    (related : CodeRelated
      (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope (.cases left) (.cases right)) :
    ScopedFVarRelated rho leftScope rightScope left.discr right.discr := by
  cases related with
  | terminal related => cases related
  | cases discr _ => exact discr

/-- Project semantic branch selection from a case-to-case alpha proof. -/
theorem codeRelated_cases_selected
    (related : CodeRelated
      (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope (.cases left) (.cases right)) :
    ∀ tag, CaseSelectionRelated
      (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope
      (chooseAlt tag left.alts.toList) (chooseAlt tag right.alts.toList) := by
  cases related with
  | terminal related => cases related
  | cases _ selected => exact selected

/-- Alpha-related code agrees on whether its outer constructor is
syntactically unreachable. -/
theorem codeRelated_isUnreachable_eq
    (related : CodeRelated
      (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope left right) :
    SimpCase.isUnreachable left = SimpCase.isUnreachable right := by
  cases related <;> try rfl
  rename_i terminal
  cases terminal <;> rfl

/-- Unreachable filtering preserves pointwise alpha relations; related bodies
are filtered in lockstep because alpha equivalence preserves the outer code
constructor. -/
theorem altsRelated_removeUnreachable
    (related : AltsRelated
      (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope left right) :
    AltsRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope
      (SimpCase.removeUnreachable left) (SimpCase.removeUnreachable right) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      cases head with
      | ctor code =>
          rename_i leftCode rightCode info
          have same := codeRelated_isUnreachable_eq code
          cases reachable : SimpCase.isUnreachable leftCode with
          | false =>
              have rightReachable :
                  SimpCase.isUnreachable rightCode = false := by
                rw [← same]
                exact reachable
              simpa [SimpCase.removeUnreachable, LCNF.Alt.getCode,
                reachable, rightReachable]
                using ListRel.cons (.ctor code) ih
          | true =>
              have rightUnreachable :
                  SimpCase.isUnreachable rightCode = true := by
                rw [← same]
                exact reachable
              simpa [SimpCase.removeUnreachable, LCNF.Alt.getCode,
                reachable, rightUnreachable]
                using ih
      | default code =>
          rename_i leftCode rightCode
          have same := codeRelated_isUnreachable_eq code
          cases reachable : SimpCase.isUnreachable leftCode with
          | false =>
              have rightReachable :
                  SimpCase.isUnreachable rightCode = false := by
                rw [← same]
                exact reachable
              simpa [SimpCase.removeUnreachable, LCNF.Alt.getCode,
                reachable, rightReachable]
                using ListRel.cons (.default code) ih
          | true =>
              have rightUnreachable :
                  SimpCase.isUnreachable rightCode = true := by
                rw [← same]
                exact reachable
              simpa [SimpCase.removeUnreachable, LCNF.Alt.getCode,
                reachable, rightUnreachable]
                using ih

/-- Exact scoped contract for the private default-folding calculation. It is
automatic when the table is unchanged; a genuine fold supplies the
bidirectional selected-branch alpha witnesses justified by the checker and
the phase's hygiene invariant. -/
structure ScopedAddDefaultSelectionEvidence
    (index : ScopeIndex) (middleAlts targetAlts :
      Array (LCNF.Alt .impure)) : Prop where
  forward : ∀ tag, CaseSelectionRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope
    (chooseAlt tag middleAlts.toList)
    (chooseAlt tag (shadowAddDefaultAlt targetAlts).toList)
  backward : ∀ tag, CaseSelectionRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope
    (chooseAlt tag (shadowAddDefaultAlt targetAlts).toList)
    (chooseAlt tag middleAlts.toList)

theorem scopedAddDefaultSelectionEvidence_of_eq
    (unchanged : shadowAddDefaultAlt alts = alts)
    (forward : AltsRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope
      alts.toList alts.toList)
    (backward : AltsRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope
      alts.toList alts.toList) :
    ScopedAddDefaultSelectionEvidence index alts alts where
  forward := by
    intro tag
    rw [unchanged]
    exact chooseAlt_related forward
  backward := by
    intro tag
    rw [unchanged]
    exact chooseAlt_related backward

/-- A universally well-scoped presentation of the factor relation. Ill-scoped
indices are not asserted to relate anything; callers provide alpha reflexivity
at the source position they actually traverse. -/
def ScopedCodeFactoredOnAlphaReflexive
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedAlphaBireflexive index source →
      ScopedCodeFactored validCase index source target

/-- Full-tree presentation used by the case kernel. Unlike root
alpha-reflexivity, this premise supplies a proof for every recursively
transformed alternative, including semantically shadowed entries. -/
def ScopedCodeFactoredOnAlphaTree
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedAlphaBireflexiveTree index source →
      ScopedCodeFactored validCase index source target

/-- Pointwise factors after applying the full-tree certificate to every
recursive alternative premise produced by the traversal. -/
inductive ScopedAltFactored
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :
    LCNF.Alt .impure → LCNF.Alt .impure → Prop where
  | ctor
      (body : ScopedCodeFactored validCase index left right) :
      ScopedAltFactored validCase index
        (.ctorAlt info left) (.ctorAlt info right)
  | default
      (body : ScopedCodeFactored validCase index left right) :
      ScopedAltFactored validCase index (.default left) (.default right)

abbrev ScopedAltsFactored
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :=
  ListRel (ScopedAltFactored validCase index)

/-- Pointwise structural relation between alternatives with identical
selectors. -/
inductive StructuralAltRelated
    (validCase : LCNF.Cases .impure → Nat → Prop) :
    LCNF.Alt .impure → LCNF.Alt .impure → Prop where
  | ctor (body : CodeRel validCase left right) :
      StructuralAltRelated validCase
        (.ctorAlt info left) (.ctorAlt info right)
  | default (body : CodeRel validCase left right) :
      StructuralAltRelated validCase (.default left) (.default right)

abbrev StructuralAltsRelated
    (validCase : LCNF.Cases .impure → Nat → Prop) :=
  ListRel (StructuralAltRelated validCase)

theorem structuralFindCtorAlt_related
    (related : StructuralAltsRelated validCase left right) :
    SelectionRel validCase (findCtorAlt tag left) (findCtorAlt tag right) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      cases head with
      | ctor body =>
          rename_i leftCode rightCode info
          by_cases selected : info.cidx == tag
          · simpa [findCtorAlt, selected] using SelectionRel.some body
          · simpa [findCtorAlt, selected] using ih
      | default body => simpa [findCtorAlt] using ih

theorem structuralFindDefaultAlt_related
    (related : StructuralAltsRelated validCase left right) :
    SelectionRel validCase (findDefaultAlt left) (findDefaultAlt right) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      cases head with
      | ctor body => simpa [findDefaultAlt] using ih
      | default body =>
          simpa [findDefaultAlt] using SelectionRel.some body

theorem selectionRel_orElse
    (primary : SelectionRel validCase left right)
    (fallback : SelectionRel validCase leftFallback rightFallback) :
    SelectionRel validCase
      (left.orElse fun _ => leftFallback)
      (right.orElse fun _ => rightFallback) := by
  cases primary with
  | none => exact fallback
  | some body => exact .some body

/-- Pointwise structural alternative rounds relate every interpreter
selection, not merely the entries visible in the list representation. -/
theorem structuralChooseAlt_related
    (related : StructuralAltsRelated validCase left right) :
    SelectionRel validCase (chooseAlt tag left) (chooseAlt tag right) := by
  unfold chooseAlt
  exact selectionRel_orElse
    (structuralFindCtorAlt_related related)
    (structuralFindDefaultAlt_related related)

/-- Materialized structural/alpha/structural data for one synchronized
alternative round. -/
structure ScopedAltsPhaseMaterialized
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : List (LCNF.Alt .impure)) : Type where
  structuralMiddle : List (LCNF.Alt .impure)
  alphaMiddle : List (LCNF.Alt .impure)
  structuralBefore : StructuralAltsRelated validCase source structuralMiddle
  alphaForward : AltsRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope
    structuralMiddle alphaMiddle
  alphaBackward : AltsRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope
    alphaMiddle structuralMiddle
  structuralAfter : StructuralAltsRelated validCase alphaMiddle target
  targetRefl : StructuralAltsRelated validCase target target
  targetAlphaForward : AltsRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope target target
  targetAlphaBackward : AltsRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope target target

def ScopedAltsPhaseResult.materialize
    (result : ScopedAltsPhaseResult validCase index source target) :
    ScopedAltsPhaseMaterialized validCase index source target :=
  match result with
  | .nil => {
      structuralMiddle := []
      alphaMiddle := []
      structuralBefore := .nil
      alphaForward := .nil
      alphaBackward := .nil
      structuralAfter := .nil
      targetRefl := .nil
      targetAlphaForward := .nil
      targetAlphaBackward := .nil
    }
  | .ctor body rest =>
      let bodyFactor := body.trifactor
      let tail := rest.materialize
      {
        structuralMiddle := .ctorAlt _ bodyFactor.structuralMiddle ::
          tail.structuralMiddle
        alphaMiddle := .ctorAlt _ bodyFactor.alphaMiddle :: tail.alphaMiddle
        structuralBefore := .cons (.ctor bodyFactor.structuralBefore)
          tail.structuralBefore
        alphaForward := .cons (.ctor bodyFactor.alphaForward)
          tail.alphaForward
        alphaBackward := .cons (.ctor bodyFactor.alphaBackward)
          tail.alphaBackward
        structuralAfter := .cons (.ctor bodyFactor.structuralAfter)
          tail.structuralAfter
        targetRefl := .cons (.ctor body.targetRefl) tail.targetRefl
        targetAlphaForward := .cons (.ctor body.targetAlpha.forward)
          tail.targetAlphaForward
        targetAlphaBackward := .cons (.ctor body.targetAlpha.backward)
          tail.targetAlphaBackward
      }
  | .default body rest =>
      let bodyFactor := body.trifactor
      let tail := rest.materialize
      {
        structuralMiddle := .default bodyFactor.structuralMiddle ::
          tail.structuralMiddle
        alphaMiddle := .default bodyFactor.alphaMiddle :: tail.alphaMiddle
        structuralBefore := .cons (.default bodyFactor.structuralBefore)
          tail.structuralBefore
        alphaForward := .cons (.default bodyFactor.alphaForward)
          tail.alphaForward
        alphaBackward := .cons (.default bodyFactor.alphaBackward)
          tail.alphaBackward
        structuralAfter := .cons (.default bodyFactor.structuralAfter)
          tail.structuralAfter
        targetRefl := .cons (.default body.targetRefl) tail.targetRefl
        targetAlphaForward := .cons (.default body.targetAlpha.forward)
          tail.targetAlphaForward
        targetAlphaBackward := .cons (.default body.targetAlpha.backward)
          tail.targetAlphaBackward
      }

/-- Lift one synchronized alternative round to the enclosing case table. -/
def ScopedAltsPhaseResult.casesResult
    (result : ScopedAltsPhaseResult validCase index source target)
    (typeName : Name) (resultType : Expr) (discr : FVarId)
    (parent : ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr source.toArray))) :
    ScopedCodePhaseResult validCase index
      (.cases (.mk typeName resultType discr source.toArray))
      (.cases (.mk typeName resultType discr target.toArray)) :=
  let materialized := result.materialize
  {
    factor := .threePhase {
      structuralMiddle := .cases (.mk typeName resultType discr
        materialized.structuralMiddle.toArray)
      alphaMiddle := .cases (.mk typeName resultType discr
        materialized.alphaMiddle.toArray)
      structuralBefore := .aligned (.cases typeName resultType discr
        source.toArray materialized.structuralMiddle.toArray
        (fun _ _ => structuralChooseAlt_related
          materialized.structuralBefore))
      alphaForward := .cases
        (codeRelated_cases_discr
          (left := .mk typeName resultType discr source.toArray)
          (right := .mk typeName resultType discr source.toArray)
          parent.forward)
        (fun _ => chooseAlt_related materialized.alphaForward)
      alphaBackward := .cases
        (codeRelated_cases_discr
          (left := .mk typeName resultType discr source.toArray)
          (right := .mk typeName resultType discr source.toArray)
          parent.backward)
        (fun _ => chooseAlt_related materialized.alphaBackward)
      structuralAfter := .aligned (.cases typeName resultType discr
        materialized.alphaMiddle.toArray target.toArray
        (fun _ _ => structuralChooseAlt_related
          materialized.structuralAfter))
    }
    targetRefl := .aligned (.cases typeName resultType discr
      target.toArray target.toArray
      (fun _ _ => structuralChooseAlt_related materialized.targetRefl))
    targetAlpha := {
      forward := .cases (codeRelated_cases_discr
        (left := .mk typeName resultType discr source.toArray)
        (right := .mk typeName resultType discr source.toArray)
        parent.forward)
        (fun _ => chooseAlt_related materialized.targetAlphaForward)
      backward := .cases (codeRelated_cases_discr
        (left := .mk typeName resultType discr source.toArray)
        (right := .mk typeName resultType discr source.toArray)
        parent.backward)
        (fun _ => chooseAlt_related materialized.targetAlphaBackward)
    }
  }

/-- Lift every synchronized alternative round to the enclosing case table. -/
def ScopedAltsPhaseTrace.casesTrace
    (trace : ScopedAltsPhaseTrace validCase index source target)
    (typeName : Name) (resultType : Expr) (discr : FVarId)
    (parent : ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr source.toArray))) :
    ScopedCodePhaseTrace validCase index
      (.cases (.mk typeName resultType discr source.toArray))
      (.cases (.mk typeName resultType discr target.toArray)) :=
  match trace with
  | .single round => .single
      (round.casesResult typeName resultType discr parent)
  | .trans round rest =>
      let lifted := round.casesResult typeName resultType discr parent
      .trans lifted
        (rest.casesTrace typeName resultType discr lifted.targetAlpha)

@[simp] theorem ScopedAltsPhaseTrace.rounds_casesTrace
    (trace : ScopedAltsPhaseTrace validCase index source target)
    (parent : ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr source.toArray))) :
    (trace.casesTrace typeName resultType discr parent).rounds =
      trace.rounds := by
  induction trace with
  | single round => rfl
  | trans round rest ih =>
      simp [ScopedAltsPhaseTrace.casesTrace,
        ScopedCodePhaseTrace.rounds, ScopedAltsPhaseTrace.rounds, ih]

/-- A materialized pointwise factor for an entire alternative list. The
structural intermediate list is explicit, while both alpha orientations use
the exact recursive scope index. -/
structure ScopedAltsBifactor
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : List (LCNF.Alt .impure)) : Type where
  middle : List (LCNF.Alt .impure)
  structural : StructuralAltsRelated validCase source middle
  alphaForward : AltsRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope middle target
  alphaBackward : AltsRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope target middle

/-- Materialize the existential body intermediate from every pointwise
`ScopedAltFactored` proof. -/
theorem scopedAltsBifactor_of_factored
    (factored : ScopedAltsFactored validCase index source target) :
    Nonempty (ScopedAltsBifactor validCase index source target) := by
  induction factored with
  | nil =>
      exact ⟨{
        middle := []
        structural := .nil
        alphaForward := .nil
        alphaBackward := .nil
      }⟩
  | cons head tail ih =>
      rcases ih with ⟨rest⟩
      cases head with
      | ctor body =>
          rcases body with ⟨factor⟩
          exact ⟨{
            middle := .ctorAlt _ factor.middle :: rest.middle
            structural := .cons (.ctor factor.structural) rest.structural
            alphaForward := .cons (.ctor factor.alphaForward)
              rest.alphaForward
            alphaBackward := .cons (.ctor factor.alphaBackward)
              rest.alphaBackward
          }⟩
      | default body =>
          rcases body with ⟨factor⟩
          exact ⟨{
            middle := .default factor.middle :: rest.middle
            structural := .cons (.default factor.structural) rest.structural
            alphaForward := .cons (.default factor.alphaForward)
              rest.alphaForward
            alphaBackward := .cons (.default factor.alphaBackward)
              rest.alphaBackward
          }⟩

theorem scopedAltsFactored_of_tree
    (related : ScopedAltsRelated
      (ScopedCodeFactoredOnAlphaTree validCase) index source target)
    (tree : ScopedAlphaBireflexiveAlts index source) :
    ScopedAltsFactored validCase index source target := by
  induction related with
  | nil =>
      exact .nil
  | cons head tail ih =>
      cases head with
      | ctor body =>
          cases tree with
          | ctor bodyTree rest =>
              exact .cons (.ctor (body bodyTree)) (ih rest)
      | default body =>
          cases tree with
          | default bodyTree rest =>
              exact .cons (.default (body bodyTree)) (ih rest)

/-- Materialize and synchronize every recursively transformed alternative.
The resulting trace has the maximum child depth; shorter bodies receive
explicit endpoint-identity rounds. -/
theorem scopedAltsPhaseTrace_of_tree
    (related : ScopedAltsRelated
      (ScopedCodePhaseTracedOnAlphaTree validCase) index source target)
    (tree : ScopedAlphaBireflexiveAlts index source) :
    Nonempty (ScopedAltsPhaseTrace validCase index source target) := by
  induction related with
  | nil => exact ⟨.single .nil⟩
  | cons head tail ih =>
      cases head with
      | ctor body =>
          cases tree with
          | ctor bodyTree restTree =>
              rcases body bodyTree with ⟨bodyTrace⟩
              rcases ih restTree with ⟨restTrace⟩
              exact ⟨bodyTrace.consCtor restTrace⟩
      | default body =>
          cases tree with
          | default bodyTree restTree =>
              rcases body bodyTree with ⟨bodyTrace⟩
              rcases ih restTree with ⟨restTrace⟩
              exact ⟨bodyTrace.consDefault restTrace⟩

/-- Certified counterpart of `scopedAltsPhaseTrace_of_tree`; pointwise child
certificates survive depth synchronization and identity padding. -/
theorem scopedAltsPhaseCertifiedTrace_of_tree
    (related : ScopedAltsRelated
      (ScopedCodePhaseCertifiedTracedOnAlphaTree validCase)
      index source target)
    (tree : ScopedAlphaBireflexiveAlts index source) :
    Nonempty (ScopedAltsPhaseCertifiedTrace
      validCase index source target) := by
  induction related with
  | nil => exact ⟨.single .nil⟩
  | cons head tail ih =>
      cases head with
      | ctor body =>
          cases tree with
          | ctor bodyTree restTree =>
              rcases body bodyTree with ⟨bodyTrace⟩
              rcases ih restTree with ⟨restTrace⟩
              exact ⟨bodyTrace.consCtor restTrace⟩
      | default body =>
          cases tree with
          | default bodyTree restTree =>
              rcases body bodyTree with ⟨bodyTrace⟩
              rcases ih restTree with ⟨restTrace⟩
              exact ⟨bodyTrace.consDefault restTrace⟩

/-- Synchronize endpoint-certified child traces without requiring their
proof-only intermediate tables to be normalized. The ordinary trace keeps
every phase edge, while `targetIdentity` certifies every body produced by the
actual recursive traversal. -/
theorem scopedAltsPhaseEndpointCertifiedTrace_of_tree
    (related : ScopedAltsRelated
      (ScopedCodePhaseEndpointCertifiedOnCertificateTree validCase)
      index source target)
    (tree : ScopedCodeTargetCertificateAlts validCase index source) :
    Nonempty (ScopedAltsPhaseEndpointCertifiedTrace
      validCase index source target) := by
  induction related with
  | nil => exact ⟨{
      trace := .single .nil
      targetIdentity := .nil
    }⟩
  | cons head tail ih =>
      cases head with
      | ctor body =>
          cases tree with
          | ctor bodyTree restTree =>
              rcases body bodyTree with ⟨bodyTrace⟩
              rcases ih restTree with ⟨restTrace⟩
              exact ⟨{
                trace := bodyTrace.trace.consCtor restTrace.trace
                targetIdentity := .ctor
                  bodyTrace.targetCertificate.identity
                  restTrace.targetIdentity
              }⟩
      | default body =>
          cases tree with
          | default bodyTree restTree =>
              rcases body bodyTree with ⟨bodyTrace⟩
              rcases ih restTree with ⟨restTrace⟩
              exact ⟨{
                trace := bodyTrace.trace.consDefault restTrace.trace
                targetIdentity := .default
                  bodyTrace.targetCertificate.identity
                  restTrace.targetIdentity
              }⟩

/-- Selection-local evidence for a simplifier result that remains a case
table. The structural leg only needs tags accepted by the phase predicate;
the alpha leg relates all semantic selections in both directions. -/
structure ScopedAlignedCaseEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source target : LCNF.Cases .impure) : Type where
  middleAlts : Array (LCNF.Alt .impure)
  structuralSelected : ∀ tag, validCase source tag →
    SelectionRel validCase (chooseAlt tag source.alts.toList)
      (chooseAlt tag middleAlts.toList)
  alphaForwardDiscr : ScopedFVarRelated index.forwardRho
    index.sourceScope index.targetScope source.discr target.discr
  alphaForwardSelected : ∀ tag,
    CaseSelectionRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope
      (chooseAlt tag middleAlts.toList)
      (chooseAlt tag target.alts.toList)
  alphaBackwardDiscr : ScopedFVarRelated index.backwardRho
    index.targetScope index.sourceScope target.discr source.discr
  alphaBackwardSelected : ∀ tag,
    CaseSelectionRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope
      (chooseAlt tag target.alts.toList)
      (chooseAlt tag middleAlts.toList)

def ScopedAlignedCaseEvidence.bifactor
    (evidence : ScopedAlignedCaseEvidence validCase index source target) :
    ScopedCodeBifactor validCase index (.cases source) (.cases target) := by
  cases source with
  | mk typeName resultType discr sourceAlts =>
      exact {
        middle := .cases
          (.mk typeName resultType discr evidence.middleAlts)
        structural := .aligned (.cases typeName resultType discr
          sourceAlts evidence.middleAlts evidence.structuralSelected)
        alphaForward := .cases evidence.alphaForwardDiscr
          evidence.alphaForwardSelected
        alphaBackward := .cases evidence.alphaBackwardDiscr
          evidence.alphaBackwardSelected
      }

theorem ScopedAlignedCaseEvidence.factored
    (evidence : ScopedAlignedCaseEvidence validCase index source target) :
    ScopedCodeFactored validCase index (.cases source) (.cases target) :=
  evidence.bifactor.factored

def ScopedAlignedCaseEvidence.phaseResult
    (evidence : ScopedAlignedCaseEvidence validCase index source target)
    (identities : ScopedCodeTargetIdentities validCase index (.cases target)) :
    ScopedCodePhaseResult validCase index (.cases source) (.cases target) :=
  evidence.bifactor.phaseResult identities

/-- Selection-local evidence for zero/singleton simplification, where the
source case table is eliminated to one structural intermediate before the
alpha leg reaches the compiler result. -/
structure ScopedEliminatedCaseEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure) (target : LCNF.Code .impure) : Type where
  middle : LCNF.Code .impure
  structuralSelected : ∀ tag, validCase source tag →
    ElimSelectionRel validCase middle
      (chooseAlt tag source.alts.toList)
  alphaForward : CodeRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope middle target
  alphaBackward : CodeRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope target middle

def ScopedEliminatedCaseEvidence.bifactor
    (evidence : ScopedEliminatedCaseEvidence
      validCase index source target) :
    ScopedCodeBifactor validCase index (.cases source) target :=
  {
    middle := evidence.middle
    structural := .eliminate source evidence.middle
      evidence.structuralSelected
    alphaForward := evidence.alphaForward
    alphaBackward := evidence.alphaBackward
  }

theorem ScopedEliminatedCaseEvidence.factored
    (evidence : ScopedEliminatedCaseEvidence
      validCase index source target) :
    ScopedCodeFactored validCase index (.cases source) target :=
  evidence.bifactor.factored

def ScopedEliminatedCaseEvidence.phaseResult
    (evidence : ScopedEliminatedCaseEvidence validCase index source target)
    (identities : ScopedCodeTargetIdentities validCase index target) :
    ScopedCodePhaseResult validCase index (.cases source) target :=
  evidence.bifactor.phaseResult identities

/-- Phase evidence that every valid source selection for a singleton prepared
table converges on one structural intermediate, with alpha proofs from that
intermediate to the sole compiler body in both directions. -/
structure ScopedSingletonSelectionConvergence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure) (target : LCNF.Code .impure) : Type where
  middle : LCNF.Code .impure
  structuralSelected : ∀ tag, validCase source tag →
    ElimSelectionRel validCase middle
      (chooseAlt tag source.alts.toList)
  alphaForward : CodeRelated
    (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
    index.forwardRho index.sourceScope index.targetScope middle target
  alphaBackward : CodeRelated
    (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
    index.backwardRho index.targetScope index.sourceScope target middle

def ScopedSingletonSelectionConvergence.eliminated
    (converges : ScopedSingletonSelectionConvergence
      validCase index source target) :
    ScopedEliminatedCaseEvidence validCase index source target := {
  middle := converges.middle
  structuralSelected := converges.structuralSelected
  alphaForward := converges.alphaForward
  alphaBackward := converges.alphaBackward
}

def ScopedEliminatedCaseEvidence.converges
    (evidence : ScopedEliminatedCaseEvidence validCase index source target) :
    ScopedSingletonSelectionConvergence validCase index source target := {
  middle := evidence.middle
  structuralSelected := evidence.structuralSelected
  alphaForward := evidence.alphaForward
  alphaBackward := evidence.alphaBackward
}

/-- Corrected local singleton classification. A pre-existing singleton uses
one common structural branch. A singleton created by alpha folding records
the final structural elimination as a third phase. -/
inductive ScopedSingletonPhaseEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure) (target : LCNF.Code .impure) : Type where
  | direct (converges : ScopedSingletonSelectionConvergence
      validCase index source target)
  | folded (factor : ScopedCodeTrifactor validCase index
      (.cases source) target)

theorem ScopedSingletonPhaseEvidence.phaseFactored
    (evidence : ScopedSingletonPhaseEvidence validCase index source target) :
    ScopedCodePhaseFactored validCase index (.cases source) target := by
  cases evidence with
  | direct converges =>
      exact (ScopedCodeBifactor.mk converges.middle
        (.eliminate source converges.middle converges.structuralSelected)
        converges.alphaForward converges.alphaBackward).phaseFactored
  | folded factor =>
      exact factor.phaseFactored

def ScopedSingletonPhaseEvidence.phaseResult
    (evidence : ScopedSingletonPhaseEvidence validCase index source target)
    (identities : ScopedCodeTargetIdentities validCase index target) :
    ScopedCodePhaseResult validCase index (.cases source) target :=
  match evidence with
  | .direct converges => converges.eliminated.phaseResult identities
  | .folded factor => factor.phaseResult identities

/-- Phase-classified singleton evidence plus the endpoint identities needed
to continue recursive traversal. -/
structure ScopedSingletonPhaseResultEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure) (target : LCNF.Code .impure) : Type where
  phase : ScopedSingletonPhaseEvidence validCase index source target
  identities : ScopedCodeTargetIdentities validCase index target

def ScopedSingletonPhaseResultEvidence.result
    (evidence : ScopedSingletonPhaseResultEvidence
      validCase index source target) :
    ScopedCodePhaseResult validCase index (.cases source) target :=
  evidence.phase.phaseResult evidence.identities

/-- Singleton phase evidence that retains the full target certificate needed
by a later alpha-fold comparison and by certified trace padding. -/
structure ScopedSingletonPhaseCertifiedResultEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure) (target : LCNF.Code .impure) : Type where
  phase : ScopedSingletonPhaseEvidence validCase index source target
  certificate : ScopedCodeTargetCertificate validCase index target

def ScopedSingletonPhaseCertifiedResultEvidence.result
    (evidence : ScopedSingletonPhaseCertifiedResultEvidence
      validCase index source target) :
    ScopedCodePhaseCertifiedResult validCase index (.cases source) target := {
  result := evidence.phase.phaseResult {
    structural := evidence.certificate.structural
    alpha := evidence.certificate.alpha
  }
  targetSide := evidence.certificate.side
}

/-- Empty prepared tables need no branch intermediate: once the phase rules
out every valid source tag, `unreach` is the fixed structural and alpha
intermediate. -/
theorem scopedEmptyCaseEvidence_of_noValid
    (noValid : ∀ tag, validCase source tag → False) :
    Nonempty (ScopedEliminatedCaseEvidence validCase index source
      (.unreach type)) :=
  ⟨{
    middle := .unreach type
    structuralSelected := by
      intro tag valid
      exact False.elim (noValid tag valid)
    alphaForward := .terminal .unreachable
    alphaBackward := .terminal .unreachable
  }⟩

/-- Two-phase assumption for small prepared tables. Pointwise branch factors
have already been materialized. An empty result rules out every phase-valid
source tag; a direct singleton makes every such tag converge on one fixed
intermediate. A singleton created by folding alpha-renamed bodies instead uses
`ScopedSingletonPhaseEvidence.folded`. -/
structure ScopedCaseSelectionSurvivalLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  empty : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)}
      {targetAlts : List (LCNF.Alt .impure)},
    ScopedAltsBifactor validCase index sourceAlts.toList targetAlts →
    (shadowPrepareAlts
      (.mk typeName resultType discr targetAlts.toArray)).size = 0 →
    ∀ tag, validCase (.mk typeName resultType discr sourceAlts) tag →
      False
  singleton : ∀ {index : ScopeIndex} {typeName : Name}
      {resultType : Expr} {discr : FVarId}
      {sourceAlts : Array (LCNF.Alt .impure)}
      {targetAlts : List (LCNF.Alt .impure)},
    ScopedAltsBifactor validCase index sourceAlts.toList targetAlts →
    (singleton : (shadowPrepareAlts
      (.mk typeName resultType discr targetAlts.toArray)).size = 1) →
    Nonempty (ScopedSingletonSelectionConvergence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowPrepareAlts
        (.mk typeName resultType discr targetAlts.toArray))[0]!.getCode)

/-- Minimal retained-table phase witness. The structural middle may differ
from the recursively transformed table; its selected branches are connected
to the prepared compiler table by the explicit default-fold contract. -/
structure ScopedRetainedPhaseEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure)
    (targetAlts : Array (LCNF.Alt .impure)) : Type where
  middleAlts : Array (LCNF.Alt .impure)
  structuralSelected : ∀ tag, validCase source tag →
    SelectionRel validCase (chooseAlt tag source.alts.toList)
      (chooseAlt tag middleAlts.toList)
  folded : ScopedAddDefaultSelectionEvidence index middleAlts
    (shadowFilterUnreachable targetAlts)

def ScopedRetainedPhaseEvidence.aligned
    (evidence : ScopedRetainedPhaseEvidence
      validCase index source targetAlts)
    (root : ScopedAlphaBireflexive index (.cases source)) :
    ScopedAlignedCaseEvidence validCase index source
      (source.updateAlts
        (shadowAddDefaultAlt (shadowFilterUnreachable targetAlts))) := by
  cases source with
  | mk typeName resultType discr sourceAlts =>
      exact {
        middleAlts := evidence.middleAlts
        structuralSelected := evidence.structuralSelected
        alphaForwardDiscr :=
          codeRelated_cases_discr
            (left := .mk typeName resultType discr sourceAlts)
            (right := .mk typeName resultType discr sourceAlts) root.forward
        alphaForwardSelected := evidence.folded.forward
        alphaBackwardDiscr :=
          codeRelated_cases_discr
            (left := .mk typeName resultType discr sourceAlts)
            (right := .mk typeName resultType discr sourceAlts) root.backward
        alphaBackwardSelected := evidence.folded.backward
      }

/-- Retained-table evidence plus endpoint identities for the prepared target
table. -/
structure ScopedRetainedPhaseResultEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure)
    (targetAlts : Array (LCNF.Alt .impure)) : Type where
  phase : ScopedRetainedPhaseEvidence validCase index source targetAlts
  identities : ScopedCodeTargetIdentities validCase index
    (.cases (source.updateAlts
      (shadowAddDefaultAlt (shadowFilterUnreachable targetAlts))))

def ScopedRetainedPhaseResultEvidence.result
    (evidence : ScopedRetainedPhaseResultEvidence
      validCase index source targetAlts)
    (root : ScopedAlphaBireflexive index (.cases source)) :
    ScopedCodePhaseResult validCase index (.cases source)
      (.cases (source.updateAlts
        (shadowAddDefaultAlt (shadowFilterUnreachable targetAlts)))) :=
  (evidence.phase.aligned root).phaseResult evidence.identities

/-- Retained-table phase evidence with the complete rebuilt case endpoint
certificate. -/
structure ScopedRetainedPhaseCertifiedResultEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure)
    (targetAlts : Array (LCNF.Alt .impure)) : Type where
  phase : ScopedRetainedPhaseEvidence validCase index source targetAlts
  certificate : ScopedCodeTargetCertificate validCase index
    (.cases (source.updateAlts
      (shadowAddDefaultAlt (shadowFilterUnreachable targetAlts))))

def ScopedRetainedPhaseCertifiedResultEvidence.result
    (evidence : ScopedRetainedPhaseCertifiedResultEvidence
      validCase index source targetAlts)
    (root : ScopedAlphaBireflexive index (.cases source)) :
    ScopedCodePhaseCertifiedResult validCase index (.cases source)
      (.cases (source.updateAlts
        (shadowAddDefaultAlt (shadowFilterUnreachable targetAlts)))) := {
  result := (evidence.phase.aligned root).phaseResult {
    structural := evidence.certificate.structural
    alpha := evidence.certificate.alpha
  }
  targetSide := evidence.certificate.side
}

/-- Output-shape classification for one admissible nonrecursive case-kernel
step. -/
inductive ScopedCaseFactorEvidence
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex)
    (source : LCNF.Cases .impure) : LCNF.Code .impure → Prop where
  | aligned
      (evidence : ScopedAlignedCaseEvidence validCase index source target) :
      ScopedCaseFactorEvidence validCase index source (.cases target)
  | eliminated
      (evidence : ScopedEliminatedCaseEvidence validCase index source target) :
      ScopedCaseFactorEvidence validCase index source target

theorem ScopedCaseFactorEvidence.factored
    (evidence : ScopedCaseFactorEvidence validCase index source target) :
    ScopedCodeFactored validCase index (.cases source) target := by
  cases evidence with
  | aligned aligned => exact aligned.factored
  | eliminated eliminated => exact eliminated.factored

/-- Exact phase/admissibility interface for the local simplifier. Recursive
branch transformation is already proved pointwise; implementations supply the
selection facts that rule out invalid empty/singleton eliminations and the
bidirectional alpha facts used by default folding. -/
structure ScopedCaseAdmissibilityLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  simplify : ∀ {fuel : Nat} {index : ScopeIndex} {typeName : Name}
      {resultType : Expr} {discr : FVarId}
      {sourceAlts : Array (LCNF.Alt .impure)}
      {targetAlts : List (LCNF.Alt .impure)},
    sourceAlts.toList.mapM (shadowAltUsing? (shadowCode? fuel)) =
        some targetAlts →
    ScopedAltsFactored validCase index sourceAlts.toList targetAlts →
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedCaseFactorEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowSimplifyCases
        (.mk typeName resultType discr targetAlts.toArray))

/-- Phase-facing decomposition of the local simplifier law along its three
actual output shapes. The recursive branch factors and source hygiene are
shared inputs; a concrete phase can establish empty, singleton, and retained
case tables independently. -/
structure ScopedCaseShapeLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  empty : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)}
      {targetAlts : List (LCNF.Alt .impure)},
    ScopedAltsFactored validCase index sourceAlts.toList targetAlts →
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    (shadowPrepareAlts
      (.mk typeName resultType discr targetAlts.toArray)).size = 0 →
    Nonempty (ScopedEliminatedCaseEvidence validCase index
      (.mk typeName resultType discr sourceAlts) (.unreach resultType))
  singleton : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)}
      {targetAlts : List (LCNF.Alt .impure)},
    ScopedAltsFactored validCase index sourceAlts.toList targetAlts →
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    (singleton : (shadowPrepareAlts
      (.mk typeName resultType discr targetAlts.toArray)).size = 1) →
    Nonempty (ScopedEliminatedCaseEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowPrepareAlts
        (.mk typeName resultType discr targetAlts.toArray))[0]!.getCode)
  retained : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)}
      {targetAlts : List (LCNF.Alt .impure)},
    ScopedAltsFactored validCase index sourceAlts.toList targetAlts →
    (shadowPrepareAlts
      (.mk typeName resultType discr targetAlts.toArray)).size ≠ 0 →
    (shadowPrepareAlts
      (.mk typeName resultType discr targetAlts.toArray)).size ≠ 1 →
    Nonempty (ScopedRetainedPhaseEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      targetAlts.toArray)

/-- Canonical semantic validity predicate for case tags: the selected source
arm exists and is not syntactically unreachable. -/
def ReachableCaseTag (cases : LCNF.Cases .impure) (tag : Nat) : Prop :=
  ∃ branch,
    chooseAlt tag cases.alts.toList = some branch ∧
    Fir.LeanIR.Passes.SimpCase.isUnreachable branch = false

/-- A caller-selected phase predicate refines canonical reachable selection.
This is the minimal bridge missing from plain `CodeReadyAt`: runtime readiness
supplies a valid tag, while this law supplies its executable source arm. -/
structure ScopedCaseReachableSelectionLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  selected : ∀ {cases : LCNF.Cases .impure} {tag : Nat},
    validCase cases tag → ReachableCaseTag cases tag

/-- Empty-table selection survival, isolated from alpha and endpoint facts.
This is the only semantic input needed to construct the fixed `unreach`
intermediate. -/
structure ScopedCaseEmptySelectionLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  empty : ∀ {typeName : Name} {resultType : Expr} {discr : FVarId}
      {sourceAlts : Array (LCNF.Alt .impure)},
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 0 →
    ∀ tag, validCase (.mk typeName resultType discr sourceAlts) tag → False

/-- Reachable source selection discharges the empty-table component: the
concrete preparation pipeline cannot erase the selected arm. -/
theorem scopedCaseEmptySelectionLaws_of_reachableSelection
    (selection : ScopedCaseReachableSelectionLaws validCase) :
    ScopedCaseEmptySelectionLaws validCase where
  empty := by
    intro typeName resultType discr sourceAlts empty tag valid
    rcases selection.selected valid with ⟨branch, selected, reachable⟩
    exact shadowPrepareAlts_size_ne_zero_of_selected selected reachable empty

/-- Canonical reachable validity satisfies the selection bridge by
construction. -/
theorem reachableCaseTag_selectionLaws :
    ScopedCaseReachableSelectionLaws ReachableCaseTag where
  selected := fun valid => valid

/-- Consequently, canonical reachable validity needs no additional premise
for its empty-table component. -/
theorem reachableCaseTag_emptySelectionLaws :
    ScopedCaseEmptySelectionLaws ReachableCaseTag :=
  scopedCaseEmptySelectionLaws_of_reachableSelection
    reachableCaseTag_selectionLaws

/-- Singleton phase classification without endpoint identities. Direct
selection survival and fold-created singleton elimination remain distinct
constructors of `ScopedSingletonPhaseEvidence`. -/
structure ScopedCaseSingletonPhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  singleton : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    Nonempty (ScopedSingletonPhaseEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowPrepareAlts
        (.mk typeName resultType discr sourceAlts))[0]!.getCode)

/-- Singleton classification for the invariant-carrying recursive path. Both
direct and fold-created results retain the selected body's endpoint
certificate. -/
structure ScopedCaseCertifiedSingletonPhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  singleton : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseCertifiedResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    Nonempty (ScopedSingletonPhaseCertifiedResultEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowPrepareAlts
        (.mk typeName resultType discr sourceAlts))[0]!.getCode)

/-- Direct-singleton convergence when unreachable filtering itself leaves one
arm. Pointwise alternative identities supply structural and alpha reflexivity
for that exact array entry, including entries hidden from case selectors. -/
theorem scopedDirectSingletonSelectionConvergence
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (alternatives : ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList)
    (singleton : (shadowFilterUnreachable sourceAlts).size = 1) :
    Nonempty (ScopedSingletonSelectionConvergence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowFilterUnreachable sourceAlts)[0]!.getCode) := by
  rcases Array.size_eq_one_iff.mp singleton with ⟨alt, filteredEq⟩
  have altFiltered : alt ∈ shadowFilterUnreachable sourceAlts := by
    rw [filteredEq]
    simp
  have altSource : alt ∈ sourceAlts.toList := by
    have altSourceArray : alt ∈ sourceAlts := by
      exact Array.mem_of_mem_filter altFiltered
    exact Array.mem_def.mp altSourceArray
  rcases alternatives.targetBodyIdentity_of_mem altSource with
    ⟨bodyIdentity⟩
  have convergence : ScopedSingletonSelectionConvergence validCase index
      (.mk typeName resultType discr sourceAlts) alt.getCode := {
    middle := alt.getCode
    structuralSelected := by
      intro tag valid
      rcases selection.selected valid with ⟨branch, selected, reachable⟩
      have selectedFiltered :=
        chooseAlt_shadowFilterUnreachable_of_selected selected reachable
      change chooseAlt tag (shadowFilterUnreachable sourceAlts).toList =
        some branch at selectedFiltered
      rw [filteredEq] at selectedFiltered
      have branchEq :=
        chooseAlt_singleton_eq_some_getCode selectedFiltered
      rw [selected, branchEq]
      exact .some bodyIdentity.targetRefl
    alphaForward := bodyIdentity.targetAlpha.forward
    alphaBackward := bodyIdentity.targetAlpha.backward
  }
  simpa [filteredEq] using Nonempty.intro convergence

/-- The genuinely folded half of singleton classification. It is consulted
only when filtering did not already produce the final singleton. -/
structure ScopedCaseFoldedSingletonPhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  folded : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowFilterUnreachable sourceAlts).size ≠ 1 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    Nonempty (ScopedCodeTrifactor validCase index
      (.cases (.mk typeName resultType discr sourceAlts))
      (shadowPrepareAlts
        (.mk typeName resultType discr sourceAlts))[0]!.getCode)

/-- Fold-created singleton contract for the invariant-carrying path. The
result includes the selected endpoint certificate rather than discarding it
after the final structural elimination leg. -/
structure ScopedCaseFoldedCertifiedSingletonPhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  folded : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseCertifiedResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowFilterUnreachable sourceAlts).size ≠ 1 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    Nonempty (ScopedSingletonPhaseCertifiedResultEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowPrepareAlts
        (.mk typeName resultType discr sourceAlts))[0]!.getCode)

/-- Minimal presentation of the alpha-changing middle of a genuine default
fold. `middleAlts` may replace one constructor by a default so that selections
outside the source constructor domain are defined on both alpha sides.
`sourceSelection` is syntax-only; pointwise endpoint identities later turn it
into the first `CodeRel` leg. -/
structure ScopedFoldedAlphaEvidence
    (index : ScopeIndex) (sourceAlts : Array (LCNF.Alt .impure)) : Type where
  middleAlts : Array (LCNF.Alt .impure)
  sourceSelection : ∀ {tag : Nat} {branch : LCNF.Code .impure},
    chooseAlt tag sourceAlts.toList = some branch →
    Fir.LeanIR.Passes.SimpCase.isUnreachable branch = false →
    chooseAlt tag middleAlts.toList = some branch
  folded : ScopedAddDefaultSelectionEvidence index middleAlts
    (shadowFilterUnreachable sourceAlts)

/-- The canonical proof intermediate discharges its source-selection field
from reachable filtering and the generic append-default selection theorem.
After this constructor, only the selected-branch alpha relation between the
canonical middle and the actual folded table remains. -/
def scopedFoldedAlphaEvidence_of_addDefault
    (folded : ScopedAddDefaultSelectionEvidence index
      (shadowAddDefaultMiddle (shadowFilterUnreachable sourceAlts))
      (shadowFilterUnreachable sourceAlts)) :
    ScopedFoldedAlphaEvidence index sourceAlts := {
  middleAlts := shadowAddDefaultMiddle
    (shadowFilterUnreachable sourceAlts)
  sourceSelection := by
    intro tag branch selected reachable
    exact chooseAlt_shadowAddDefaultMiddle_of_selected
      (chooseAlt_shadowFilterUnreachable_of_selected selected reachable)
  folded := folded
}

/-- Pure alpha boundary for genuine default folding. The canonical proof
intermediate and its structural selection behavior are fixed transparently;
implementations provide only the two selected-branch alpha orientations used
by `shadowAddDefaultAlt`. -/
structure ScopedCaseAddDefaultAlphaLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  folded : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowFilterUnreachable sourceAlts).size ≠ 1 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    ScopedAddDefaultSelectionEvidence index
      (shadowAddDefaultMiddle (shadowFilterUnreachable sourceAlts))
      (shadowFilterUnreachable sourceAlts)

/-- Certified pure-alpha boundary: recursive alternatives provide the full
endpoint certificate for every body instead of relying on a global recovery
law from weaker identities. -/
structure ScopedCaseAddDefaultCertifiedAlphaLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  folded : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAltsPhaseCertifiedResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowFilterUnreachable sourceAlts).size ≠ 1 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    ScopedAddDefaultSelectionEvidence index
      (shadowAddDefaultMiddle (shadowFilterUnreachable sourceAlts))
      (shadowFilterUnreachable sourceAlts)

/-- Scoped conversion required after the transparent fold has identified two
selected bodies and the exact upstream alpha check between them. The identity
records provide the hygiene, metadata, and endpoint structure from which the
trusted adapter will derive this law; the table algorithm itself is absent
from the contract. -/
structure ScopedFoldAlphaSideLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  side : ∀ {index : ScopeIndex} {left right : LCNF.Code .impure},
    ScopedCodeTargetIdentities validCase index left →
    ScopedCodeTargetIdentities validCase index right →
    left.alphaEqv right = true →
    CodeSideConditions
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope left right

/-- Factored endpoint obligation for default folding. Endpoint certificates
carry all unary hygiene and normalization facts; the cross-code field retains
only exact runtime type compatibility, which Lean's Boolean alpha checker does
not imply. -/
structure ScopedFoldAlphaEndpointLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  self : ∀ {index : ScopeIndex} {code : LCNF.Code .impure},
    ScopedCodeTargetIdentities validCase index code →
    ScopedCodeSideReflexive index code
  runtimeTypes : ∀ {index : ScopeIndex} {left right : LCNF.Code .impure},
    ScopedCodeTargetIdentities validCase index left →
    ScopedCodeTargetIdentities validCase index right →
    left.alphaEqv right = true →
    CodeRuntimeTypesEq left right

/-- Unary endpoint invariants plus exact runtime type compatibility construct
the complete forward side-condition law. -/
theorem scopedFoldAlphaSideLaws_of_endpoints
    (endpoints : ScopedFoldAlphaEndpointLaws validCase) :
    ScopedFoldAlphaSideLaws validCase where
  side := by
    intro index left right leftIdentities rightIdentities accepted
    exact (endpoints.runtimeTypes leftIdentities rightIdentities accepted).sideConditions
      (endpoints.self leftIdentities)
      (endpoints.self rightIdentities).target

/-- Exact cross-code runtime type obligation when endpoint certificates are
already carried by the recursive phase trace. -/
structure ScopedFoldRuntimeTypeLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  compatible : ∀ {index : ScopeIndex} {left right : LCNF.Code .impure},
    ScopedCodeTargetCertificate validCase index left →
    ScopedCodeTargetCertificate validCase index right →
    left.alphaEqv right = true →
    CodeRuntimeTypesEq left right

/-- Certified fold transport consumes the actual endpoint certificates from
the recursive alternatives instead of recovering them from a global law. -/
structure ScopedFoldAlphaCertifiedTransportLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  related : ∀ {index : ScopeIndex} {left right : LCNF.Code .impure},
    ScopedCodeTargetCertificate validCase index left →
    ScopedCodeTargetCertificate validCase index right →
    left.alphaEqv right = true →
    CodeRelated
        (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
        index.forwardRho index.sourceScope index.targetScope left right ∧
      CodeRelated
        (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
        index.backwardRho index.targetScope index.sourceScope right left

/-- The certified endpoint path still uses exactly one audited upstream
comparison; reverse orientation remains kernel-derived. -/
theorem scopedFoldAlphaCertifiedTransportLaws_of_upstreamBridge
    (bridge : UpstreamBridge)
    (runtimeTypes : ScopedFoldRuntimeTypeLaws validCase) :
    ScopedFoldAlphaCertifiedTransportLaws validCase where
  related := by
    intro index left right leftCertificate rightCertificate accepted
    have side : CodeSideConditions
        (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
        index.forwardRho index.sourceScope index.targetScope left right :=
      (runtimeTypes.compatible
        leftCertificate rightCertificate accepted).sideConditions
          leftCertificate.side rightCertificate.side.target
    have forward : CodeRelated
        (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
        index.forwardRho index.sourceScope index.targetScope left right :=
      codeRelated_of_local_accepts side
        (index.localAcceptsAtForward_of_upstream bridge left right accepted)
    exact ⟨forward, index.codeRelated_symm forward⟩

/-- Scoped conversion required after the transparent fold has identified two
selected bodies and the exact upstream alpha check between them. -/
structure ScopedFoldAlphaTransportLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  related : ∀ {index : ScopeIndex} {left right : LCNF.Code .impure},
    ScopedCodeTargetIdentities validCase index left →
    ScopedCodeTargetIdentities validCase index right →
    left.alphaEqv right = true →
    CodeRelated
        (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
        index.forwardRho index.sourceScope index.targetScope left right ∧
      CodeRelated
        (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
        index.backwardRho index.targetScope index.sourceScope right left

/-- The single audited upstream bridge plus explicit cross-code side
conditions constructs the complete bidirectional transport law. Only the
forward local check is replayed; the reverse `CodeRelated` orientation is a
kernel theorem from the paired scope-index renamings. -/
theorem scopedFoldAlphaTransportLaws_of_upstreamBridge
    (bridge : UpstreamBridge)
    (sides : ScopedFoldAlphaSideLaws validCase) :
    ScopedFoldAlphaTransportLaws validCase where
  related := by
    intro index left right leftIdentities rightIdentities accepted
    have forward : CodeRelated
        (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
        index.forwardRho index.sourceScope index.targetScope left right :=
      codeRelated_of_local_accepts
        (sides.side leftIdentities rightIdentities accepted)
        (index.localAcceptsAtForward_of_upstream bridge left right accepted)
    exact ⟨forward, index.codeRelated_symm forward⟩

/-- The transparent fold discharges the complete table/selector part of the
alpha boundary. What remains is only scoped soundness of one successful
upstream body comparison, supplied uniformly by `ScopedFoldAlphaTransportLaws`.
-/
theorem scopedCaseAddDefaultAlphaLaws_of_transport
    (transport : ScopedFoldAlphaTransportLaws validCase) :
    ScopedCaseAddDefaultAlphaLaws validCase where
  folded := by
    intro index typeName resultType discr sourceAlts alternatives
      filteredNotSingleton preparedSingleton
    have foldedSingleton :
        (shadowAddDefaultAlt
          (shadowFilterUnreachable sourceAlts)).size = 1 := by
      simpa [shadowPrepareAlts, LCNF.Cases.alts] using preparedSingleton
    have filteredLarge :
        1 < (shadowFilterUnreachable sourceAlts).size :=
      one_lt_size_of_shadowAddDefaultAlt_singleton
        filteredNotSingleton foldedSingleton
    have filteredNonempty :
        (shadowFilterUnreachable sourceAlts).size ≠ 0 := by omega
    have representativeMemberFiltered :
        (shadowGetMaxOccs
          (shadowFilterUnreachable sourceAlts)).1 ∈
            shadowFilterUnreachable sourceAlts :=
      shadowGetMaxOccs_fst_mem filteredNonempty
    have representativeMemberSource :
        (shadowGetMaxOccs
          (shadowFilterUnreachable sourceAlts)).1 ∈ sourceAlts := by
      unfold shadowFilterUnreachable at representativeMemberFiltered
      exact (Array.mem_filter.mp representativeMemberFiltered).1
    rcases alternatives.targetBodyIdentities_of_mem (by
        simpa using representativeMemberSource) with
      ⟨representativeIdentities⟩
    have relatedAt : ∀ tag,
        CaseSelectionRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (chooseAlt tag (shadowAddDefaultMiddle
              (shadowFilterUnreachable sourceAlts)).toList)
            (chooseAlt tag (shadowAddDefaultAlt
              (shadowFilterUnreachable sourceAlts)).toList) ∧
          CaseSelectionRelated
            (leftJoins := index.targetJoins)
            (rightJoins := index.sourceJoins)
            index.backwardRho index.targetScope index.sourceScope
            (chooseAlt tag (shadowAddDefaultAlt
              (shadowFilterUnreachable sourceAlts)).toList)
            (chooseAlt tag (shadowAddDefaultMiddle
              (shadowFilterUnreachable sourceAlts)).toList) := by
      intro tag
      rcases chooseAlt_foldCreatedSingleton_alpha
          filteredNotSingleton foldedSingleton with
        ⟨middleBody, middleSelected, foldedSelected,
          ⟨middleAlt, middleMemberFiltered, middleBodyEq⟩, sameOrAlpha⟩
      have middleMemberSource : middleAlt ∈ sourceAlts := by
        unfold shadowFilterUnreachable at middleMemberFiltered
        exact (Array.mem_filter.mp middleMemberFiltered).1
      rcases alternatives.targetBodyIdentities_of_mem (by
          simpa using middleMemberSource) with ⟨rawMiddleIdentities⟩
      have middleIdentities :
          ScopedCodeTargetIdentities validCase index middleBody := by
        simpa [middleBodyEq] using rawMiddleIdentities
      have directions :
          CodeRelated
              (leftJoins := index.sourceJoins)
              (rightJoins := index.targetJoins)
              index.forwardRho index.sourceScope index.targetScope
              middleBody
              (shadowGetMaxOccs
                (shadowFilterUnreachable sourceAlts)).1.getCode ∧
            CodeRelated
              (leftJoins := index.targetJoins)
              (rightJoins := index.sourceJoins)
              index.backwardRho index.targetScope index.sourceScope
              (shadowGetMaxOccs
                (shadowFilterUnreachable sourceAlts)).1.getCode
              middleBody := by
        rcases sameOrAlpha with same | accepted
        · have middleAltEq : middleAlt.getCode =
              (shadowGetMaxOccs
                (shadowFilterUnreachable sourceAlts)).1.getCode :=
            middleBodyEq.trans same
          constructor
          · simpa [same, middleAltEq] using
              representativeIdentities.alpha.forward
          · simpa [same, middleAltEq] using
              representativeIdentities.alpha.backward
        · exact transport.related middleIdentities
            representativeIdentities accepted
      constructor
      · rw [middleSelected, foldedSelected]
        exact .some directions.1
      · rw [middleSelected, foldedSelected]
        exact .some directions.2
    exact {
      forward := fun tag => (relatedAt tag).1
      backward := fun tag => (relatedAt tag).2
    }

/-- Certified default folding obtains unary side conditions directly from the
recursive alternative endpoints. The table/selector proof is otherwise the
same transparent calculation as the identity-only presentation. -/
theorem scopedCaseAddDefaultCertifiedAlphaLaws_of_transport
    (transport : ScopedFoldAlphaCertifiedTransportLaws validCase) :
    ScopedCaseAddDefaultCertifiedAlphaLaws validCase where
  folded := by
    intro index typeName resultType discr sourceAlts alternatives
      filteredNotSingleton preparedSingleton
    have foldedSingleton :
        (shadowAddDefaultAlt
          (shadowFilterUnreachable sourceAlts)).size = 1 := by
      simpa [shadowPrepareAlts, LCNF.Cases.alts] using preparedSingleton
    have filteredLarge :
        1 < (shadowFilterUnreachable sourceAlts).size :=
      one_lt_size_of_shadowAddDefaultAlt_singleton
        filteredNotSingleton foldedSingleton
    have filteredNonempty :
        (shadowFilterUnreachable sourceAlts).size ≠ 0 := by omega
    have representativeMemberFiltered :
        (shadowGetMaxOccs
          (shadowFilterUnreachable sourceAlts)).1 ∈
            shadowFilterUnreachable sourceAlts :=
      shadowGetMaxOccs_fst_mem filteredNonempty
    have representativeMemberSource :
        (shadowGetMaxOccs
          (shadowFilterUnreachable sourceAlts)).1 ∈ sourceAlts := by
      unfold shadowFilterUnreachable at representativeMemberFiltered
      exact (Array.mem_filter.mp representativeMemberFiltered).1
    rcases alternatives.targetBodyCertificate_of_mem (by
        simpa using representativeMemberSource) with
      ⟨representativeCertificate⟩
    have relatedAt : ∀ tag,
        CaseSelectionRelated
            (leftJoins := index.sourceJoins)
            (rightJoins := index.targetJoins)
            index.forwardRho index.sourceScope index.targetScope
            (chooseAlt tag (shadowAddDefaultMiddle
              (shadowFilterUnreachable sourceAlts)).toList)
            (chooseAlt tag (shadowAddDefaultAlt
              (shadowFilterUnreachable sourceAlts)).toList) ∧
          CaseSelectionRelated
            (leftJoins := index.targetJoins)
            (rightJoins := index.sourceJoins)
            index.backwardRho index.targetScope index.sourceScope
            (chooseAlt tag (shadowAddDefaultAlt
              (shadowFilterUnreachable sourceAlts)).toList)
            (chooseAlt tag (shadowAddDefaultMiddle
              (shadowFilterUnreachable sourceAlts)).toList) := by
      intro tag
      rcases chooseAlt_foldCreatedSingleton_alpha
          filteredNotSingleton foldedSingleton with
        ⟨middleBody, middleSelected, foldedSelected,
          ⟨middleAlt, middleMemberFiltered, middleBodyEq⟩, sameOrAlpha⟩
      have middleMemberSource : middleAlt ∈ sourceAlts := by
        unfold shadowFilterUnreachable at middleMemberFiltered
        exact (Array.mem_filter.mp middleMemberFiltered).1
      rcases alternatives.targetBodyCertificate_of_mem (by
          simpa using middleMemberSource) with ⟨rawMiddleCertificate⟩
      have middleCertificate :
          ScopedCodeTargetCertificate validCase index middleBody := by
        simpa [middleBodyEq] using rawMiddleCertificate
      have directions :
          CodeRelated
              (leftJoins := index.sourceJoins)
              (rightJoins := index.targetJoins)
              index.forwardRho index.sourceScope index.targetScope
              middleBody
              (shadowGetMaxOccs
                (shadowFilterUnreachable sourceAlts)).1.getCode ∧
            CodeRelated
              (leftJoins := index.targetJoins)
              (rightJoins := index.sourceJoins)
              index.backwardRho index.targetScope index.sourceScope
              (shadowGetMaxOccs
                (shadowFilterUnreachable sourceAlts)).1.getCode
              middleBody := by
        rcases sameOrAlpha with same | accepted
        · have middleAltEq : middleAlt.getCode =
              (shadowGetMaxOccs
                (shadowFilterUnreachable sourceAlts)).1.getCode :=
            middleBodyEq.trans same
          constructor
          · simpa [same, middleAltEq] using
              representativeCertificate.alpha.forward
          · simpa [same, middleAltEq] using
              representativeCertificate.alpha.backward
        · exact transport.related middleCertificate
            representativeCertificate accepted
      constructor
      · rw [middleSelected, foldedSelected]
        exact .some directions.1
      · rw [middleSelected, foldedSelected]
        exact .some directions.2
    exact {
      forward := fun tag => (relatedAt tag).1
      backward := fun tag => (relatedAt tag).2
    }

/-- The irreducible semantic input for a genuine default fold. Filtering and
the final singleton elimination are structural; this contract exposes a
selection-preserving middle table and supplies only the bidirectional alpha
relation introduced by `shadowAddDefaultAlt`. The pointwise endpoint round is
available to establish scoped alpha side conditions even for
selector-shadowed alternatives. -/
structure ScopedCaseFoldedAlphaLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  folded : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowFilterUnreachable sourceAlts).size ≠ 1 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    Nonempty (ScopedFoldedAlphaEvidence index sourceAlts)

/-- Certified folded-alpha law used by the invariant-carrying recursive path. -/
structure ScopedCaseFoldedCertifiedAlphaLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  folded : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAltsPhaseCertifiedResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowFilterUnreachable sourceAlts).size ≠ 1 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    Nonempty (ScopedFoldedAlphaEvidence index sourceAlts)

/-- Lift the pure alpha boundary to the fold presentation consumed by the
three-phase constructor. No additional semantic premise is introduced. -/
theorem scopedCaseFoldedAlphaLaws_of_addDefaultAlpha
    (alpha : ScopedCaseAddDefaultAlphaLaws validCase) :
    ScopedCaseFoldedAlphaLaws validCase where
  folded := by
    intro index typeName resultType discr sourceAlts alternatives
      filteredNotSingleton preparedSingleton
    exact ⟨scopedFoldedAlphaEvidence_of_addDefault
      (alpha.folded alternatives filteredNotSingleton preparedSingleton)⟩

theorem scopedCaseFoldedCertifiedAlphaLaws_of_addDefaultAlpha
    (alpha : ScopedCaseAddDefaultCertifiedAlphaLaws validCase) :
    ScopedCaseFoldedCertifiedAlphaLaws validCase where
  folded := by
    intro index typeName resultType discr sourceAlts alternatives
      filteredNotSingleton preparedSingleton
    exact ⟨scopedFoldedAlphaEvidence_of_addDefault
      (alpha.folded alternatives filteredNotSingleton preparedSingleton)⟩

/-- Assemble singleton phase classification from the generic direct path and
the remaining fold-created singleton contract. -/
theorem scopedCaseSingletonPhaseLaws_of_reachableSelection
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (folded : ScopedCaseFoldedSingletonPhaseLaws validCase) :
    ScopedCaseSingletonPhaseLaws validCase where
  singleton := by
    intro index typeName resultType discr sourceAlts root alternatives
      preparedSingleton
    by_cases filteredSingleton :
        (shadowFilterUnreachable sourceAlts).size = 1
    · have preparedEq : shadowPrepareAlts
          (.mk typeName resultType discr sourceAlts) =
          shadowFilterUnreachable sourceAlts :=
        shadowPrepareAlts_eq_filter_of_small (by
          simp [LCNF.Cases.alts, filteredSingleton])
      rcases scopedDirectSingletonSelectionConvergence selection alternatives
          filteredSingleton with ⟨convergence⟩
      exact ⟨.direct (by simpa [preparedEq] using convergence)⟩
    · rcases folded.folded root alternatives filteredSingleton
          preparedSingleton with ⟨factor⟩
      exact ⟨.folded factor⟩

/-- Retained-table folding evidence, kept separate from the target identities
needed only when the local result is appended to a recursive trace. -/
structure ScopedCaseRetainedPhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  retained : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 0 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 1 →
    Nonempty (ScopedRetainedPhaseEvidence validCase index
      (.mk typeName resultType discr sourceAlts) sourceAlts)

/-- Retained-table folding for the invariant-carrying path. The semantic
phase witness is unchanged, while the prepared endpoint certificate is
rebuilt from the incoming case certificate and the certified recursive
alternative round. -/
structure ScopedCaseCertifiedRetainedPhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  retained : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseCertifiedResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 0 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 1 →
    Nonempty (ScopedRetainedPhaseCertifiedResultEvidence validCase index
      (.mk typeName resultType discr sourceAlts) sourceAlts)

/-- Upgrade the retained semantic law to the certified path without an
external target-identity premise. Preparation preserves table normalization
and every retained body comes from the certified recursive result. -/
theorem scopedCaseCertifiedRetainedPhaseLaws_of_retained
    (retained : ScopedCaseRetainedPhaseLaws validCase) :
    ScopedCaseCertifiedRetainedPhaseLaws validCase where
  retained := by
    intro index typeName resultType discr sourceAlts root alternatives
      nonempty nonsingleton
    rcases retained.retained root.alpha alternatives.forget nonempty
        nonsingleton with ⟨phase⟩
    have certificate := scopedPreparedCaseTargetCertificate root alternatives
    exact ⟨{
      phase := phase
      certificate := by
        simpa [shadowPrepareAlts, LCNF.Cases.alts, LCNF.Cases.updateAlts]
          using certificate
    }⟩

/-- Endpoint identities for the two nonterminal output shapes. Empty-table
identities are generic because `unreach` is structurally and alpha reflexive.
Keeping these facts independent avoids baking traversal padding into the
selection and folding contracts. -/
structure ScopedCasePhaseTargetIdentityLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  singleton : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1 →
    ScopedCodeTargetIdentities validCase index
      (shadowPrepareAlts
        (.mk typeName resultType discr sourceAlts))[0]!.getCode
  retained : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 0 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 1 →
    ScopedCodeTargetIdentities validCase index
      (.cases ((LCNF.Cases.mk typeName resultType discr sourceAlts).updateAlts
        (shadowAddDefaultAlt (shadowFilterUnreachable sourceAlts))))

/-- Derive the complete three-phase witness for a fold-created singleton.
Reachable selection makes unreachable filtering a structural step, the
fold-alpha contract supplies the only alpha-changing step, and the generic
singleton target identities justify eliminating the newly created default. -/
theorem scopedCaseFoldedSingletonPhaseLaws_of_reachableSelectionAndAlpha
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (foldAlpha : ScopedCaseFoldedAlphaLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase) :
    ScopedCaseFoldedSingletonPhaseLaws validCase where
  folded := by
    intro index typeName resultType discr sourceAlts root alternatives
      filteredNotSingleton preparedSingleton
    let source : LCNF.Cases .impure :=
      .mk typeName resultType discr sourceAlts
    let filtered : Array (LCNF.Alt .impure) :=
      shadowFilterUnreachable sourceAlts
    let prepared : Array (LCNF.Alt .impure) :=
      shadowAddDefaultAlt filtered
    rcases foldAlpha.folded alternatives filteredNotSingleton
        preparedSingleton with ⟨alphaEvidence⟩
    have targetIdentity := targetIdentities.singleton root alternatives
      preparedSingleton
    refine ⟨{
      structuralMiddle := .cases (source.updateAlts alphaEvidence.middleAlts)
      alphaMiddle := .cases (source.updateAlts prepared)
      structuralBefore := ?_
      alphaForward := ?_
      alphaBackward := ?_
      structuralAfter := ?_
    }⟩
    · apply CodeRel.aligned
      apply HeadRel.cases
      intro tag valid
      rcases selection.selected valid with ⟨branch, selected, reachable⟩
      change chooseAlt tag sourceAlts.toList = some branch at selected
      have selectedMiddle := alphaEvidence.sourceSelection selected reachable
      have selectedRefl := structuralChooseAlt_related
        (tag := tag) alternatives.materialize.targetRefl
      have branchRefl : CodeRel validCase branch branch := by
        rw [selected] at selectedRefl
        cases selectedRefl with
        | some related => exact related
      change SelectionRel validCase
        (chooseAlt tag sourceAlts.toList)
        (chooseAlt tag alphaEvidence.middleAlts.toList)
      rw [selected, selectedMiddle]
      exact .some branchRefl
    · apply CodeRelated.cases
      · have discrRelated := codeRelated_cases_discr root.forward
        change ScopedFVarRelated index.forwardRho index.sourceScope
          index.targetScope discr discr at discrRelated
        change ScopedFVarRelated index.forwardRho index.sourceScope
          index.targetScope discr discr
        exact discrRelated
      · exact alphaEvidence.folded.forward
    · apply CodeRelated.cases
      · have discrRelated := codeRelated_cases_discr root.backward
        change ScopedFVarRelated index.backwardRho index.targetScope
          index.sourceScope discr discr at discrRelated
        change ScopedFVarRelated index.backwardRho index.targetScope
          index.sourceScope discr discr
        exact discrRelated
      · exact alphaEvidence.folded.backward
    · apply CodeRel.eliminate
      intro tag valid
      have selectedPrepared :=
        chooseAlt_shadowAddDefaultAlt_of_created_singleton
          (tag := tag) filteredNotSingleton preparedSingleton
      change ElimSelectionRel validCase prepared[0]!.getCode
        (chooseAlt tag prepared.toList)
      rw [selectedPrepared]
      exact .some (by
        simpa [prepared, filtered, shadowPrepareAlts, LCNF.Cases.alts] using
          targetIdentity.structural)

/-- Certified fold-created singleton assembly. The selected endpoint
certificate is recovered from the recursive alternative result itself, so no
separate target-identity law is needed for the elimination leg. -/
theorem scopedCaseFoldedCertifiedSingletonPhaseLaws_of_reachableSelectionAndAlpha
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (foldAlpha : ScopedCaseFoldedCertifiedAlphaLaws validCase) :
    ScopedCaseFoldedCertifiedSingletonPhaseLaws validCase where
  folded := by
    intro index typeName resultType discr sourceAlts root alternatives
      filteredNotSingleton preparedSingleton
    let source : LCNF.Cases .impure :=
      .mk typeName resultType discr sourceAlts
    let filtered : Array (LCNF.Alt .impure) :=
      shadowFilterUnreachable sourceAlts
    let prepared : Array (LCNF.Alt .impure) :=
      shadowAddDefaultAlt filtered
    rcases foldAlpha.folded alternatives filteredNotSingleton
        preparedSingleton with ⟨alphaEvidence⟩
    rcases alternatives.preparedSingletonCertificate preparedSingleton with
      ⟨targetCertificate⟩
    refine ⟨{
      phase := .folded {
        structuralMiddle := .cases
          (source.updateAlts alphaEvidence.middleAlts)
        alphaMiddle := .cases (source.updateAlts prepared)
        structuralBefore := ?_
        alphaForward := ?_
        alphaBackward := ?_
        structuralAfter := ?_
      }
      certificate := targetCertificate
    }⟩
    · apply CodeRel.aligned
      apply HeadRel.cases
      intro tag valid
      rcases selection.selected valid with ⟨branch, selected, reachable⟩
      change chooseAlt tag sourceAlts.toList = some branch at selected
      have selectedMiddle := alphaEvidence.sourceSelection selected reachable
      have selectedRefl := structuralChooseAlt_related
        (tag := tag) alternatives.forget.materialize.targetRefl
      have branchRefl : CodeRel validCase branch branch := by
        rw [selected] at selectedRefl
        cases selectedRefl with
        | some related => exact related
      change SelectionRel validCase
        (chooseAlt tag sourceAlts.toList)
        (chooseAlt tag alphaEvidence.middleAlts.toList)
      rw [selected, selectedMiddle]
      exact .some branchRefl
    · apply CodeRelated.cases
      · have discrRelated := codeRelated_cases_discr root.forward
        change ScopedFVarRelated index.forwardRho index.sourceScope
          index.targetScope discr discr at discrRelated
        change ScopedFVarRelated index.forwardRho index.sourceScope
          index.targetScope discr discr
        exact discrRelated
      · exact alphaEvidence.folded.forward
    · apply CodeRelated.cases
      · have discrRelated := codeRelated_cases_discr root.backward
        change ScopedFVarRelated index.backwardRho index.targetScope
          index.sourceScope discr discr at discrRelated
        change ScopedFVarRelated index.backwardRho index.targetScope
          index.sourceScope discr discr
        exact discrRelated
      · exact alphaEvidence.folded.backward
    · apply CodeRel.eliminate
      intro tag valid
      have selectedPrepared :=
        chooseAlt_shadowAddDefaultAlt_of_created_singleton
          (tag := tag) filteredNotSingleton preparedSingleton
      change ElimSelectionRel validCase prepared[0]!.getCode
        (chooseAlt tag prepared.toList)
      rw [selectedPrepared]
      exact .some (by
        simpa [prepared, filtered, shadowPrepareAlts, LCNF.Cases.alts] using
          targetCertificate.structural)

/-- Assemble both singleton shapes without an external endpoint-identity
contract. Direct filtering and default folding use the same certificate
extracted from the recursively processed alternative table. -/
theorem scopedCaseCertifiedSingletonPhaseLaws_of_reachableSelection
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (folded : ScopedCaseFoldedCertifiedSingletonPhaseLaws validCase) :
    ScopedCaseCertifiedSingletonPhaseLaws validCase where
  singleton := by
    intro index typeName resultType discr sourceAlts root alternatives
      preparedSingleton
    rcases alternatives.preparedSingletonCertificate preparedSingleton with
      ⟨targetCertificate⟩
    by_cases filteredSingleton :
        (shadowFilterUnreachable sourceAlts).size = 1
    · have preparedEq : shadowPrepareAlts
          (.mk typeName resultType discr sourceAlts) =
          shadowFilterUnreachable sourceAlts :=
        shadowPrepareAlts_eq_filter_of_small (by
          simp [LCNF.Cases.alts, filteredSingleton])
      rcases scopedDirectSingletonSelectionConvergence selection
          alternatives.forget filteredSingleton with ⟨convergence⟩
      exact ⟨{
        phase := .direct (by simpa [preparedEq] using convergence)
        certificate := targetCertificate
      }⟩
    · exact folded.folded root alternatives filteredSingleton
        preparedSingleton

/-- Phase-aware local output-shape contract. Empty tables retain the ordinary
elimination evidence; singleton tables explicitly classify direct versus
fold-created results; retained tables carry target identities for subsequent
recursive rounds. Nonempty shapes receive the pointwise endpoint identity
round produced while recursively transforming their alternatives. -/
structure ScopedCasePhaseShapeLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  empty : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 0 →
    Nonempty (ScopedEliminatedCaseEvidence validCase index
      (.mk typeName resultType discr sourceAlts) (.unreach resultType))
  singleton : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (singleton : (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1) →
    Nonempty (ScopedSingletonPhaseResultEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowPrepareAlts
        (.mk typeName resultType discr sourceAlts))[0]!.getCode)
  retained : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 0 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 1 →
    Nonempty (ScopedRetainedPhaseResultEvidence validCase index
      (.mk typeName resultType discr sourceAlts) sourceAlts)

/-- Invariant-carrying local output-shape contract. Each branch returns the
complete endpoint certificate needed by a following recursive round. -/
structure ScopedCaseCertifiedPhaseShapeLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  empty : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 0 →
    Nonempty (ScopedCodePhaseCertifiedResult validCase index
      (.cases (.mk typeName resultType discr sourceAlts))
      (.unreach resultType))
  singleton : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseCertifiedResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (singleton : (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size = 1) →
    Nonempty (ScopedSingletonPhaseCertifiedResultEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      (shadowPrepareAlts
        (.mk typeName resultType discr sourceAlts))[0]!.getCode)
  retained : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)},
    ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr sourceAlts)) →
    ScopedAltsPhaseCertifiedResult validCase index
      sourceAlts.toList sourceAlts.toList →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 0 →
    (shadowPrepareAlts
      (.mk typeName resultType discr sourceAlts)).size ≠ 1 →
    Nonempty (ScopedRetainedPhaseCertifiedResultEvidence validCase index
      (.mk typeName resultType discr sourceAlts) sourceAlts)

/-- Assemble the phase-aware shape contract from independently dischargeable
selection, phase-classification, folding, and endpoint-identity laws. -/
theorem scopedCasePhaseShapeLaws_of_components
    (emptySelection : ScopedCaseEmptySelectionLaws validCase)
    (singletonPhases : ScopedCaseSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase) :
    ScopedCasePhaseShapeLaws validCase where
  empty := by
    intro index typeName resultType discr sourceAlts root empty
    exact scopedEmptyCaseEvidence_of_noValid
      (emptySelection.empty empty)
  singleton := by
    intro index typeName resultType discr sourceAlts root alternatives singleton
    rcases singletonPhases.singleton root alternatives singleton with ⟨phase⟩
    exact ⟨{
      phase := phase
      identities := targetIdentities.singleton root alternatives singleton
    }⟩
  retained := by
    intro index typeName resultType discr sourceAlts root alternatives
      nonempty nonsingleton
    rcases retainedPhases.retained root alternatives nonempty nonsingleton with
      ⟨phase⟩
    exact ⟨{
      phase := phase
      identities := targetIdentities.retained root alternatives nonempty
        nonsingleton
    }⟩

/-- Assemble all certified local shapes from reachable selection and the two
nonempty semantic phase contracts. Endpoint certificates are carried by the
recursive result instead of supplied through a separate identity law. -/
theorem scopedCaseCertifiedPhaseShapeLaws_of_components
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (singletonPhases : ScopedCaseCertifiedSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseCertifiedRetainedPhaseLaws validCase) :
    ScopedCaseCertifiedPhaseShapeLaws validCase where
  empty := by
    intro index typeName resultType discr sourceAlts root empty
    rcases scopedEmptyCaseEvidence_of_noValid
        ((scopedCaseEmptySelectionLaws_of_reachableSelection selection).empty
          empty) with ⟨evidence⟩
    let certificate := scopedUnreachTargetCertificate
      validCase index resultType
    exact ⟨{
      result := evidence.phaseResult {
        structural := certificate.structural
        alpha := certificate.alpha
      }
      targetSide := certificate.side
    }⟩
  singleton := by
    intro index typeName resultType discr sourceAlts root alternatives singleton
    exact singletonPhases.singleton root.alpha alternatives singleton
  retained := by
    intro index typeName resultType discr sourceAlts root alternatives
      nonempty nonsingleton
    exact retainedPhases.retained root alternatives nonempty nonsingleton

/-- Three remaining phase components plus reachable-selection refinement are
enough for the full shape law; empty selection is now derived, not assumed. -/
theorem scopedCasePhaseShapeLaws_of_reachableSelection
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (singletonPhases : ScopedCaseSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase) :
    ScopedCasePhaseShapeLaws validCase :=
  scopedCasePhaseShapeLaws_of_components
    (scopedCaseEmptySelectionLaws_of_reachableSelection selection)
    singletonPhases retainedPhases targetIdentities

/-- Reachable selection discharges empty and direct-singleton shapes. The
only remaining singleton premise is the genuine default-fold path. -/
theorem scopedCasePhaseShapeLaws_of_reachableSelectionAndFolded
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (foldedSingletons : ScopedCaseFoldedSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase) :
    ScopedCasePhaseShapeLaws validCase :=
  scopedCasePhaseShapeLaws_of_reachableSelection selection
    (scopedCaseSingletonPhaseLaws_of_reachableSelection selection
      foldedSingletons)
    retainedPhases targetIdentities

/-- Preferred folded-singleton assembly: callers provide only the selected
alpha relation introduced by default folding. The two structural legs are
derived by `scopedCaseFoldedSingletonPhaseLaws_of_reachableSelectionAndAlpha`.
-/
theorem scopedCasePhaseShapeLaws_of_reachableSelectionAndFoldedAlpha
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (foldAlpha : ScopedCaseFoldedAlphaLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase) :
    ScopedCasePhaseShapeLaws validCase :=
  scopedCasePhaseShapeLaws_of_reachableSelectionAndFolded selection
    (scopedCaseFoldedSingletonPhaseLaws_of_reachableSelectionAndAlpha
      selection foldAlpha targetIdentities)
    retainedPhases targetIdentities

/-- The retained-table half of the phase contract. Genuine default folding
remains isolated here; empty and singleton tables are derived generically
from `ScopedCaseSelectionSurvivalLaws`. -/
structure ScopedRetainedCaseShapeLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  retained : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {sourceAlts : Array (LCNF.Alt .impure)}
      {targetAlts : List (LCNF.Alt .impure)},
    ScopedAltsFactored validCase index sourceAlts.toList targetAlts →
    (shadowPrepareAlts
      (.mk typeName resultType discr targetAlts.toArray)).size ≠ 0 →
    (shadowPrepareAlts
      (.mk typeName resultType discr targetAlts.toArray)).size ≠ 1 →
    Nonempty (ScopedRetainedPhaseEvidence validCase index
      (.mk typeName resultType discr sourceAlts)
      targetAlts.toArray)

/-- Materialize pointwise branch factors once and assemble the original
two-phase shape law. This covers empty and direct-singleton elimination;
fold-created alpha-renamed singletons require the separate three-phase local
classification above. -/
theorem scopedCaseShapeLaws_of_selectionSurvival
    (survival : ScopedCaseSelectionSurvivalLaws validCase)
    (retained : ScopedRetainedCaseShapeLaws validCase) :
    ScopedCaseShapeLaws validCase where
  empty := by
    intro index typeName resultType discr sourceAlts targetAlts
      factors root empty
    rcases scopedAltsBifactor_of_factored factors with ⟨materialized⟩
    exact scopedEmptyCaseEvidence_of_noValid
      (fun tag valid => survival.empty materialized empty tag valid)
  singleton := by
    intro index typeName resultType discr sourceAlts targetAlts
      factors root singleton
    rcases scopedAltsBifactor_of_factored factors with ⟨materialized⟩
    rcases survival.singleton materialized singleton with ⟨converges⟩
    exact ⟨converges.eliminated⟩
  retained := retained.retained

/-- Assemble the exact local admissibility law by following
`shadowSimplifyCases`' empty/singleton/retained decision tree. -/
theorem scopedCaseAdmissibilityLaws_of_shapes
    (shapes : ScopedCaseShapeLaws validCase) :
    ScopedCaseAdmissibilityLaws validCase where
  simplify := by
    intro fuel index typeName resultType discr sourceAlts targetAlts
      altsRun factors root
    let targetCases : LCNF.Cases .impure :=
      .mk typeName resultType discr targetAlts.toArray
    by_cases empty : (shadowPrepareAlts targetCases).size = 0
    · rw [shadowSimplifyCases_eq_unreach empty]
      rcases shapes.empty factors root empty with ⟨evidence⟩
      exact .eliminated evidence
    · by_cases singleton : (shadowPrepareAlts targetCases).size = 1
      · rw [shadowSimplifyCases_eq_singleton singleton]
        rcases shapes.singleton factors root singleton with ⟨evidence⟩
        exact .eliminated evidence
      · rw [shadowSimplifyCases_eq_cases empty singleton]
        rcases shapes.retained factors empty singleton with ⟨evidence⟩
        exact .aligned
          (evidence.aligned root)

/-- Direct constructor for the two-phase subset: small outputs use fixed-middle
selection survival and retained tables use their separate fold law. -/
theorem scopedCaseAdmissibilityLaws_of_selectionSurvival
    (survival : ScopedCaseSelectionSurvivalLaws validCase)
    (retained : ScopedRetainedCaseShapeLaws validCase) :
    ScopedCaseAdmissibilityLaws validCase :=
  scopedCaseAdmissibilityLaws_of_shapes
    (scopedCaseShapeLaws_of_selectionSurvival survival retained)

theorem scopedCaseKernelLaws_of_admissibility
    (admissible : ScopedCaseAdmissibilityLaws validCase) :
    ScopedCaseKernelLaws (ScopedCodeFactoredOnAlphaTree validCase) where
  simplify := by
    intro fuel index typeName resultType discr sourceAlts targetAlts
      altsRun related tree
    cases tree with
    | cases root alternativesTree =>
        exact (admissible.simplify altsRun
          (scopedAltsFactored_of_tree related alternativesTree) root).factored

/-- Exact nonrecursive phase contract for `shadowSimplifyCases`. The input
table is already recursively transformed; its pointwise endpoint identity
round is retained so the parent simplifier can inspect even selector-shadowed
entries. This law contributes exactly the parent round. -/
structure ScopedLocalCasePhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  simplify : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {alts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr alts)) →
    ScopedAltsPhaseResult validCase index alts.toList alts.toList →
    Nonempty (ScopedCodePhaseResult validCase index
      (.cases (.mk typeName resultType discr alts))
      (shadowSimplifyCases (.mk typeName resultType discr alts)))

/-- Certified nonrecursive phase contract for `shadowSimplifyCases`. The
incoming root and recursively transformed alternatives both carry their full
side certificates, and the local result returns the corresponding endpoint
certificate for the selected output shape. -/
structure ScopedLocalCaseCertifiedPhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  simplify : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {alts : Array (LCNF.Alt .impure)},
    ScopedCodeTargetCertificate validCase index
      (.cases (.mk typeName resultType discr alts)) →
    ScopedAltsPhaseCertifiedResult validCase index alts.toList alts.toList →
    Nonempty (ScopedCodePhaseCertifiedResult validCase index
      (.cases (.mk typeName resultType discr alts))
      (shadowSimplifyCases (.mk typeName resultType discr alts)))

/-- Assemble the exact local phase law by following
`shadowSimplifyCases`' output-shape decision tree. Unlike the older two-phase
assembly, the singleton branch preserves the direct/folded classification. -/
theorem scopedLocalCasePhaseLaws_of_shapes
    (shapes : ScopedCasePhaseShapeLaws validCase) :
    ScopedLocalCasePhaseLaws validCase where
  simplify := by
    intro index typeName resultType discr alts root alternatives
    let cases : LCNF.Cases .impure :=
      .mk typeName resultType discr alts
    by_cases empty : (shadowPrepareAlts cases).size = 0
    · rw [shadowSimplifyCases_eq_unreach empty]
      rcases shapes.empty root empty with ⟨evidence⟩
      exact ⟨evidence.phaseResult
        (scopedUnreachTargetIdentities validCase index resultType)⟩
    · by_cases singleton : (shadowPrepareAlts cases).size = 1
      · rw [shadowSimplifyCases_eq_singleton singleton]
        rcases shapes.singleton root alternatives singleton with ⟨evidence⟩
        exact ⟨evidence.result⟩
      · rw [shadowSimplifyCases_eq_cases empty singleton]
        rcases shapes.retained root alternatives empty singleton with ⟨evidence⟩
        exact ⟨by
          simpa [cases, shadowPrepareAlts, LCNF.Cases.alts] using
            evidence.result root⟩

/-- Assemble the certified local phase by following the same concrete
empty/singleton/retained decision tree as `shadowSimplifyCases`. -/
theorem scopedLocalCaseCertifiedPhaseLaws_of_shapes
    (shapes : ScopedCaseCertifiedPhaseShapeLaws validCase) :
    ScopedLocalCaseCertifiedPhaseLaws validCase where
  simplify := by
    intro index typeName resultType discr alts root alternatives
    let cases : LCNF.Cases .impure :=
      .mk typeName resultType discr alts
    by_cases empty : (shadowPrepareAlts cases).size = 0
    · rw [shadowSimplifyCases_eq_unreach empty]
      exact shapes.empty root empty
    · by_cases singleton : (shadowPrepareAlts cases).size = 1
      · rw [shadowSimplifyCases_eq_singleton singleton]
        rcases shapes.singleton root alternatives singleton with ⟨evidence⟩
        exact ⟨evidence.result⟩
      · rw [shadowSimplifyCases_eq_cases empty singleton]
        rcases shapes.retained root alternatives empty singleton with
          ⟨evidence⟩
        exact ⟨by
          simpa [cases, shadowPrepareAlts, LCNF.Cases.alts] using
            evidence.result root.alpha⟩

/-- Direct local-phase constructor from the four lower-level contracts. -/
theorem scopedLocalCasePhaseLaws_of_components
    (emptySelection : ScopedCaseEmptySelectionLaws validCase)
    (singletonPhases : ScopedCaseSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase) :
    ScopedLocalCasePhaseLaws validCase :=
  scopedLocalCasePhaseLaws_of_shapes
    (scopedCasePhaseShapeLaws_of_components emptySelection singletonPhases
      retainedPhases targetIdentities)

/-- Direct certified local-phase constructor. The former endpoint-identity
parameter disappears because the recursive result supplies body certificates
and preparation preserves the root certificate. -/
theorem scopedLocalCaseCertifiedPhaseLaws_of_components
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (singletonPhases : ScopedCaseCertifiedSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseCertifiedRetainedPhaseLaws validCase) :
    ScopedLocalCaseCertifiedPhaseLaws validCase :=
  scopedLocalCaseCertifiedPhaseLaws_of_shapes
    (scopedCaseCertifiedPhaseShapeLaws_of_components selection
      singletonPhases retainedPhases)

/-- The trace-aware recursive case kernel. It synchronizes all recursive
alternative traces, lifts them to the source case table, and appends the one
local round supplied by `ScopedLocalCasePhaseLaws`. -/
theorem scopedCaseTraceKernelLaws_of_localPhases
    (phases : ScopedLocalCasePhaseLaws validCase) :
    ScopedCaseKernelLaws
      (ScopedCodePhaseTracedOnAlphaTree validCase) where
  simplify := by
    intro fuel index typeName resultType discr sourceAlts targetAlts
      altsRun related tree
    cases tree with
    | cases root alternativesTree =>
        rcases scopedAltsPhaseTrace_of_tree related alternativesTree with
          ⟨alternativesTrace⟩
        have sourceRoot : ScopedAlphaBireflexive index
            (.cases (.mk typeName resultType discr
              sourceAlts.toList.toArray)) := by
          simpa using root
        have recursiveTrace : ScopedCodePhaseTrace validCase index
            (.cases (.mk typeName resultType discr sourceAlts))
            (.cases (.mk typeName resultType discr targetAlts.toArray)) := by
          simpa using alternativesTrace.casesTrace
            typeName resultType discr sourceRoot
        rcases phases.simplify recursiveTrace.targetAlpha (by
          simpa using alternativesTrace.targetIdentity) with ⟨parentRound⟩
        exact (recursiveTrace.append parentRound.trace).traced

/-- Certified arbitrary-depth case kernel. Recursive bodies may take
different numbers of phase rounds; their ordinary traces are synchronized,
the deterministic `mapM` endpoint is certified pointwise, and the certified
local case round is appended without imposing normalization on proof-only
intermediate tables. -/
theorem scopedCaseEndpointCertifiedTraceKernelLaws_of_localPhases
    (phases : ScopedLocalCaseCertifiedPhaseLaws validCase) :
    ScopedCaseKernelLaws
      (ScopedCodePhaseEndpointCertifiedOnCertificateTree validCase) where
  simplify := by
    intro fuel index typeName resultType discr sourceAlts targetAlts
      altsRun related tree
    cases tree with
    | cases root alternativesTree =>
        rcases scopedAltsPhaseEndpointCertifiedTrace_of_tree
            related alternativesTree with ⟨alternativesTrace⟩
        have recursiveTrace : ScopedCodePhaseTrace validCase index
            (.cases (.mk typeName resultType discr sourceAlts))
            (.cases (.mk typeName resultType discr targetAlts.toArray)) := by
          simpa using alternativesTrace.trace.casesTrace
            typeName resultType discr root.alpha
        have recursiveCertificate : ScopedCodeTargetCertificate validCase index
            (.cases (.mk typeName resultType discr targetAlts.toArray)) :=
          scopedTransformedCaseTargetCertificate altsRun root
            alternativesTrace.targetIdentity
        rcases phases.simplify recursiveCertificate (by
          simpa using alternativesTrace.targetIdentity) with ⟨parentRound⟩
        have recursiveCertified : ScopedCodePhaseEndpointCertifiedTrace
            validCase index
            (.cases (.mk typeName resultType discr sourceAlts))
            (.cases (.mk typeName resultType discr targetAlts.toArray)) := {
          trace := recursiveTrace
          targetSide := recursiveCertificate.side
        }
        exact ⟨recursiveCertified.append parentRound⟩

/-- Peel unchanged parameters to expose the code relation at their final
scope index. -/
theorem paramBodyRelated_finalCode
    {index : ScopeIndex} {params : List (LCNF.Param .impure)}
    {left right : LCNF.Code .impure}
    (related : ParamBodyRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope
      params params left right) :
    CodeRelated
      (leftJoins := (index.pushParamList params).sourceJoins)
      (rightJoins := (index.pushParamList params).targetJoins)
      (index.pushParamList params).forwardRho
      (index.pushParamList params).sourceScope
      (index.pushParamList params).targetScope left right := by
  induction params generalizing index with
  | nil =>
      cases related with
      | nil body => simpa [ScopeIndex.pushParamList] using body
  | cons param rest ih =>
      cases related with
      | cons _ _ _ _ tail =>
          simpa [ScopeIndex.pushParamList] using
            (ih (index := index.pushVar param.fvarId) tail)

/-- Reuse parameter freshness from a reflexive body relation while replacing
its final code relation. -/
theorem paramBodyRelated_replaceCode
    {index : ScopeIndex} {params : List (LCNF.Param .impure)}
    {source left right : LCNF.Code .impure}
    (shape : ParamBodyRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope
      params params source source)
    (body : CodeRelated
      (leftJoins := (index.pushParamList params).sourceJoins)
      (rightJoins := (index.pushParamList params).targetJoins)
      (index.pushParamList params).forwardRho
      (index.pushParamList params).sourceScope
      (index.pushParamList params).targetScope left right) :
    ParamBodyRelated
      (leftJoins := index.sourceJoins) (rightJoins := index.targetJoins)
      index.forwardRho index.sourceScope index.targetScope
      params params left right := by
  induction params generalizing index with
  | nil =>
      cases shape
      exact .nil (by
        simpa [ScopeIndex.pushParamList, ScopedCodeSideReflexive] using body)
  | cons param rest ih =>
      cases shape with
      | cons leftFresh rightFresh leftJoinFresh rightJoinFresh tail =>
          exact .cons leftFresh rightFresh leftJoinFresh rightJoinFresh
            (ih (index := index.pushVar param.fvarId) tail
              (by simpa [ScopeIndex.pushParamList,
                  ScopedCodeSideReflexive] using body))

theorem paramBodyRelated_finalCode_backward
    {index : ScopeIndex} {params : List (LCNF.Param .impure)}
    {left right : LCNF.Code .impure}
    (related : ParamBodyRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope
      params params left right) :
    CodeRelated
      (leftJoins := (index.pushParamList params).targetJoins)
      (rightJoins := (index.pushParamList params).sourceJoins)
      (index.pushParamList params).backwardRho
      (index.pushParamList params).targetScope
      (index.pushParamList params).sourceScope left right := by
  have result := paramBodyRelated_finalCode
    (index := index.reverse) related
  rw [← ScopeIndex.reverse_pushParamList] at result
  simpa [ScopeIndex.reverse] using result

theorem paramBodyRelated_replaceCode_backward
    {index : ScopeIndex} {params : List (LCNF.Param .impure)}
    {source left right : LCNF.Code .impure}
    (shape : ParamBodyRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope
      params params source source)
    (body : CodeRelated
      (leftJoins := (index.pushParamList params).targetJoins)
      (rightJoins := (index.pushParamList params).sourceJoins)
      (index.pushParamList params).backwardRho
      (index.pushParamList params).targetScope
      (index.pushParamList params).sourceScope left right) :
    ParamBodyRelated
      (leftJoins := index.targetJoins) (rightJoins := index.sourceJoins)
      index.backwardRho index.targetScope index.sourceScope
      params params left right := by
  have converted : CodeRelated
      (leftJoins := (index.reverse.pushParamList params).sourceJoins)
      (rightJoins := (index.reverse.pushParamList params).targetJoins)
      (index.reverse.pushParamList params).forwardRho
      (index.reverse.pushParamList params).sourceScope
      (index.reverse.pushParamList params).targetScope left right := by
    rw [← ScopeIndex.reverse_pushParamList]
    simpa [ScopeIndex.reverse] using body
  simpa [ScopeIndex.reverse] using
    (paramBodyRelated_replaceCode (index := index.reverse) shape converted)

/-- Reuse parameter freshness from a reflexive source side certificate while
replacing the final body with a certified transformed endpoint. -/
theorem paramBodySideConditions_replaceCode
    {index : ScopeIndex} {params : List (LCNF.Param .impure)}
    {source target : LCNF.Code .impure}
    (shape : ParamBodySideConditions
      (leftJoins := index.sourceJoins) (rightJoins := index.sourceJoins)
      index.forwardRho index.sourceScope index.sourceScope
      params params source source)
    (body : ScopedCodeSideReflexive
      (index.pushParamList params) target) :
    ParamBodySideConditions
      (leftJoins := index.sourceJoins) (rightJoins := index.sourceJoins)
      index.forwardRho index.sourceScope index.sourceScope
      params params target target := by
  unfold ScopedCodeSideReflexive at body
  induction params generalizing index with
  | nil =>
      cases shape
      exact .nil (by simpa [ScopeIndex.pushParamList] using body)
  | cons param rest ih =>
      cases shape with
      | cons leftFresh rightFresh leftJoinFresh rightJoinFresh tail =>
          exact .cons leftFresh rightFresh leftJoinFresh rightJoinFresh
            (ih (index := index.pushVar param.fvarId) tail
              (by simpa [ScopeIndex.pushParamList] using body))

/-- Explicit alpha reflexivity supplies exactly the scoped metadata and binder
freshness needed to lift a structural/alpha factor through every ordinary
recursive constructor. -/
theorem scopedCodeFactoredOnAlphaReflexive_traversalLaws :
    ScopedTraversalLaws
      (ScopedCodeFactoredOnAlphaReflexive validCase) where
  letE := by
    intro index declaration left right child parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | letE forwardDecl forwardLeftFresh forwardRightFresh
        forwardLeftJoinFresh forwardRightJoinFresh forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | letE backwardDecl backwardLeftFresh backwardRightFresh
          backwardLeftJoinFresh backwardRightJoinFresh backwardContinuation =>
        rcases child ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨factor⟩
        exact ⟨{
          middle := .let declaration factor.middle
          structural := .aligned (.let declaration factor.structural)
          alphaForward := .letE forwardDecl forwardLeftFresh forwardRightFresh
            forwardLeftJoinFresh forwardRightJoinFresh factor.alphaForward
          alphaBackward := .letE backwardDecl backwardLeftFresh backwardRightFresh
            backwardLeftJoinFresh backwardRightJoinFresh factor.alphaBackward
        }⟩
  jp := by
    intro index fvarId binderName params type leftBody rightBody
      leftContinuation rightContinuation body continuation parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | jp forwardLeftFresh forwardRightFresh forwardBody forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | jp backwardLeftFresh backwardRightFresh backwardBody backwardContinuation =>
        have bodyForward : CodeRelated
            (leftJoins := (index.pushParams params).sourceJoins)
            (rightJoins := (index.pushParams params).targetJoins)
            (index.pushParams params).forwardRho
            (index.pushParams params).sourceScope
            (index.pushParams params).targetScope leftBody leftBody := by
          simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
            LCNF.FunDecl.value] using
            (paramBodyRelated_finalCode (index := index) forwardBody)
        have bodyBackward : CodeRelated
            (leftJoins := (index.pushParams params).targetJoins)
            (rightJoins := (index.pushParams params).sourceJoins)
            (index.pushParams params).backwardRho
            (index.pushParams params).targetScope
            (index.pushParams params).sourceScope leftBody leftBody := by
          simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
            LCNF.FunDecl.value] using
            (paramBodyRelated_finalCode_backward (index := index) backwardBody)
        rcases body ⟨bodyForward, bodyBackward⟩ with ⟨bodyFactor⟩
        rcases continuation ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨continuationFactor⟩
        have replacedForward := paramBodyRelated_replaceCode
          (index := index) forwardBody bodyFactor.alphaForward
        have replacedBackward := paramBodyRelated_replaceCode_backward
          (index := index) backwardBody
          (by simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
              LCNF.FunDecl.value] using bodyFactor.alphaBackward)
        exact ⟨{
          middle := .jp
            (.mk fvarId binderName params type bodyFactor.middle)
            continuationFactor.middle
          structural := .aligned (.jp fvarId binderName params type
            bodyFactor.structural continuationFactor.structural)
          alphaForward := .jp forwardLeftFresh forwardRightFresh
            replacedForward continuationFactor.alphaForward
          alphaBackward := .jp backwardLeftFresh backwardRightFresh
            replacedBackward continuationFactor.alphaBackward
        }⟩
  jmp := by
    intro index fvarId args parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | jmp forwardTarget forwardArgs =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | jmp backwardTarget backwardArgs =>
        exact ⟨{
          middle := .jmp fvarId args
          structural := .aligned (.jmp fvarId args)
          alphaForward := .jmp forwardTarget forwardArgs
          alphaBackward := .jmp backwardTarget backwardArgs
        }⟩
  ret := by
    intro index fvarId parent
    cases parent.forward with
    | terminal forwardTerminal =>
      cases forwardTerminal with
      | ret forwardRelated =>
        cases parent.backward with
        | terminal backwardTerminal =>
          cases backwardTerminal with
          | ret backwardRelated =>
            exact ⟨{
              middle := .return fvarId
              structural := .aligned (.return fvarId)
              alphaForward := .terminal (.ret forwardRelated)
              alphaBackward := .terminal (.ret backwardRelated)
            }⟩
  unreach := by
    intro index type parent
    cases parent.forward with
    | terminal forwardTerminal =>
      cases forwardTerminal
      cases parent.backward with
      | terminal backwardTerminal =>
        cases backwardTerminal
        exact ⟨{
          middle := .unreach type
          structural := .aligned (.unreach type)
          alphaForward := .terminal .unreachable
          alphaBackward := .terminal .unreachable
        }⟩
  oset := by
    intro index fvarId fieldIndex value left right child parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | oset forwardObject forwardField forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | oset backwardObject backwardField backwardContinuation =>
        rcases child ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨factor⟩
        exact ⟨{
          middle := .oset fvarId fieldIndex value factor.middle
          structural := .aligned (.oset fvarId fieldIndex value factor.structural)
          alphaForward := .oset forwardObject forwardField factor.alphaForward
          alphaBackward := .oset backwardObject backwardField factor.alphaBackward
        }⟩
  uset := by
    intro index fvarId fieldIndex value left right child parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | uset forwardObject forwardField forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | uset backwardObject backwardField backwardContinuation =>
        rcases child ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨factor⟩
        exact ⟨{
          middle := .uset fvarId fieldIndex value factor.middle
          structural := .aligned (.uset fvarId fieldIndex value factor.structural)
          alphaForward := .uset forwardObject forwardField factor.alphaForward
          alphaBackward := .uset backwardObject backwardField factor.alphaBackward
        }⟩
  sset := by
    intro index fvarId width offset value type left right child parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | sset forwardObject forwardField forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | sset backwardObject backwardField backwardContinuation =>
        rcases child ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨factor⟩
        exact ⟨{
          middle := .sset fvarId width offset value type factor.middle
          structural := .aligned
            (.sset fvarId width offset value type factor.structural)
          alphaForward := .sset forwardObject forwardField factor.alphaForward
          alphaBackward := .sset backwardObject backwardField factor.alphaBackward
        }⟩
  setTag := by
    intro index fvarId tag left right child parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | setTag forwardObject forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | setTag backwardObject backwardContinuation =>
        rcases child ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨factor⟩
        exact ⟨{
          middle := .setTag fvarId tag factor.middle
          structural := .aligned (.setTag fvarId tag factor.structural)
          alphaForward := .setTag forwardObject factor.alphaForward
          alphaBackward := .setTag backwardObject factor.alphaBackward
        }⟩
  inc := by
    intro index fvarId amount check persistent left right child parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | inc forwardObject forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | inc backwardObject backwardContinuation =>
        rcases child ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨factor⟩
        exact ⟨{
          middle := .inc fvarId amount check persistent factor.middle
          structural := .aligned
            (.inc fvarId amount check persistent factor.structural)
          alphaForward := .inc forwardObject factor.alphaForward
          alphaBackward := .inc backwardObject factor.alphaBackward
        }⟩
  dec := by
    intro index fvarId amount check persistent objects left right child parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | dec forwardObject forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | dec backwardObject backwardContinuation =>
        rcases child ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨factor⟩
        exact ⟨{
          middle := .dec fvarId amount check persistent objects factor.middle
          structural := .aligned
            (.dec fvarId amount check persistent objects factor.structural)
          alphaForward := .dec forwardObject factor.alphaForward
          alphaBackward := .dec backwardObject factor.alphaBackward
        }⟩
  del := by
    intro index fvarId left right child parent
    cases parent.forward with
    | terminal impossible => cases impossible
    | del forwardObject forwardContinuation =>
      cases parent.backward with
      | terminal impossible => cases impossible
      | del backwardObject backwardContinuation =>
        rcases child ⟨forwardContinuation, backwardContinuation⟩ with
          ⟨factor⟩
        exact ⟨{
          middle := .del fvarId factor.middle
          structural := .aligned (.del fvarId factor.structural)
          alphaForward := .del forwardObject factor.alphaForward
          alphaBackward := .del backwardObject factor.alphaBackward
        }⟩

/-- Full-tree hygiene is stable through every non-case traversal constructor.
The existing root-reflexive laws do the semantic lifting; the tree supplies
the exact child certificate at each recursive call. -/
theorem scopedCodeFactoredOnAlphaTree_traversalLaws :
    ScopedTraversalLaws (ScopedCodeFactoredOnAlphaTree validCase) where
  letE := by
    intro index declaration left right child tree
    cases tree with
    | letE root childTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.letE
          (fun _ => child childTree)) root
  jp := by
    intro index fvarId binderName params type leftBody rightBody
      leftContinuation rightContinuation body continuation tree
    cases tree with
    | jp root bodyTree continuationTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.jp
          (fun _ => body bodyTree)
          (fun _ => continuation continuationTree)) root
  jmp := by
    intro index fvarId args tree
    exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.jmp
      index fvarId args) tree.root
  ret := by
    intro index fvarId tree
    exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.ret
      index fvarId) tree.root
  unreach := by
    intro index type tree
    exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.unreach
      index type) tree.root
  oset := by
    intro index fvarId fieldIndex value left right child tree
    cases tree with
    | oset root childTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.oset
          (fun _ => child childTree)) root
  uset := by
    intro index fvarId fieldIndex value left right child tree
    cases tree with
    | uset root childTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.uset
          (fun _ => child childTree)) root
  sset := by
    intro index fvarId width offset value type left right child tree
    cases tree with
    | sset root childTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.sset
          (fun _ => child childTree)) root
  setTag := by
    intro index fvarId tag left right child tree
    cases tree with
    | setTag root childTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.setTag
          (fun _ => child childTree)) root
  inc := by
    intro index fvarId amount check persistent left right child tree
    cases tree with
    | inc root childTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.inc
          (fun _ => child childTree)) root
  dec := by
    intro index fvarId amount check persistent objects left right child tree
    cases tree with
    | dec root childTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.dec
          (fun _ => child childTree)) root
  del := by
    intro index fvarId left right child tree
    cases tree with
    | del root childTree =>
        exact (scopedCodeFactoredOnAlphaReflexive_traversalLaws.del
          (fun _ => child childTree)) root

/-- Phase results lift through every non-case constructor. Each recursive
result is normalized to structural/alpha/structural; its recorded target
identity pads an older two-phase child when a sibling already needs the final
structural leg. The existing two-phase traversal proof supplies the common
prefix, so this theorem adds no new alpha assumptions. -/
theorem scopedCodePhaseResultOnAlphaReflexive_traversalLaws :
    ScopedTraversalLaws
      (ScopedCodePhaseResultOnAlphaReflexive validCase) where
  letE := by
    intro index declaration left right child parent
    have childReflexive : ScopedAlphaBireflexive
        (index.pushVar declaration.fvarId) left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | letE _ _ _ _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | letE _ _ _ _ _ continuation => exact continuation
    rcases child childReflexive with ⟨childResult⟩
    let childFactor := childResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.letE
      (fun _ => childFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .let declaration childFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned
          (.let declaration childFactor.structuralAfter)
      }
      targetRefl := .aligned (.let declaration childResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | letE declaration leftFresh rightFresh leftJoinFresh
              rightJoinFresh _ =>
              exact .letE declaration leftFresh rightFresh leftJoinFresh
                rightJoinFresh childResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | letE declaration leftFresh rightFresh leftJoinFresh
              rightJoinFresh _ =>
              exact .letE declaration leftFresh rightFresh leftJoinFresh
                rightJoinFresh childResult.targetAlpha.backward
    }⟩
  jp := by
    intro index fvarId binderName params type leftBody rightBody
      leftContinuation rightContinuation body continuation parent
    have bodyReflexive : ScopedAlphaBireflexive
        (index.pushParams params) leftBody := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | jp _ _ body _ =>
            simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
              LCNF.FunDecl.value] using
              (paramBodyRelated_finalCode (index := index) body)
      · cases parent.backward with
        | terminal impossible => cases impossible
        | jp _ _ body _ =>
            simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
              LCNF.FunDecl.value] using
              (paramBodyRelated_finalCode_backward (index := index) body)
    have continuationReflexive : ScopedAlphaBireflexive
        (index.pushJoin fvarId) leftContinuation := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | jp _ _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | jp _ _ _ continuation => exact continuation
    rcases body bodyReflexive with ⟨bodyResult⟩
    rcases continuation continuationReflexive with ⟨continuationResult⟩
    let bodyFactor := bodyResult.trifactor
    let continuationFactor := continuationResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.jp
      (fun _ => bodyFactor.beforeAlpha.factored)
      (fun _ => continuationFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .jp
          (.mk fvarId binderName params type bodyFactor.alphaMiddle)
          continuationFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned (.jp fvarId binderName params type
          bodyFactor.structuralAfter continuationFactor.structuralAfter)
      }
      targetRefl := .aligned (.jp fvarId binderName params type
        bodyResult.targetRefl continuationResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | jp leftFresh rightFresh bodyShape _ =>
              exact .jp leftFresh rightFresh
                (paramBodyRelated_replaceCode (index := index) bodyShape
                  (by simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
                      LCNF.FunDecl.value] using
                    bodyResult.targetAlpha.forward))
                continuationResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | jp leftFresh rightFresh bodyShape _ =>
              exact .jp leftFresh rightFresh
                (paramBodyRelated_replaceCode_backward (index := index)
                  bodyShape
                  (by simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
                      LCNF.FunDecl.value] using
                    bodyResult.targetAlpha.backward))
                continuationResult.targetAlpha.backward
    }⟩
  jmp := by
    intro index fvarId args parent
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.jmp
      index fvarId args parent) with ⟨factor⟩
    exact ⟨{
      factor := .twoPhase factor
      targetRefl := .aligned (.jmp fvarId args)
      targetAlpha := parent
    }⟩
  ret := by
    intro index fvarId parent
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.ret
      index fvarId parent) with ⟨factor⟩
    exact ⟨{
      factor := .twoPhase factor
      targetRefl := .aligned (.return fvarId)
      targetAlpha := parent
    }⟩
  unreach := by
    intro index type parent
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.unreach
      index type parent) with ⟨factor⟩
    exact ⟨{
      factor := .twoPhase factor
      targetRefl := .aligned (.unreach type)
      targetAlpha := parent
    }⟩
  oset := by
    intro index fvarId fieldIndex value left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | oset _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | oset _ _ continuation => exact continuation
    rcases child childReflexive with ⟨childResult⟩
    let childFactor := childResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.oset
      (fun _ => childFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .oset fvarId fieldIndex value childFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned
          (.oset fvarId fieldIndex value childFactor.structuralAfter)
      }
      targetRefl := .aligned
        (.oset fvarId fieldIndex value childResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | oset object field _ =>
              exact .oset object field childResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | oset object field _ =>
              exact .oset object field childResult.targetAlpha.backward
    }⟩
  uset := by
    intro index fvarId fieldIndex value left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | uset _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | uset _ _ continuation => exact continuation
    rcases child childReflexive with ⟨childResult⟩
    let childFactor := childResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.uset
      (fun _ => childFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .uset fvarId fieldIndex value childFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned
          (.uset fvarId fieldIndex value childFactor.structuralAfter)
      }
      targetRefl := .aligned
        (.uset fvarId fieldIndex value childResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | uset object field _ =>
              exact .uset object field childResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | uset object field _ =>
              exact .uset object field childResult.targetAlpha.backward
    }⟩
  sset := by
    intro index fvarId width offset value type left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | sset _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | sset _ _ continuation => exact continuation
    rcases child childReflexive with ⟨childResult⟩
    let childFactor := childResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.sset
      (fun _ => childFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .sset fvarId width offset value type childFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned
          (.sset fvarId width offset value type childFactor.structuralAfter)
      }
      targetRefl := .aligned
        (.sset fvarId width offset value type childResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | sset object field _ =>
              exact .sset object field childResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | sset object field _ =>
              exact .sset object field childResult.targetAlpha.backward
    }⟩
  setTag := by
    intro index fvarId tag left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | setTag _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | setTag _ continuation => exact continuation
    rcases child childReflexive with ⟨childResult⟩
    let childFactor := childResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.setTag
      (fun _ => childFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .setTag fvarId tag childFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned
          (.setTag fvarId tag childFactor.structuralAfter)
      }
      targetRefl := .aligned
        (.setTag fvarId tag childResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | setTag object _ =>
              exact .setTag object childResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | setTag object _ =>
              exact .setTag object childResult.targetAlpha.backward
    }⟩
  inc := by
    intro index fvarId amount check persistent left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | inc _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | inc _ continuation => exact continuation
    rcases child childReflexive with ⟨childResult⟩
    let childFactor := childResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.inc
      (fun _ => childFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .inc fvarId amount check persistent childFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned
          (.inc fvarId amount check persistent childFactor.structuralAfter)
      }
      targetRefl := .aligned
        (.inc fvarId amount check persistent childResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | inc object _ =>
              exact .inc object childResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | inc object _ =>
              exact .inc object childResult.targetAlpha.backward
    }⟩
  dec := by
    intro index fvarId amount check persistent objects left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | dec _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | dec _ continuation => exact continuation
    rcases child childReflexive with ⟨childResult⟩
    let childFactor := childResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.dec
      (fun _ => childFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .dec fvarId amount check persistent objects
          childFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned (.dec fvarId amount check persistent objects
          childFactor.structuralAfter)
      }
      targetRefl := .aligned (.dec fvarId amount check persistent objects
        childResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | dec object _ =>
              exact .dec object childResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | dec object _ =>
              exact .dec object childResult.targetAlpha.backward
    }⟩
  del := by
    intro index fvarId left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | del _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | del _ continuation => exact continuation
    rcases child childReflexive with ⟨childResult⟩
    let childFactor := childResult.trifactor
    rcases (scopedCodeFactoredOnAlphaReflexive_traversalLaws.del
      (fun _ => childFactor.beforeAlpha.factored) parent) with ⟨lifted⟩
    exact ⟨{
      factor := .threePhase {
        structuralMiddle := lifted.middle
        alphaMiddle := .del fvarId childFactor.alphaMiddle
        structuralBefore := lifted.structural
        alphaForward := lifted.alphaForward
        alphaBackward := lifted.alphaBackward
        structuralAfter := .aligned
          (.del fvarId childFactor.structuralAfter)
      }
      targetRefl := .aligned (.del fvarId childResult.targetRefl)
      targetAlpha := by
        constructor
        · cases parent.forward with
          | terminal impossible => cases impossible
          | del object _ =>
              exact .del object childResult.targetAlpha.forward
        · cases parent.backward with
          | terminal impossible => cases impossible
          | del object _ =>
              exact .del object childResult.targetAlpha.backward
    }⟩

/-- Arbitrary phase traces lift through every non-case constructor. Unary
contexts map each round directly; join points zip body and continuation
traces, padding the shorter trace with explicit identity rounds. -/
theorem scopedCodePhaseTracedOnAlphaReflexive_traversalLaws :
    ScopedTraversalLaws
      (ScopedCodePhaseTracedOnAlphaReflexive validCase) where
  letE := by
    intro index declaration left right child parent
    have childReflexive : ScopedAlphaBireflexive
        (index.pushVar declaration.fvarId) left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | letE _ _ _ _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | letE _ _ _ _ _ continuation => exact continuation
    rcases child childReflexive with ⟨trace⟩
    exact trace.lift
      (wrap := fun code => .let declaration code)
      (roundLift := fun round root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.letE
          (fun _ => ⟨round⟩) root)
      parent
  jp := by
    intro index fvarId binderName params type leftBody rightBody
      leftContinuation rightContinuation body continuation parent
    have bodyReflexive : ScopedAlphaBireflexive
        (index.pushParams params) leftBody := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | jp _ _ body _ =>
            simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
              LCNF.FunDecl.value] using
              (paramBodyRelated_finalCode (index := index) body)
      · cases parent.backward with
        | terminal impossible => cases impossible
        | jp _ _ body _ =>
            simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
              LCNF.FunDecl.value] using
              (paramBodyRelated_finalCode_backward (index := index) body)
    have continuationReflexive : ScopedAlphaBireflexive
        (index.pushJoin fvarId) leftContinuation := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | jp _ _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | jp _ _ _ continuation => exact continuation
    rcases body bodyReflexive with ⟨bodyTrace⟩
    rcases continuation continuationReflexive with ⟨continuationTrace⟩
    exact bodyTrace.zip continuationTrace
      (wrap := fun body continuation =>
        .jp (.mk fvarId binderName params type body) continuation)
      (roundLift := fun bodyRound continuationRound root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.jp
          (fun _ => ⟨bodyRound⟩) (fun _ => ⟨continuationRound⟩) root)
      parent
  jmp := by
    intro index fvarId args parent
    exact (scopedCodePhaseTracedOnAlphaReflexive_of_result
      (scopedCodePhaseResultOnAlphaReflexive_traversalLaws.jmp
        index fvarId args)) parent
  ret := by
    intro index fvarId parent
    exact (scopedCodePhaseTracedOnAlphaReflexive_of_result
      (scopedCodePhaseResultOnAlphaReflexive_traversalLaws.ret
        index fvarId)) parent
  unreach := by
    intro index type parent
    exact (scopedCodePhaseTracedOnAlphaReflexive_of_result
      (scopedCodePhaseResultOnAlphaReflexive_traversalLaws.unreach
        index type)) parent
  oset := by
    intro index fvarId fieldIndex value left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | oset _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | oset _ _ continuation => exact continuation
    rcases child childReflexive with ⟨trace⟩
    exact trace.lift
      (wrap := fun code => .oset fvarId fieldIndex value code)
      (roundLift := fun round root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.oset
          (fun _ => ⟨round⟩) root)
      parent
  uset := by
    intro index fvarId fieldIndex value left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | uset _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | uset _ _ continuation => exact continuation
    rcases child childReflexive with ⟨trace⟩
    exact trace.lift
      (wrap := fun code => .uset fvarId fieldIndex value code)
      (roundLift := fun round root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.uset
          (fun _ => ⟨round⟩) root)
      parent
  sset := by
    intro index fvarId width offset value type left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | sset _ _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | sset _ _ continuation => exact continuation
    rcases child childReflexive with ⟨trace⟩
    exact trace.lift
      (wrap := fun code =>
        .sset fvarId width offset value type code)
      (roundLift := fun round root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.sset
          (fun _ => ⟨round⟩) root)
      parent
  setTag := by
    intro index fvarId tag left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | setTag _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | setTag _ continuation => exact continuation
    rcases child childReflexive with ⟨trace⟩
    exact trace.lift
      (wrap := fun code => .setTag fvarId tag code)
      (roundLift := fun round root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.setTag
          (fun _ => ⟨round⟩) root)
      parent
  inc := by
    intro index fvarId amount check persistent left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | inc _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | inc _ continuation => exact continuation
    rcases child childReflexive with ⟨trace⟩
    exact trace.lift
      (wrap := fun code =>
        .inc fvarId amount check persistent code)
      (roundLift := fun round root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.inc
          (fun _ => ⟨round⟩) root)
      parent
  dec := by
    intro index fvarId amount check persistent objects left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | dec _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | dec _ continuation => exact continuation
    rcases child childReflexive with ⟨trace⟩
    exact trace.lift
      (wrap := fun code =>
        .dec fvarId amount check persistent objects code)
      (roundLift := fun round root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.dec
          (fun _ => ⟨round⟩) root)
      parent
  del := by
    intro index fvarId left right child parent
    have childReflexive : ScopedAlphaBireflexive index left := by
      constructor
      · cases parent.forward with
        | terminal impossible => cases impossible
        | del _ continuation => exact continuation
      · cases parent.backward with
        | terminal impossible => cases impossible
        | del _ continuation => exact continuation
    rcases child childReflexive with ⟨trace⟩
    exact trace.lift
      (wrap := fun code => .del fvarId code)
      (roundLift := fun round root =>
        scopedCodePhaseResultOnAlphaReflexive_traversalLaws.del
          (fun _ => ⟨round⟩) root)
      parent

/-- Full-tree hygiene is stable through trace lifting at every non-case
constructor. The root law performs round alignment; the tree supplies the
original child certificates required to start each trace. -/
theorem scopedCodePhaseTracedOnAlphaTree_traversalLaws :
    ScopedTraversalLaws
      (ScopedCodePhaseTracedOnAlphaTree validCase) where
  letE := by
    intro index declaration left right child tree
    cases tree with
    | letE root childTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.letE
          (fun _ => child childTree)) root
  jp := by
    intro index fvarId binderName params type leftBody rightBody
      leftContinuation rightContinuation body continuation tree
    cases tree with
    | jp root bodyTree continuationTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.jp
          (fun _ => body bodyTree)
          (fun _ => continuation continuationTree)) root
  jmp := by
    intro index fvarId args tree
    exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.jmp
      index fvarId args) tree.root
  ret := by
    intro index fvarId tree
    exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.ret
      index fvarId) tree.root
  unreach := by
    intro index type tree
    exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.unreach
      index type) tree.root
  oset := by
    intro index fvarId fieldIndex value left right child tree
    cases tree with
    | oset root childTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.oset
          (fun _ => child childTree)) root
  uset := by
    intro index fvarId fieldIndex value left right child tree
    cases tree with
    | uset root childTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.uset
          (fun _ => child childTree)) root
  sset := by
    intro index fvarId width offset value type left right child tree
    cases tree with
    | sset root childTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.sset
          (fun _ => child childTree)) root
  setTag := by
    intro index fvarId tag left right child tree
    cases tree with
    | setTag root childTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.setTag
          (fun _ => child childTree)) root
  inc := by
    intro index fvarId amount check persistent left right child tree
    cases tree with
    | inc root childTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.inc
          (fun _ => child childTree)) root
  dec := by
    intro index fvarId amount check persistent objects left right child tree
    cases tree with
    | dec root childTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.dec
          (fun _ => child childTree)) root
  del := by
    intro index fvarId left right child tree
    cases tree with
    | del root childTree =>
        exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.del
          (fun _ => child childTree)) root

/-- Endpoint certification is stable through every non-case constructor.
Ordinary trace lifting retains the non-lockstep schedule; constructor-local
scope and metadata facts come from the source root certificate, with only the
recursively transformed endpoint side certificates replaced. -/
theorem scopedCodePhaseEndpointCertifiedOnCertificateTree_traversalLaws :
    ScopedTraversalLaws
      (ScopedCodePhaseEndpointCertifiedOnCertificateTree validCase) where
  letE := by
    intro index declaration left right child tree
    cases tree with
    | letE root childTree =>
        rcases child childTree with ⟨childTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.letE
            (fun _ => childTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.let declaration right) := by
          cases root.side with
          | letE typeEq leftValueScoped rightValueScoped boxTypesEq
              leftFresh rightFresh leftJoinFresh rightJoinFresh continuation =>
            exact .letE typeEq leftValueScoped rightValueScoped boxTypesEq
              leftFresh rightFresh leftJoinFresh rightJoinFresh
              childTrace.targetSide
        exact ⟨{ trace := trace, targetSide := targetSide }⟩
  jp := by
    intro index fvarId binderName params type leftBody rightBody
      leftContinuation rightContinuation body continuation tree
    cases tree with
    | jp root bodyTree continuationTree =>
        rcases body bodyTree with ⟨bodyTrace⟩
        rcases continuation continuationTree with ⟨continuationTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.jp
            (fun _ => bodyTrace.trace.traced)
            (fun _ => continuationTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.jp (.mk fvarId binderName params type rightBody)
              rightContinuation) := by
          cases root.side with
          | jp leftFresh rightFresh bodyShape continuationShape =>
            have bodySide : ScopedCodeSideReflexive
                (index.pushParamList params.toList) rightBody := by
              simpa [ScopeIndex.pushParams, LCNF.FunDecl.params,
                LCNF.FunDecl.value] using bodyTrace.targetSide
            have replacedBody := paramBodySideConditions_replaceCode
              (index := index) bodyShape bodySide
            exact .jp leftFresh rightFresh
              (by simpa [LCNF.FunDecl.params, LCNF.FunDecl.value] using
                replacedBody)
              (show ScopedCodeSideReflexive
                (index.pushJoin fvarId) rightContinuation from
                  continuationTrace.targetSide)
        exact ⟨{ trace := trace, targetSide := targetSide }⟩
  jmp := by
    intro index fvarId args tree
    exact ⟨{
      trace := .single (.identity tree.root.structural tree.root.alpha)
      targetSide := tree.root.side
    }⟩
  ret := by
    intro index fvarId tree
    exact ⟨{
      trace := .single (.identity tree.root.structural tree.root.alpha)
      targetSide := tree.root.side
    }⟩
  unreach := by
    intro index type tree
    exact ⟨{
      trace := .single (.identity tree.root.structural tree.root.alpha)
      targetSide := tree.root.side
    }⟩
  oset := by
    intro index fvarId fieldIndex value left right child tree
    cases tree with
    | oset root childTree =>
        rcases child childTree with ⟨childTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.oset
            (fun _ => childTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.oset fvarId fieldIndex value right) := by
          cases root.side with
          | oset leftObjectScoped rightObjectScoped leftFieldScoped
              rightFieldScoped continuation =>
            exact .oset leftObjectScoped rightObjectScoped leftFieldScoped
              rightFieldScoped childTrace.targetSide
        exact ⟨{ trace := trace, targetSide := targetSide }⟩
  uset := by
    intro index fvarId fieldIndex value left right child tree
    cases tree with
    | uset root childTree =>
        rcases child childTree with ⟨childTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.uset
            (fun _ => childTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.uset fvarId fieldIndex value right) := by
          cases root.side with
          | uset leftObjectScoped rightObjectScoped leftFieldScoped
              rightFieldScoped continuation =>
            exact .uset leftObjectScoped rightObjectScoped leftFieldScoped
              rightFieldScoped childTrace.targetSide
        exact ⟨{ trace := trace, targetSide := targetSide }⟩
  sset := by
    intro index fvarId width offset value type left right child tree
    cases tree with
    | sset root childTree =>
        rcases child childTree with ⟨childTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.sset
            (fun _ => childTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.sset fvarId width offset value type right) := by
          cases root.side with
          | sset leftObjectScoped rightObjectScoped leftFieldScoped
              rightFieldScoped continuation =>
            exact .sset leftObjectScoped rightObjectScoped leftFieldScoped
              rightFieldScoped childTrace.targetSide
        exact ⟨{ trace := trace, targetSide := targetSide }⟩
  setTag := by
    intro index fvarId tag left right child tree
    cases tree with
    | setTag root childTree =>
        rcases child childTree with ⟨childTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.setTag
            (fun _ => childTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.setTag fvarId tag right) := by
          cases root.side with
          | setTag leftObjectScoped rightObjectScoped continuation =>
            exact .setTag leftObjectScoped rightObjectScoped
              childTrace.targetSide
        exact ⟨{ trace := trace, targetSide := targetSide }⟩
  inc := by
    intro index fvarId amount check persistent left right child tree
    cases tree with
    | inc root childTree =>
        rcases child childTree with ⟨childTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.inc
            (fun _ => childTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.inc fvarId amount check persistent right) := by
          cases root.side with
          | inc leftObjectScoped rightObjectScoped continuation =>
            exact .inc leftObjectScoped rightObjectScoped
              childTrace.targetSide
        exact ⟨{ trace := trace, targetSide := targetSide }⟩
  dec := by
    intro index fvarId amount check persistent objects left right child tree
    cases tree with
    | dec root childTree =>
        rcases child childTree with ⟨childTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.dec
            (fun _ => childTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.dec fvarId amount check persistent objects right) := by
          cases root.side with
          | dec leftObjectScoped rightObjectScoped continuation =>
            exact .dec leftObjectScoped rightObjectScoped
              childTrace.targetSide
        exact ⟨{ trace := trace, targetSide := targetSide }⟩
  del := by
    intro index fvarId left right child tree
    cases tree with
    | del root childTree =>
        rcases child childTree with ⟨childTrace⟩
        rcases (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.del
            (fun _ => childTrace.trace.traced) root.alpha) with ⟨trace⟩
        have targetSide : ScopedCodeSideReflexive index
            (.del fvarId right) := by
          cases root.side with
          | del leftObjectScoped rightObjectScoped continuation =>
            exact .del leftObjectScoped rightObjectScoped
              childTrace.targetSide
        exact ⟨{ trace := trace, targetSide := targetSide }⟩

theorem scopedCodePhaseEndpointCertifiedTree_caseBoundary_iff_kernel :
    ScopedCaseBoundarySound
        (ScopedCodePhaseEndpointCertifiedOnCertificateTree validCase) ↔
      ScopedCaseKernelLaws
        (ScopedCodePhaseEndpointCertifiedOnCertificateTree validCase) :=
  scopedCaseBoundarySound_iff_kernel
    scopedCodePhaseEndpointCertifiedOnCertificateTree_traversalLaws

/-- Universal certified recursive boundary from the exact certified local
phase contract. -/
theorem scopedCaseBoundarySoundEndpointCertifiedTree_of_localPhases
    (phases : ScopedLocalCaseCertifiedPhaseLaws validCase) :
    ScopedCaseBoundarySound
      (ScopedCodePhaseEndpointCertifiedOnCertificateTree validCase) :=
  scopedCaseBoundarySound_of_kernel
    scopedCodePhaseEndpointCertifiedOnCertificateTree_traversalLaws
    (scopedCaseEndpointCertifiedTraceKernelLaws_of_localPhases phases)

/-- End-to-end arbitrary-depth non-lockstep trace with a certified actual
endpoint. Complete source certificates are consumed pointwise, including
case alternatives hidden by duplicate selectors. -/
theorem shadowCode_scopedPhaseEndpointCertifiedTree
    (phases : ScopedLocalCaseCertifiedPhaseLaws validCase)
    (certificates : ScopedCodeTargetCertificateTree validCase index source)
    (run : shadowCode? fuel source = some target) :
    Nonempty (ScopedCodePhaseEndpointCertifiedTrace
      validCase index source target) :=
  (shadowCode_scopedRelated_of_caseKernel
    scopedCodePhaseEndpointCertifiedOnCertificateTree_traversalLaws
    (scopedCaseEndpointCertifiedTraceKernelLaws_of_localPhases phases) run)
      certificates

/-- End-to-end certified traversal from reachable selection, certified
singleton classification, and the retained semantic phase law. The retained
endpoint certificate itself is reconstructed generically. -/
theorem shadowCode_scopedPhaseEndpointCertifiedTree_of_components
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (singletonPhases : ScopedCaseCertifiedSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (certificates : ScopedCodeTargetCertificateTree validCase index source)
    (run : shadowCode? fuel source = some target) :
    Nonempty (ScopedCodePhaseEndpointCertifiedTrace
      validCase index source target) :=
  shadowCode_scopedPhaseEndpointCertifiedTree
    (scopedLocalCaseCertifiedPhaseLaws_of_components selection
      singletonPhases
      (scopedCaseCertifiedRetainedPhaseLaws_of_retained retainedPhases))
    certificates run

theorem scopedCodePhaseTracedTree_caseBoundary_iff_kernel :
    ScopedCaseBoundarySound
        (ScopedCodePhaseTracedOnAlphaTree validCase) ↔
      ScopedCaseKernelLaws
        (ScopedCodePhaseTracedOnAlphaTree validCase) :=
  scopedCaseBoundarySound_iff_kernel
    scopedCodePhaseTracedOnAlphaTree_traversalLaws

/-- Universal trace-producing recursive boundary from the exact local
`shadowSimplifyCases` phase contract. -/
theorem scopedCaseBoundarySoundTraceTree_of_localPhases
    (phases : ScopedLocalCasePhaseLaws validCase) :
    ScopedCaseBoundarySound
      (ScopedCodePhaseTracedOnAlphaTree validCase) :=
  scopedCaseBoundarySound_of_kernel
    scopedCodePhaseTracedOnAlphaTree_traversalLaws
    (scopedCaseTraceKernelLaws_of_localPhases phases)

theorem scopedCaseBoundarySoundTraceTree_of_phaseShapes
    (shapes : ScopedCasePhaseShapeLaws validCase) :
    ScopedCaseBoundarySound
      (ScopedCodePhaseTracedOnAlphaTree validCase) :=
  scopedCaseBoundarySoundTraceTree_of_localPhases
    (scopedLocalCasePhaseLaws_of_shapes shapes)

/-- Universal recursive boundary from the independently dischargeable local
selection, phase, folding, and endpoint-identity contracts. -/
theorem scopedCaseBoundarySoundTraceTree_of_phaseComponents
    (emptySelection : ScopedCaseEmptySelectionLaws validCase)
    (singletonPhases : ScopedCaseSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase) :
    ScopedCaseBoundarySound
      (ScopedCodePhaseTracedOnAlphaTree validCase) :=
  scopedCaseBoundarySoundTraceTree_of_localPhases
    (scopedLocalCasePhaseLaws_of_components emptySelection singletonPhases
      retainedPhases targetIdentities)

/-- End-to-end arbitrary recursive trace under full lexical hygiene. Every
nested case contributes a separate local round. -/
theorem shadowCode_scopedPhaseTracedTree
    (phases : ScopedLocalCasePhaseLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodePhaseTraced validCase index source target :=
  (shadowCode_scopedRelated_of_caseKernel
    scopedCodePhaseTracedOnAlphaTree_traversalLaws
    (scopedCaseTraceKernelLaws_of_localPhases phases) run) hygiene

/-- End-to-end recursive trace from independently proved phase-aware empty,
singleton, and retained output-shape laws. -/
theorem shadowCode_scopedPhaseTracedTree_of_phaseShapes
    (shapes : ScopedCasePhaseShapeLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodePhaseTraced validCase index source target :=
  shadowCode_scopedPhaseTracedTree
    (scopedLocalCasePhaseLaws_of_shapes shapes) hygiene run

/-- End-to-end recursive trace assembled directly from the four local
component contracts, without a bundled phase-shape premise. -/
theorem shadowCode_scopedPhaseTracedTree_of_phaseComponents
    (emptySelection : ScopedCaseEmptySelectionLaws validCase)
    (singletonPhases : ScopedCaseSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodePhaseTraced validCase index source target :=
  shadowCode_scopedPhaseTracedTree
    (scopedLocalCasePhaseLaws_of_components emptySelection singletonPhases
      retainedPhases targetIdentities) hygiene run

/-- End-to-end recursive trace with the empty component discharged from
reachable source selection. Only singleton, retained, and endpoint contracts
remain as explicit local phase obligations. -/
theorem shadowCode_scopedPhaseTracedTree_of_reachableSelection
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (singletonPhases : ScopedCaseSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodePhaseTraced validCase index source target :=
  shadowCode_scopedPhaseTracedTree_of_phaseShapes
    (scopedCasePhaseShapeLaws_of_reachableSelection selection singletonPhases
      retainedPhases targetIdentities) hygiene run

/-- Recursive trace after deriving both empty-table safety and the ordinary
direct-singleton path. Fold-created singleton evidence remains explicit. -/
theorem shadowCode_scopedPhaseTracedTree_of_foldedSingletons
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (foldedSingletons : ScopedCaseFoldedSingletonPhaseLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodePhaseTraced validCase index source target :=
  shadowCode_scopedPhaseTracedTree_of_phaseShapes
    (scopedCasePhaseShapeLaws_of_reachableSelectionAndFolded selection
      foldedSingletons retainedPhases targetIdentities) hygiene run

/-- End-to-end recursive trace whose only singleton-fold premise is the
bidirectional selected-branch alpha contract. Filtering and elimination are
now discharged generically. -/
theorem shadowCode_scopedPhaseTracedTree_of_foldedAlpha
    (selection : ScopedCaseReachableSelectionLaws validCase)
    (foldAlpha : ScopedCaseFoldedAlphaLaws validCase)
    (retainedPhases : ScopedCaseRetainedPhaseLaws validCase)
    (targetIdentities : ScopedCasePhaseTargetIdentityLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodePhaseTraced validCase index source target :=
  shadowCode_scopedPhaseTracedTree_of_phaseShapes
    (scopedCasePhaseShapeLaws_of_reachableSelectionAndFoldedAlpha selection
      foldAlpha retainedPhases targetIdentities) hygiene run

/-- Recursive correctness for the trace relation reduces exactly to a local
case-kernel law, just as it does for the one-round result relation. -/
theorem scopedCodePhaseTraced_caseBoundary_iff_kernel :
    ScopedCaseBoundarySound
        (ScopedCodePhaseTracedOnAlphaReflexive validCase) ↔
      ScopedCaseKernelLaws
        (ScopedCodePhaseTracedOnAlphaReflexive validCase) :=
  scopedCaseBoundarySound_iff_kernel
    scopedCodePhaseTracedOnAlphaReflexive_traversalLaws

/-- End-to-end recursive traversal from a trace-producing local case kernel.
Unlike the fixed phase factor theorem, the conclusion retains every nested
round in execution order. -/
theorem shadowCode_scopedPhaseTraced_of_caseKernel
    (caseKernel : ScopedCaseKernelLaws
      (ScopedCodePhaseTracedOnAlphaReflexive validCase))
    (reflexive : ScopedAlphaBireflexive index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodePhaseTraced validCase index source target :=
  (shadowCode_scopedRelated_of_caseKernel
    scopedCodePhaseTracedOnAlphaReflexive_traversalLaws caseKernel run)
      reflexive

/-- The phase-aware recursive boundary has the same local-kernel reduction as
the older two-phase relation. The stronger kernel result additionally records
target structural and alpha identities for schedule alignment. -/
theorem scopedCodePhaseResult_caseBoundary_iff_kernel :
    ScopedCaseBoundarySound
        (ScopedCodePhaseResultOnAlphaReflexive validCase) ↔
      ScopedCaseKernelLaws
        (ScopedCodePhaseResultOnAlphaReflexive validCase) :=
  scopedCaseBoundarySound_iff_kernel
    scopedCodePhaseResultOnAlphaReflexive_traversalLaws

/-- End-to-end recursive traversal from a phase-aware local case kernel.
The result exposes the honest two/three-phase classification while retaining
the target identities only as internal traversal evidence. -/
theorem shadowCode_scopedPhaseFactored_of_caseKernel
    (caseKernel : ScopedCaseKernelLaws
      (ScopedCodePhaseResultOnAlphaReflexive validCase))
    (reflexive : ScopedAlphaBireflexive index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodePhaseFactored validCase index source target := by
  rcases (shadowCode_scopedRelated_of_caseKernel
    scopedCodePhaseResultOnAlphaReflexive_traversalLaws caseKernel run)
      reflexive with ⟨result⟩
  exact result.phaseFactored

/-- Universal recursive boundary derived from the explicit local
selection/admissibility contract. -/
theorem scopedCaseBoundarySoundTree_of_admissibility
    (admissible : ScopedCaseAdmissibilityLaws validCase) :
    ScopedCaseBoundarySound (ScopedCodeFactoredOnAlphaTree validCase) :=
  scopedCaseBoundarySound_of_kernel
    scopedCodeFactoredOnAlphaTree_traversalLaws
    (scopedCaseKernelLaws_of_admissibility admissible)

/-- Universal recursive boundary from the compiler-shaped phase interface. -/
theorem scopedCaseBoundarySoundTree_of_shapes
    (shapes : ScopedCaseShapeLaws validCase) :
    ScopedCaseBoundarySound (ScopedCodeFactoredOnAlphaTree validCase) :=
  scopedCaseBoundarySoundTree_of_admissibility
    (scopedCaseAdmissibilityLaws_of_shapes shapes)

/-- Universal boundary for the two-phase subset. It intentionally does not
consume the final structural leg of a fold-created singleton. -/
theorem scopedCaseBoundarySoundTree_of_selectionSurvival
    (survival : ScopedCaseSelectionSurvivalLaws validCase)
    (retained : ScopedRetainedCaseShapeLaws validCase) :
    ScopedCaseBoundarySound (ScopedCodeFactoredOnAlphaTree validCase) :=
  scopedCaseBoundarySoundTree_of_admissibility
    (scopedCaseAdmissibilityLaws_of_selectionSurvival survival retained)

/-- Arbitrary recursive shadow traversal once the local case kernel consumes
full-tree scope/hygiene evidence. -/
theorem shadowCode_scopedFactoredTree_of_caseKernel
    (caseKernel : ScopedCaseKernelLaws
      (ScopedCodeFactoredOnAlphaTree validCase))
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodeFactored validCase index source target :=
  (shadowCode_scopedRelated_of_caseKernel
    scopedCodeFactoredOnAlphaTree_traversalLaws caseKernel run) hygiene

/-- End-to-end arbitrary recursive shadow result under complete lexical
hygiene and the phase-specific local case admissibility laws. -/
theorem shadowCode_scopedFactoredTree
    (admissible : ScopedCaseAdmissibilityLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodeFactored validCase index source target :=
  shadowCode_scopedFactoredTree_of_caseKernel
    (scopedCaseKernelLaws_of_admissibility admissible) hygiene run

/-- End-to-end recursive shadow result from independently proved empty,
singleton, and retained case-shape laws. -/
theorem shadowCode_scopedFactoredTree_of_shapes
    (shapes : ScopedCaseShapeLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodeFactored validCase index source target :=
  shadowCode_scopedFactoredTree
    (scopedCaseAdmissibilityLaws_of_shapes shapes) hygiene run

/-- End-to-end recursive result for empty, direct-singleton, and retained
two-phase cases. Fold-created singletons await the phase-factor traversal
lift. -/
theorem shadowCode_scopedFactoredTree_of_selectionSurvival
    (survival : ScopedCaseSelectionSurvivalLaws validCase)
    (retained : ScopedRetainedCaseShapeLaws validCase)
    (hygiene : ScopedAlphaBireflexiveTree index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodeFactored validCase index source target :=
  shadowCode_scopedFactoredTree
    (scopedCaseAdmissibilityLaws_of_selectionSurvival survival retained)
    hygiene run

/-- The remaining proof input is now strictly local to
`shadowSimplifyCases`: recursive alternative bodies and every surrounding
constructor are discharged by the generic traversal theorem. -/
theorem shadowCode_scopedFactored_of_caseKernel
    (caseKernel : ScopedCaseKernelLaws
      (ScopedCodeFactoredOnAlphaReflexive validCase))
    (reflexive : ScopedAlphaBireflexive index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodeFactored validCase index source target :=
  (shadowCode_scopedRelated_of_caseKernel
    scopedCodeFactoredOnAlphaReflexive_traversalLaws caseKernel run) reflexive

/-- For the structural/alpha factor relation, the universal recursive
boundary is exactly the nonrecursive simplifier law—provided explicitly
because neither hygiene nor an unconstrained `validCase` can imply it. -/
theorem scopedCodeFactored_caseBoundary_iff_kernel :
    ScopedCaseBoundarySound
        (ScopedCodeFactoredOnAlphaReflexive validCase) ↔
      ScopedCaseKernelLaws
        (ScopedCodeFactoredOnAlphaReflexive validCase) :=
  scopedCaseBoundarySound_iff_kernel
    scopedCodeFactoredOnAlphaReflexive_traversalLaws

/-- End-to-end recursive traversal theorem for structural/alpha factors. The
universal case premise remains explicit; lexical alpha reflexivity is consumed
only at the concrete source position. -/
theorem shadowCode_scopedFactored
    (caseSound : ScopedCaseBoundarySound
      (ScopedCodeFactoredOnAlphaReflexive validCase))
    (reflexive : ScopedAlphaBireflexive index source)
    (run : shadowCode? fuel source = some target) :
    ScopedCodeFactored validCase index source target :=
  (shadowCode_scopedRelated
    scopedCodeFactoredOnAlphaReflexive_traversalLaws caseSound run) reflexive

end Fir.LeanIR.Passes.SimpCaseScopedBridge
