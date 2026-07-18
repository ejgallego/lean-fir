import Fir.LeanIR.Passes.SimpCaseAlphaBridge

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
  sourceScope : List FVarId
  targetScope : List FVarId
  sourceJoins : List FVarId
  targetJoins : List FVarId

/-- Empty declaration-body index. -/
def ScopeIndex.empty : ScopeIndex where
  forwardRho := {}
  backwardRho := {}
  sourceScope := []
  targetScope := []
  sourceJoins := []
  targetJoins := []

/-- Descend through an unchanged ordinary binder. -/
def ScopeIndex.pushVar (index : ScopeIndex) (fvarId : FVarId) : ScopeIndex := {
  index with
  forwardRho := index.forwardRho.insert fvarId fvarId
  backwardRho := index.backwardRho.insert fvarId fvarId
  sourceScope := fvarId :: index.sourceScope
  targetScope := fvarId :: index.targetScope
}

/-- Descend through an unchanged join binder. -/
def ScopeIndex.pushJoin (index : ScopeIndex) (fvarId : FVarId) : ScopeIndex := {
  index with
  forwardRho := index.forwardRho.insert fvarId fvarId
  backwardRho := index.backwardRho.insert fvarId fvarId
  sourceJoins := fvarId :: index.sourceJoins
  targetJoins := fvarId :: index.targetJoins
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
  sourceScope := index.targetScope
  targetScope := index.sourceScope
  sourceJoins := index.targetJoins
  targetJoins := index.sourceJoins

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

/-- A nonempty sequence of synchronized alternative rounds. -/
inductive ScopedAltsPhaseTrace
    (validCase : LCNF.Cases .impure → Nat → Prop) (index : ScopeIndex) :
    List (LCNF.Alt .impure) → List (LCNF.Alt .impure) → Type where
  | single (round : ScopedAltsPhaseResult validCase index source target) :
      ScopedAltsPhaseTrace validCase index source target
  | trans (round : ScopedAltsPhaseResult validCase index source middle)
      (rest : ScopedAltsPhaseTrace validCase index middle target) :
      ScopedAltsPhaseTrace validCase index source target

def ScopedAltsPhaseTrace.rounds
    (trace : ScopedAltsPhaseTrace validCase index source target) : Nat :=
  match trace with
  | .single _ => 1
  | .trans _ rest => 1 + rest.rounds

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

/-- Full-tree trace presentation used by the recursive case kernel. The tree
supplies hygiene for every alternative, including syntactically shadowed
entries that root alpha selection cannot expose. -/
def ScopedCodePhaseTracedOnAlphaTree
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedAlphaBireflexiveTree index source →
      ScopedCodePhaseTraced validCase index source target

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

theorem ScopedAlignedCaseEvidence.factored
    (evidence : ScopedAlignedCaseEvidence validCase index source target) :
    ScopedCodeFactored validCase index (.cases source) (.cases target) := by
  cases source with
  | mk typeName resultType discr sourceAlts =>
      exact ⟨{
        middle := .cases
          (.mk typeName resultType discr evidence.middleAlts)
        structural := .aligned (.cases typeName resultType discr
          sourceAlts evidence.middleAlts evidence.structuralSelected)
        alphaForward := .cases evidence.alphaForwardDiscr
          evidence.alphaForwardSelected
        alphaBackward := .cases evidence.alphaBackwardDiscr
          evidence.alphaBackwardSelected
      }⟩

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

theorem ScopedEliminatedCaseEvidence.factored
    (evidence : ScopedEliminatedCaseEvidence
      validCase index source target) :
    ScopedCodeFactored validCase index (.cases source) target :=
  ⟨{
    middle := evidence.middle
    structural := .eliminate source evidence.middle
      evidence.structuralSelected
    alphaForward := evidence.alphaForward
    alphaBackward := evidence.alphaBackward
  }⟩

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

/-- Exact nonrecursive phase contract for `shadowSimplifyCases`. Recursive
alternative traversal is intentionally absent: the input table is already
the transformed table, and this law contributes exactly the parent round. -/
structure ScopedLocalCasePhaseLaws
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop where
  simplify : ∀ {index : ScopeIndex} {typeName : Name} {resultType : Expr}
      {discr : FVarId} {alts : Array (LCNF.Alt .impure)},
    ScopedAlphaBireflexive index
      (.cases (.mk typeName resultType discr alts)) →
    Nonempty (ScopedCodePhaseResult validCase index
      (.cases (.mk typeName resultType discr alts))
      (shadowSimplifyCases (.mk typeName resultType discr alts)))

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
        rcases phases.simplify recursiveTrace.targetAlpha with ⟨parentRound⟩
        exact (recursiveTrace.append parentRound.trace).traced

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
      exact .nil (by simpa [ScopeIndex.pushParamList] using body)
  | cons param rest ih =>
      cases shape with
      | cons leftFresh rightFresh leftJoinFresh rightJoinFresh tail =>
          exact .cons leftFresh rightFresh leftJoinFresh rightJoinFresh
            (ih (index := index.pushVar param.fvarId) tail
              (by simpa [ScopeIndex.pushParamList] using body))

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
