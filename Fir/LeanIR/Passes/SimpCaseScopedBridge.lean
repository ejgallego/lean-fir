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

/-- A universally well-scoped presentation of the factor relation. Ill-scoped
indices are not asserted to relate anything; callers provide alpha reflexivity
at the source position they actually traverse. -/
def ScopedCodeFactoredOnAlphaReflexive
    (validCase : LCNF.Cases .impure → Nat → Prop) : ScopedCodeRelation :=
  fun index source target =>
    ScopedAlphaBireflexive index source →
      ScopedCodeFactored validCase index source target

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
