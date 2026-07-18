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
def ScopeIndex.pushParams (index : ScopeIndex)
    (params : Array (LCNF.Param .impure)) : ScopeIndex :=
  params.foldl (fun current param => current.pushVar param.fvarId) index

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

end Fir.LeanIR.Passes.SimpCaseScopedBridge
