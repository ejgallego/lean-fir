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

/-- Universal recursive boundary derived from the explicit local
selection/admissibility contract. -/
theorem scopedCaseBoundarySoundTree_of_admissibility
    (admissible : ScopedCaseAdmissibilityLaws validCase) :
    ScopedCaseBoundarySound (ScopedCodeFactoredOnAlphaTree validCase) :=
  scopedCaseBoundarySound_of_kernel
    scopedCodeFactoredOnAlphaTree_traversalLaws
    (scopedCaseKernelLaws_of_admissibility admissible)

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
