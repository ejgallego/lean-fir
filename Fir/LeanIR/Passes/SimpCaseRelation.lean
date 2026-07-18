import Fir.LeanIR.Passes.Structural

namespace Fir.LeanIR.Passes.SimpCaseRelation

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.NonLockstep
open Fir.LeanIR.Passes.NonLockstep.Structural

/-!
`CodeRel` is a proof-facing graph for recursive `simpCase` traversals.  It is
deliberately independent of Lean's private `Code.simpCase` implementation:
compiler conformance is a separate boundary.

The graph distinguishes head-aligned code from an eliminated case prefix.
Head-aligned nodes take the same kind of interpreter step; an eliminated case
may take one source step while the target stutters.  Recursive occurrences in
continuations, join bodies, and selected case branches use `CodeRel` again.
-/

mutual

  /-- Recursive relation between source code and its `simpCase` target. -/
  inductive CodeRel
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      LCNF.Code .impure → LCNF.Code .impure → Prop where
    | aligned (related : HeadRel validCase left right) :
        CodeRel validCase left right
    | eliminate
        (cases : LCNF.Cases .impure)
        (target : LCNF.Code .impure)
        (selected : ∀ tag, validCase cases tag →
          ElimSelectionRel validCase target
            (chooseAlt tag cases.alts.toList)) :
        CodeRel validCase (.cases cases) target

  /-- Code whose outer interpreter action is aligned on both sides. -/
  inductive HeadRel
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      LCNF.Code .impure → LCNF.Code .impure → Prop where
    | let (decl : LCNF.LetDecl .impure)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.let decl left) (.let decl right)
    | jp (fvarId : FVarId) (binderName : Name)
        (params : Array (LCNF.Param .impure)) (type : Expr)
        (body : CodeRel validCase leftBody rightBody)
        (continuation : CodeRel validCase leftContinuation rightContinuation) :
        HeadRel validCase
          (.jp (.mk fvarId binderName params type leftBody) leftContinuation)
          (.jp (.mk fvarId binderName params type rightBody) rightContinuation)
    | jmp (fvarId : FVarId) (args : Array (LCNF.Arg .impure)) :
        HeadRel validCase (.jmp fvarId args) (.jmp fvarId args)
    | cases (typeName : Name) (resultType : Expr) (discr : FVarId)
        (leftAlts rightAlts : Array (LCNF.Alt .impure))
        (selected : ∀ tag,
          validCase (.mk typeName resultType discr leftAlts) tag →
          SelectionRel validCase (chooseAlt tag leftAlts.toList)
            (chooseAlt tag rightAlts.toList)) :
        HeadRel validCase
          (.cases (.mk typeName resultType discr leftAlts))
          (.cases (.mk typeName resultType discr rightAlts))
    | return (fvarId : FVarId) :
        HeadRel validCase (.return fvarId) (.return fvarId)
    | unreach (type : Expr) :
        HeadRel validCase (.unreach type) (.unreach type)
    | oset (fvarId : FVarId) (index : Nat) (value : LCNF.Arg .impure)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.oset fvarId index value left)
          (.oset fvarId index value right)
    | uset (fvarId : FVarId) (index : Nat) (value : FVarId)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.uset fvarId index value left)
          (.uset fvarId index value right)
    | sset (fvarId : FVarId) (width offset : Nat) (value : FVarId)
        (type : Expr) (continuation : CodeRel validCase left right) :
        HeadRel validCase (.sset fvarId width offset value type left)
          (.sset fvarId width offset value type right)
    | setTag (fvarId : FVarId) (tag : Nat)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.setTag fvarId tag left) (.setTag fvarId tag right)
    | inc (fvarId : FVarId) (amount : Nat) (check persistent : Bool)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.inc fvarId amount check persistent left)
          (.inc fvarId amount check persistent right)
    | dec (fvarId : FVarId) (amount : Nat) (check persistent : Bool)
        (objects : Option Nat) (continuation : CodeRel validCase left right) :
        HeadRel validCase (.dec fvarId amount check persistent objects left)
          (.dec fvarId amount check persistent objects right)
    | del (fvarId : FVarId) (continuation : CodeRel validCase left right) :
        HeadRel validCase (.del fvarId left) (.del fvarId right)

  /-- Selected alternatives are either both absent or recursively related. -/
  inductive SelectionRel
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      Option (LCNF.Code .impure) → Option (LCNF.Code .impure) → Prop where
    | none : SelectionRel validCase none none
    | some (related : CodeRel validCase left right) :
        SelectionRel validCase (some left) (some right)

  /-- An eliminated case must select a recursively related source branch for
  every tag permitted by its phase invariant. -/
  inductive ElimSelectionRel
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      LCNF.Code .impure → Option (LCNF.Code .impure) → Prop where
    | some (related : CodeRel validCase source target) :
        ElimSelectionRel validCase target (some source)

end

/-- Lift an aligned head into the full recursive relation. -/
theorem HeadRel.codeRel (related : HeadRel validCase left right) :
    CodeRel validCase left right :=
  .aligned related

/-- Runtime obligation for the currently active related code.  Aligned cases
may fault in lockstep before reading a tag; if a tag is read, it must be in the
relation's permitted set.  An eliminated case must be able to take its source
administrative step. -/
def CodeReadyAt
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (state : MachineState) (left right : LCNF.Code .impure) : Prop :=
  match left, right with
  | .cases cases, .cases _ =>
      ∀ value tag,
        lookupValue state.env cases.discr = .ok value →
        getTag state.runtime value = .ok tag →
        validCase cases tag
  | .cases cases, _ =>
      ∃ value tag,
        lookupValue state.env cases.discr = .ok value ∧
        getTag state.runtime value = .ok tag ∧
        validCase cases tag
  | _, _ => True

/-- Readiness for the active control pair in a structural machine relation. -/
def ControlReadyAt
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (state : MachineState) (left right : Control) : Prop :=
  match left, right with
  | .code left, .code right => CodeReadyAt validCase state left right
  | _, _ => True

/-- A semantic invariant used with `MachineRelatedWith` must establish active
case readiness and remain true along matched finite paths.  The path-stability
field is a typing-preservation obligation, not a simulation assumption: the
structural proof still has to construct both matching paths. -/
structure InvariantLaws (externals : ExternalSpec)
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (invariant : MachineState → MachineState → Prop) : Prop where
  ready : ∀ {left right}
    (_ : MachineRelated (CodeRel validCase) left right),
    invariant left right →
    ControlReadyAt validCase left left.control right.control
  stable : ∀ {leftBefore rightBefore leftAfter rightAfter},
    invariant leftBefore rightBefore →
    MachineRelated (CodeRel validCase) leftBefore rightBefore →
    Reaches externals leftBefore leftAfter →
    Reaches externals rightBefore rightAfter →
    MachineRelated (CodeRel validCase) leftAfter rightAfter →
    invariant leftAfter rightAfter

/-- The direct readiness predicate can be used as one component of a stronger
typed-machine invariant.  Its preservation is intentionally not automatic:
the phase proof must show that future case discriminants remain valid. -/
def AllCasesReady
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (left right : MachineState) : Prop :=
  ControlReadyAt validCase left left.control right.control

end Fir.LeanIR.Passes.SimpCaseRelation
