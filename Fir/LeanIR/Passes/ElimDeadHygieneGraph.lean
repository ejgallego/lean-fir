import Fir.LeanIR.Passes.ElimDeadHygiene
import Fir.LeanIR.Passes.ElimDeadProgram

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.ImpureHygiene
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.SimpCaseScopedBridge
open Fir.LeanIR.Passes.SimpCaseWellFormed

/-!
Proof-relevant exact graphs for the transparent `elimDeadVars` traversal.

The operational `ShadowCodeGraph` is intentionally `Prop`-valued and permits
monotone liveness widening.  It is therefore the right relation for runtime
environment agreement, but the wrong place to recover which computational
branch made a deletion decision.  This module retains the exact traversal
seed and replays its branch decisions as transparent data before forgetting
them into the monotone graph.
-/

/-- Exact successful traversal witness.  Unlike `ShadowCodeGraph`, the final
liveness set is not widened and the seed remains proof-relevant data. -/
structure ExactShadowCodeGraph (fuel : Nat) (final : UsedLocals)
    (source target : LCNF.Code .impure) where
  initial : UsedLocals
  result : shadowCode? fuel initial source = some (target, final)

def ExactShadowCodeGraph.ofResult
    {initial : UsedLocals}
    (result : shadowCode? fuel initial source = some (target, final)) :
    ExactShadowCodeGraph fuel final source target :=
  ⟨initial, result⟩

/-- Forget exact branch provenance into the monotone operational graph. -/
theorem ExactShadowCodeGraph.toShadowCodeGraph
    (exact : ExactShadowCodeGraph fuel final source target) :
    ShadowCodeGraph fuel final source target :=
  ⟨fuel, exact.initial, final, Nat.le_refl fuel, exact.result, .refl final⟩

/-- Exact code result with its seed exposed as an index.  Child edges in the
proof-relevant view use this form so their seed is definitionally the
threaded liveness output of the preceding child. -/
structure ExactShadowCodeRun (fuel : Nat) (initial final : UsedLocals)
    (source target : LCNF.Code .impure) : Type where
  result : shadowCode? fuel initial source = some (target, final)

/-- Exact alternative-list counterpart of `ExactShadowCodeRun`. -/
structure ExactShadowAltListRun (fuel : Nat)
    (initial final : UsedLocals)
    (source target : List (LCNF.Alt .impure)) : Type where
  result :
    shadowAltList? (shadowCode? fuel) initial source = some (target, final)

/-- Repackage an indexed child run as an exact graph, retaining its seed as
data for another proof-relevant view step. -/
def ExactShadowCodeRun.toGraph
    (run : ExactShadowCodeRun fuel initial final source target) :
    ExactShadowCodeGraph fuel final source target :=
  ⟨initial, run.result⟩

/-- One transparent alternative-list layer.  The head body starts at the
list's seed, and the exact tail starts at the head body's final liveness set,
matching the compiler's left-to-right threading order. -/
inductive ExactShadowAltListView (fuel : Nat) (initial : UsedLocals) :
    UsedLocals →
      List (LCNF.Alt .impure) → List (LCNF.Alt .impure) → Type where
  | nil :
      ExactShadowAltListView fuel initial initial [] []
  | ctor
      (body :
        ExactShadowCodeRun fuel initial middle sourceBody targetBody)
      (rest :
        ExactShadowAltListRun fuel middle final sourceRest targetRest) :
      ExactShadowAltListView fuel initial final
        (.ctorAlt info sourceBody :: sourceRest)
        (.ctorAlt info targetBody :: targetRest)
  | default
      (body :
        ExactShadowCodeRun fuel initial middle sourceBody targetBody)
      (rest :
        ExactShadowAltListRun fuel middle final sourceRest targetRest) :
      ExactShadowAltListView fuel initial final
        (.default sourceBody :: sourceRest)
        (.default targetBody :: targetRest)

/-- Compute the proof-relevant head/tail decomposition of an exact
alternative-list run. -/
def ExactShadowAltListRun.view
    (run : ExactShadowAltListRun fuel initial final source target) :
    ExactShadowAltListView fuel initial final source target := by
  rcases run with ⟨exactResult⟩
  cases source with
  | nil =>
      simp [shadowAltList?] at exactResult
      rcases exactResult with ⟨rfl, rfl⟩
      exact .nil
  | cons alternative sourceRest =>
      cases bodyResult :
          shadowCode? fuel initial alternative.getCode with
      | none =>
          simp [shadowAltList?, bodyResult] at exactResult
      | some bodyOutput =>
          obtain ⟨targetBody, middle⟩ := bodyOutput
          cases restResult :
              shadowAltList? (shadowCode? fuel) middle sourceRest with
          | none =>
              simp [shadowAltList?, bodyResult, restResult] at exactResult
          | some restOutput =>
              obtain ⟨targetRest, threadedFinal⟩ := restOutput
              simp [shadowAltList?, bodyResult, restResult] at exactResult
              rcases exactResult with ⟨rfl, rfl⟩
              cases alternative with
              | ctorAlt info sourceBody =>
                  exact .ctor ⟨bodyResult⟩ ⟨restResult⟩
              | default sourceBody =>
                  exact .default ⟨bodyResult⟩ ⟨restResult⟩
              | alt _ _ _ impossible => nomatch impossible

/-- One transparent, proof-relevant view of every successful `shadowCode?`
branch.  Its constructors retain exact child runs and threaded liveness data,
so later hereditary proofs can recurse without recovering computational
branch provenance from a `Prop`-valued residual. -/
inductive ExactShadowCodeView (initial : UsedLocals) :
    Nat → UsedLocals → LCNF.Code .impure → LCNF.Code .impure → Type where
  | letRetained
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (keep :
        declaration.fvarId ∈ continuationUsed ∨
          safeToElim declaration.value = false) :
      ExactShadowCodeView initial (nextFuel + 1)
        (collectLetValue continuationUsed declaration.value)
        (.let declaration sourceContinuation)
        (.let declaration targetContinuation)
  | letDeleted
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (absent :
        continuationUsed.contains declaration.fvarId = false)
      (safe : safeToElim declaration.value = true) :
      ExactShadowCodeView initial (nextFuel + 1) continuationUsed
        (.let declaration sourceContinuation) targetContinuation
  | joinRetained
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (live : continuationUsed.contains fvarId = true)
      (body :
        ExactShadowCodeRun nextFuel continuationUsed bodyUsed
          sourceBody targetBody) :
      ExactShadowCodeView initial (nextFuel + 1) bodyUsed
        (.jp (.mk fvarId binderName params type sourceBody)
          sourceContinuation)
        (.jp (.mk fvarId binderName params type targetBody)
          targetContinuation)
  | joinDeleted
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (absent : continuationUsed.contains fvarId = false) :
      ExactShadowCodeView initial (nextFuel + 1) continuationUsed
        (.jp (.mk fvarId binderName params type sourceBody)
          sourceContinuation)
        targetContinuation
  | cases
      (alternatives :
        ExactShadowAltListRun nextFuel initial beforeDiscr
          sourceAlternatives.toList targetAlternatives) :
      ExactShadowCodeView initial (nextFuel + 1)
        (beforeDiscr.insert discr)
        (.cases (.mk typeName resultType discr sourceAlternatives))
        (.cases (.mk typeName resultType discr targetAlternatives.toArray))
  | jump :
      ExactShadowCodeView initial fuel
        (collectArgs (initial.insert join) arguments)
        (.jmp join arguments) (.jmp join arguments)
  | return :
      ExactShadowCodeView initial fuel (initial.insert result)
        (.return result) (.return result)
  | unreachable :
      ExactShadowCodeView initial fuel initial
        (.unreach type) (.unreach type)
  | objectSetRetained
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (live : continuationUsed.contains object = true) :
      ExactShadowCodeView initial (nextFuel + 1)
        (collectArg continuationUsed field)
        (.oset object index field sourceContinuation)
        (.oset object index field targetContinuation)
  | objectSetDeleted
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (absent : continuationUsed.contains object = false) :
      ExactShadowCodeView initial (nextFuel + 1) continuationUsed
        (.oset object index field sourceContinuation) targetContinuation
  | usizeSetRetained
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (live : continuationUsed.contains object = true) :
      ExactShadowCodeView initial (nextFuel + 1)
        (continuationUsed.insert field)
        (.uset object index field sourceContinuation)
        (.uset object index field targetContinuation)
  | usizeSetDeleted
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (absent : continuationUsed.contains object = false) :
      ExactShadowCodeView initial (nextFuel + 1) continuationUsed
        (.uset object index field sourceContinuation) targetContinuation
  | scalarSetRetained
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (live : continuationUsed.contains object = true) :
      ExactShadowCodeView initial (nextFuel + 1)
        (continuationUsed.insert field)
        (.sset object width offset field type sourceContinuation)
        (.sset object width offset field type targetContinuation)
  | scalarSetDeleted
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation)
      (absent : continuationUsed.contains object = false) :
      ExactShadowCodeView initial (nextFuel + 1) continuationUsed
        (.sset object width offset field type sourceContinuation)
        targetContinuation
  | tagSet
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation) :
      ExactShadowCodeView initial (nextFuel + 1)
        (continuationUsed.insert object)
        (.setTag object tag sourceContinuation)
        (.setTag object tag targetContinuation)
  | increment
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation) :
      ExactShadowCodeView initial (nextFuel + 1)
        (continuationUsed.insert object)
        (.inc object amount check persistent sourceContinuation)
        (.inc object amount check persistent targetContinuation)
  | decrement
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation) :
      ExactShadowCodeView initial (nextFuel + 1)
        (continuationUsed.insert object)
        (.dec object amount check persistent objects sourceContinuation)
        (.dec object amount check persistent objects targetContinuation)
  | delete
      (continuation :
        ExactShadowCodeRun nextFuel initial continuationUsed
          sourceContinuation targetContinuation) :
      ExactShadowCodeView initial (nextFuel + 1)
        (continuationUsed.insert object)
        (.del object sourceContinuation)
        (.del object targetContinuation)

/-- Compute the unique one-layer proof-relevant view of an exact successful
run.  This definition is intentionally a transparent replay of
`shadowCode?`, including every retained/deleted decision. -/
def ExactShadowCodeGraph.view
    (exact : ExactShadowCodeGraph fuel final source target) :
    ExactShadowCodeView exact.initial fuel final source target := by
  rcases exact with ⟨initial, exactResult⟩
  cases fuel with
  | zero =>
      cases source with
      | «let» declaration continuation =>
          simp [shadowCode?] at exactResult
      | jp declaration continuation =>
          simp [shadowCode?] at exactResult
      | cases caseInfo =>
          simp [shadowCode?] at exactResult
      | jmp join arguments =>
          have result := exactResult
          simp [shadowCode?] at result
          rcases result with ⟨rfl, rfl⟩
          exact .jump
      | «return» result =>
          have transformed := exactResult
          simp [shadowCode?] at transformed
          rcases transformed with ⟨rfl, rfl⟩
          exact .return
      | unreach type =>
          have result := exactResult
          simp [shadowCode?] at result
          rcases result with ⟨rfl, rfl⟩
          exact .unreachable
      | oset object index field continuation =>
          simp [shadowCode?] at exactResult
      | uset object index field continuation =>
          simp [shadowCode?] at exactResult
      | sset object width offset field type continuation =>
          simp [shadowCode?] at exactResult
      | setTag object tag continuation =>
          simp [shadowCode?] at exactResult
      | inc object amount check persistent continuation =>
          simp [shadowCode?] at exactResult
      | dec object amount check persistent objects continuation =>
          simp [shadowCode?] at exactResult
      | del object continuation =>
          simp [shadowCode?] at exactResult
      | «fun» _ _ impossible => nomatch impossible
  | succ nextFuel =>
      cases source with
      | «let» declaration sourceContinuation =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none =>
              simp [shadowCode?, continuationResult] at exactResult
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              by_cases keep :
                  declaration.fvarId ∈ continuationUsed ∨
                    safeToElim declaration.value = false
              · have result := exactResult
                simp [shadowCode?, continuationResult, keep] at result
                rcases result with ⟨rfl, rfl⟩
                exact .letRetained ⟨continuationResult⟩ keep
              · have result := exactResult
                simp [shadowCode?, continuationResult, keep] at result
                rcases result with ⟨rfl, rfl⟩
                have absent :
                    continuationUsed.contains declaration.fvarId = false := by
                  cases memberEq :
                      continuationUsed.contains declaration.fvarId <;>
                    simp_all
                have safe : safeToElim declaration.value = true := by
                  cases safeEq : safeToElim declaration.value <;>
                    simp_all
                exact .letDeleted ⟨continuationResult⟩ absent safe
      | jp declaration sourceContinuation =>
          cases declaration with
          | mk fvarId binderName params type sourceBody =>
              cases continuationResult :
                  shadowCode? nextFuel initial sourceContinuation with
              | none =>
                  simp [shadowCode?, continuationResult] at exactResult
              | some output =>
                  obtain ⟨targetContinuation, continuationUsed⟩ := output
                  by_cases live : fvarId ∈ continuationUsed
                  · cases bodyResult :
                        shadowCode? nextFuel continuationUsed sourceBody with
                    | none =>
                        simp [shadowCode?, continuationResult, live,
                          bodyResult] at exactResult
                    | some bodyOutput =>
                        obtain ⟨targetBody, bodyUsed⟩ := bodyOutput
                        have result := exactResult
                        simp [shadowCode?, continuationResult, live,
                          bodyResult] at result
                        rcases result with ⟨rfl, rfl⟩
                        have liveEq :
                            continuationUsed.contains fvarId = true := by
                          simpa using live
                        exact .joinRetained ⟨continuationResult⟩ liveEq
                          ⟨bodyResult⟩
                  · have result := exactResult
                    simp [shadowCode?, continuationResult, live] at result
                    rcases result with ⟨rfl, rfl⟩
                    have absent :
                        continuationUsed.contains fvarId = false := by
                      cases memberEq :
                          continuationUsed.contains fvarId <;>
                        simp_all
                    exact .joinDeleted ⟨continuationResult⟩ absent
      | cases caseInfo =>
          cases caseInfo with
          | mk typeName resultType discr sourceAlternatives =>
              cases alternativesResult :
                  shadowAltList? (shadowCode? nextFuel) initial
                    sourceAlternatives.toList with
              | none =>
                  simp [shadowCode?, alternativesResult] at exactResult
              | some output =>
                  obtain ⟨targetAlternatives, beforeDiscr⟩ := output
                  have result := exactResult
                  simp [shadowCode?, alternativesResult] at result
                  rcases result with ⟨rfl, rfl⟩
                  exact .cases ⟨alternativesResult⟩
      | jmp join arguments =>
          have result := exactResult
          simp [shadowCode?] at result
          rcases result with ⟨rfl, rfl⟩
          exact .jump
      | «return» result =>
          have transformed := exactResult
          simp [shadowCode?] at transformed
          rcases transformed with ⟨rfl, rfl⟩
          exact .return
      | unreach type =>
          have result := exactResult
          simp [shadowCode?] at result
          rcases result with ⟨rfl, rfl⟩
          exact .unreachable
      | oset object index field sourceContinuation =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none =>
              simp [shadowCode?, continuationResult] at exactResult
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              by_cases live : object ∈ continuationUsed
              · have result := exactResult
                simp [shadowCode?, continuationResult, live] at result
                rcases result with ⟨rfl, rfl⟩
                have liveEq : continuationUsed.contains object = true := by
                  simpa using live
                exact .objectSetRetained ⟨continuationResult⟩ liveEq
              · have result := exactResult
                simp [shadowCode?, continuationResult, live] at result
                rcases result with ⟨rfl, rfl⟩
                have absent :
                    continuationUsed.contains object = false := by
                  cases memberEq : continuationUsed.contains object <;>
                    simp_all
                exact .objectSetDeleted ⟨continuationResult⟩ absent
      | uset object index field sourceContinuation =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none =>
              simp [shadowCode?, continuationResult] at exactResult
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              by_cases live : object ∈ continuationUsed
              · have result := exactResult
                simp [shadowCode?, continuationResult, live] at result
                rcases result with ⟨rfl, rfl⟩
                have liveEq : continuationUsed.contains object = true := by
                  simpa using live
                exact .usizeSetRetained ⟨continuationResult⟩ liveEq
              · have result := exactResult
                simp [shadowCode?, continuationResult, live] at result
                rcases result with ⟨rfl, rfl⟩
                have absent :
                    continuationUsed.contains object = false := by
                  cases memberEq : continuationUsed.contains object <;>
                    simp_all
                exact .usizeSetDeleted ⟨continuationResult⟩ absent
      | sset object width offset field type sourceContinuation =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none =>
              simp [shadowCode?, continuationResult] at exactResult
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              by_cases live : object ∈ continuationUsed
              · have result := exactResult
                simp [shadowCode?, continuationResult, live] at result
                rcases result with ⟨rfl, rfl⟩
                have liveEq : continuationUsed.contains object = true := by
                  simpa using live
                exact .scalarSetRetained ⟨continuationResult⟩ liveEq
              · have result := exactResult
                simp [shadowCode?, continuationResult, live] at result
                rcases result with ⟨rfl, rfl⟩
                have absent :
                    continuationUsed.contains object = false := by
                  cases memberEq : continuationUsed.contains object <;>
                    simp_all
                exact .scalarSetDeleted ⟨continuationResult⟩ absent
      | setTag object tag sourceContinuation =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none =>
              simp [shadowCode?, continuationResult] at exactResult
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              have result := exactResult
              simp [shadowCode?, continuationResult] at result
              rcases result with ⟨rfl, rfl⟩
              exact .tagSet ⟨continuationResult⟩
      | inc object amount check persistent sourceContinuation =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none =>
              simp [shadowCode?, continuationResult] at exactResult
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              have result := exactResult
              simp [shadowCode?, continuationResult] at result
              rcases result with ⟨rfl, rfl⟩
              exact .increment ⟨continuationResult⟩
      | dec object amount check persistent objects sourceContinuation =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none =>
              simp [shadowCode?, continuationResult] at exactResult
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              have result := exactResult
              simp [shadowCode?, continuationResult] at result
              rcases result with ⟨rfl, rfl⟩
              exact .decrement ⟨continuationResult⟩
      | del object sourceContinuation =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none =>
              simp [shadowCode?, continuationResult] at exactResult
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              have result := exactResult
              simp [shadowCode?, continuationResult] at result
              rcases result with ⟨rfl, rfl⟩
              exact .delete ⟨continuationResult⟩
      | «fun» _ _ impossible => nomatch impossible

/-- Every listed binder that is absent from one liveness set remains absent
from another.  This is the contravariant transport used when backwards
liveness moves from a child result to the result of its containing node. -/
def BinderAbsenceTransfers (binders : List FVarId)
    (sourceUsed targetUsed : UsedLocals) : Prop :=
  ∀ forbidden, forbidden ∈ binders →
    sourceUsed.contains forbidden = false →
      targetUsed.contains forbidden = false

theorem BinderAbsenceTransfers.refl
    (binders : List FVarId) (used : UsedLocals) :
    BinderAbsenceTransfers binders used used :=
  fun _ _ absent => absent

theorem BinderAbsenceTransfers.trans
    (first : BinderAbsenceTransfers binders sourceUsed middle)
    (second : BinderAbsenceTransfers binders middle targetUsed) :
    BinderAbsenceTransfers binders sourceUsed targetUsed :=
  fun forbidden member absent => second forbidden member
    (first forbidden member absent)

theorem BinderAbsenceTransfers.mono
    (transfer : BinderAbsenceTransfers larger sourceUsed targetUsed)
    (subset : ∀ forbidden, forbidden ∈ smaller → forbidden ∈ larger) :
    BinderAbsenceTransfers smaller sourceUsed targetUsed :=
  fun forbidden member => transfer forbidden (subset forbidden member)

mutual

  /-- Hereditary static readiness for a proof-relevant exact traversal.
  Every deleted value or join binder is absent from `ambient`, and the same
  certificate recursively covers every child run selected by the exact
  compiler branch view. -/
  inductive ExactShadowCodeBinderReady (ambient : UsedLocals) :
      {initial : UsedLocals} → {fuel : Nat} → {final : UsedLocals} →
        {source target : LCNF.Code .impure} →
          ExactShadowCodeView initial fuel final source target → Prop where
    | letRetained
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.letRetained continuation keep)
    | letDeleted
        (declaration : LCNF.LetDecl .impure)
        (ambientAbsent :
          ambient.contains declaration.fvarId = false)
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.letDeleted continuation absent safe)
    | joinRetained
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view)
        (bodyReady :
          ExactShadowCodeBinderReady ambient body.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.joinRetained continuation live body)
    | joinDeleted
        (ambientAbsent : ambient.contains fvarId = false)
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.joinDeleted continuation absent)
    | cases
        (alternativesReady :
          ExactShadowAltListBinderReady ambient alternatives.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.cases alternatives)
    | jump :
        ExactShadowCodeBinderReady ambient ExactShadowCodeView.jump
    | return :
        ExactShadowCodeBinderReady ambient ExactShadowCodeView.return
    | unreachable :
        ExactShadowCodeBinderReady ambient ExactShadowCodeView.unreachable
    | objectSetRetained
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.objectSetRetained continuation live)
    | objectSetDeleted
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.objectSetDeleted continuation absent)
    | usizeSetRetained
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.usizeSetRetained continuation live)
    | usizeSetDeleted
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.usizeSetDeleted continuation absent)
    | scalarSetRetained
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.scalarSetRetained continuation live)
    | scalarSetDeleted
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.scalarSetDeleted continuation absent)
    | tagSet
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.tagSet continuation)
    | increment
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.increment continuation)
    | decrement
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.decrement continuation)
    | delete
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.delete continuation)

  /-- Alternative-list counterpart of `ExactShadowCodeBinderReady`. -/
  inductive ExactShadowAltListBinderReady (ambient : UsedLocals) :
      {fuel : Nat} → {initial final : UsedLocals} →
        {source target : List (LCNF.Alt .impure)} →
          ExactShadowAltListView fuel initial final source target → Prop where
    | nil :
        ExactShadowAltListBinderReady ambient ExactShadowAltListView.nil
    | ctor
        (bodyReady :
          ExactShadowCodeBinderReady ambient body.toGraph.view)
        (restReady :
          ExactShadowAltListBinderReady ambient rest.view) :
        ExactShadowAltListBinderReady ambient
          (ExactShadowAltListView.ctor body rest)
    | default
        (bodyReady :
          ExactShadowCodeBinderReady ambient body.toGraph.view)
        (restReady :
          ExactShadowAltListBinderReady ambient rest.view) :
        ExactShadowAltListBinderReady ambient
          (ExactShadowAltListView.default body rest)

end

private theorem paramBindersAvoid_of_binderNamesAvoid
    {params : Array (LCNF.Param .impure)}
    (avoids : BinderNamesAvoid forbidden (paramIds params)) :
    ParamBindersAvoidName forbidden params.toList := by
  intro parameter member
  apply avoids parameter.fvarId
  unfold paramIds
  exact List.mem_map.mpr ⟨parameter, member, rfl⟩

private theorem insert_preserves_absent_of_scoped
    {scope : List FVarId} {forbidden inserted : FVarId}
    {used : UsedLocals}
    (fresh : FreshForScope forbidden scope)
    (inScope : scope.contains inserted = true)
    (absent : used.contains forbidden = false) :
    (used.insert inserted).contains forbidden = false := by
  simpa [collectArg] using
    (collectArg_preserves_absent
      (argument := LCNF.Arg.fvar inserted) absent
      (fvarId_ne_of_freshForScope fresh inScope))

private theorem binderReady_caseAlts_sizeOf_lt
    (cases : LCNF.Cases .impure) :
    sizeOf cases.alts.toList < sizeOf (LCNF.Code.cases cases) := by
  rcases cases with ⟨typeName, resultType, discr, alternatives⟩
  rcases alternatives with ⟨alternatives⟩
  simp [LCNF.Cases.alts]
  omega

private theorem binderReady_altCode_sizeOf_lt_cons
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

set_option maxRecDepth 2048 in
mutual

  /-- Checked scoping, exact structural ownership, and global binder-name
  uniqueness construct hereditary deletion readiness for one exact code
  view.  `transfer` relates the view's exact final liveness set to the
  ambient set at which the certificate will be consumed. -/
  theorem ExactShadowCodeView.binderReady
      (view : ExactShadowCodeView initial fuel final source target)
      (wellFormed : ScopedCodeWellFormedTree index source)
      (listing : CodeBinderList source binders)
      (unique : BinderNamesUnique binders)
      (transfer : BinderAbsenceTransfers binders final ambient) :
      ExactShadowCodeBinderReady ambient view := by
    cases view with
    | @letRetained nextFuel continuationUsed sourceContinuation
        targetContinuation declaration continuation keep =>
        cases listing with
        | @letE _ restBinders _ continuationListing =>
            cases wellFormed with
            | letE valueScoped variableFresh joinFresh runtimeTypes
                continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers restBinders continuationUsed
                      ambient := by
                  intro forbidden member absent
                  apply transfer forbidden (by simp [member])
                  apply collectLetValue_preserves_absent absent
                  apply letValueAvoids_of_scoped
                  · have childFresh :=
                      continuationListing.memberFreshForRoot
                        continuationTree member
                    exact freshForScope_of_subset childFresh.1
                      (scopeSubset_pushVar_sourceScope _ _)
                  · exact valueScoped
                exact .letRetained
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique.tail_unique childTransfer)
    | @letDeleted nextFuel continuationUsed sourceContinuation
        targetContinuation declaration continuation absent safe =>
        cases listing with
        | @letE _ restBinders _ continuationListing =>
            cases wellFormed with
            | letE valueScoped variableFresh joinFresh runtimeTypes
                continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers restBinders final ambient := by
                  intro forbidden member absent
                  exact transfer forbidden
                    (List.mem_cons_of_mem _ member) absent
                exact .letDeleted _
                  (transfer _ (by simp) absent)
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique.tail_unique childTransfer)
    | @joinRetained nextFuel continuationUsed sourceContinuation
        targetContinuation fvarId bodyUsed sourceBody targetBody binderName
        params type continuation live body =>
        cases listing with
        | @join bodyBinders _ restBinders _ bodyListing
            continuationListing =>
            cases wellFormed with
            | @jp _ _ _ _ _ _ _ binderFresh paramsFresh bodyTree
                continuationTree =>
                have tailUnique := unique.tail_unique
                have normalizedTailUnique :
                    BinderNamesUnique
                      (paramIds params ++ (bodyBinders ++ restBinders)) := by
                  simpa [LCNF.FunDecl.params, List.append_assoc] using
                    tailUnique
                have bodyContinuationUnique :
                    BinderNamesUnique (bodyBinders ++ restBinders) := by
                  exact BinderNamesUnique.right_of_append
                    (left := paramIds params) normalizedTailUnique
                have bodyTransfer :
                    BinderAbsenceTransfers bodyBinders final ambient := by
                  intro forbidden member absent
                  exact transfer forbidden (by simp [member]) absent
                have continuationTransfer :
                    BinderAbsenceTransfers restBinders
                      continuationUsed ambient := by
                  intro forbidden member absent
                  apply transfer forbidden (by simp [member])
                  have continuationFresh :=
                    continuationListing.memberFreshForRoot
                      continuationTree member
                  have variablesFresh :
                      FreshForScope forbidden
                        (index.pushParams params).sourceScope := by
                    apply freshForScope_pushParams
                    · simpa [ScopeIndex.pushJoin] using
                        continuationFresh.1
                    · apply paramBindersAvoid_of_binderNamesAvoid
                      exact normalizedTailUnique.left_avoids_of_mem_right
                        (show forbidden ∈ bodyBinders ++ restBinders by
                          simp [member])
                  have joinsFresh :
                      FreshForScope forbidden
                        (index.pushParams params).sourceJoins := by
                    rw [pushParams_sourceJoins]
                    exact freshForScope_of_subset continuationFresh.2
                      (scopeSubset_pushJoin_sourceJoins index fvarId)
                  exact
                    shadowCode_preserves_absent_of_binder_owned_to_right
                      bodyTree variablesFresh joinsFresh bodyListing
                      bodyContinuationUnique member absent body.result
                exact .joinRetained
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing
                    bodyContinuationUnique.right_of_append
                    continuationTransfer)
                  (ExactShadowCodeView.binderReady body.toGraph.view bodyTree
                    bodyListing bodyContinuationUnique.left_of_append
                    bodyTransfer)
    | @joinDeleted nextFuel continuationUsed sourceContinuation
        targetContinuation fvarId binderName params type sourceBody
        continuation absent =>
        cases listing with
        | @join bodyBinders _ restBinders _ bodyListing
            continuationListing =>
            cases wellFormed with
            | @jp _ _ _ _ _ _ _ binderFresh paramsFresh bodyTree
                continuationTree =>
                have continuationUnique :
                    BinderNamesUnique restBinders :=
                  unique.tail_unique.right_of_append
                have childTransfer :
                    BinderAbsenceTransfers restBinders final ambient := by
                  intro forbidden member absent
                  exact transfer forbidden (by simp [member]) absent
                exact .joinDeleted
                  (transfer _
                    (by
                      exact
                        (List.mem_cons_self :
                          fvarId ∈ fvarId :: _))
                    absent)
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing continuationUnique childTransfer)
    | @cases nextFuel beforeDiscr targetAlternatives discr typeName
        resultType sourceAlternatives alternatives =>
        cases listing with
        | cases alternativesListing =>
            cases wellFormed with
            | cases discrScoped normalization alternativesTree =>
                have alternativesTransfer :
                    BinderAbsenceTransfers binders beforeDiscr ambient := by
                  intro forbidden member absent
                  apply transfer forbidden member
                  exact insert_preserves_absent_of_scoped
                    (alternativesListing.memberFreshForRoot
                      alternativesTree member).1
                    discrScoped absent
                exact .cases
                  (ExactShadowAltListView.binderReady alternatives.view
                    alternativesTree alternativesListing unique
                    alternativesTransfer)
    | jump =>
        cases listing
        exact .jump
    | «return» =>
        cases listing
        exact .return
    | unreachable =>
        cases listing
        exact .unreachable
    | @objectSetRetained nextFuel continuationUsed sourceContinuation
        targetContinuation object field fieldIndex continuation live =>
        cases listing with
        | objectSet continuationListing =>
            cases wellFormed with
            | oset objectScoped fieldScoped continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers binders continuationUsed
                      ambient := by
                  intro forbidden member absent
                  apply transfer forbidden member
                  exact collectArg_preserves_absent absent
                    (argAvoids_of_scoped
                      (continuationListing.memberFreshForRoot
                        continuationTree member).1
                      fieldScoped)
                exact .objectSetRetained
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | objectSetDeleted continuation absent =>
        cases listing with
        | objectSet continuationListing =>
            cases wellFormed with
            | oset objectScoped fieldScoped continuationTree =>
                exact .objectSetDeleted
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique transfer)
    | @usizeSetRetained nextFuel continuationUsed sourceContinuation
        targetContinuation object field fieldIndex continuation live =>
        cases listing with
        | usizeSet continuationListing =>
            cases wellFormed with
            | uset objectScoped fieldScoped continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers binders continuationUsed
                      ambient := by
                  intro forbidden member absent
                  apply transfer forbidden member
                  exact insert_preserves_absent_of_scoped
                    (continuationListing.memberFreshForRoot
                      continuationTree member).1
                    fieldScoped absent
                exact .usizeSetRetained
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | usizeSetDeleted continuation absent =>
        cases listing with
        | usizeSet continuationListing =>
            cases wellFormed with
            | uset objectScoped fieldScoped continuationTree =>
                exact .usizeSetDeleted
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique transfer)
    | @scalarSetRetained nextFuel continuationUsed sourceContinuation
        targetContinuation object field width offset type continuation live =>
        cases listing with
        | scalarSet continuationListing =>
            cases wellFormed with
            | sset objectScoped fieldScoped continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers binders continuationUsed
                      ambient := by
                  intro forbidden member absent
                  apply transfer forbidden member
                  exact insert_preserves_absent_of_scoped
                    (continuationListing.memberFreshForRoot
                      continuationTree member).1
                    fieldScoped absent
                exact .scalarSetRetained
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | scalarSetDeleted continuation absent =>
        cases listing with
        | scalarSet continuationListing =>
            cases wellFormed with
            | sset objectScoped fieldScoped continuationTree =>
                exact .scalarSetDeleted
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique transfer)
    | @tagSet nextFuel continuationUsed sourceContinuation
        targetContinuation object tag continuation =>
        cases listing with
        | tagSet continuationListing =>
            cases wellFormed with
            | setTag objectScoped continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers binders continuationUsed
                      ambient := by
                  intro forbidden member absent
                  apply transfer forbidden member
                  exact insert_preserves_absent_of_scoped
                    (continuationListing.memberFreshForRoot
                      continuationTree member).1
                    objectScoped absent
                exact .tagSet
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | @increment nextFuel continuationUsed sourceContinuation
        targetContinuation object amount check persistent continuation =>
        cases listing with
        | increment continuationListing =>
            cases wellFormed with
            | inc objectScoped continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers binders continuationUsed
                      ambient := by
                  intro forbidden member absent
                  apply transfer forbidden member
                  exact insert_preserves_absent_of_scoped
                    (continuationListing.memberFreshForRoot
                      continuationTree member).1
                    objectScoped absent
                exact .increment
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | @decrement nextFuel continuationUsed sourceContinuation
        targetContinuation object amount check persistent objects
        continuation =>
        cases listing with
        | decrement continuationListing =>
            cases wellFormed with
            | dec objectScoped continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers binders continuationUsed
                      ambient := by
                  intro forbidden member absent
                  apply transfer forbidden member
                  exact insert_preserves_absent_of_scoped
                    (continuationListing.memberFreshForRoot
                      continuationTree member).1
                    objectScoped absent
                exact .decrement
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | @delete nextFuel continuationUsed sourceContinuation
        targetContinuation object continuation =>
        cases listing with
        | delete continuationListing =>
            cases wellFormed with
            | del objectScoped continuationTree =>
                have childTransfer :
                    BinderAbsenceTransfers binders continuationUsed
                      ambient := by
                  intro forbidden member absent
                  apply transfer forbidden member
                  exact insert_preserves_absent_of_scoped
                    (continuationListing.memberFreshForRoot
                      continuationTree member).1
                    objectScoped absent
                exact .delete
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)

  termination_by sizeOf source
  decreasing_by
    all_goals subst_vars
    all_goals first
      | simpa only [LCNF.Cases.alts] using
          (binderReady_caseAlts_sizeOf_lt
            (LCNF.Cases.mk _ _ _ _))
      | (simp_wf <;> try omega)

  theorem ExactShadowAltListView.binderReady
      (view :
        ExactShadowAltListView fuel initial final source target)
      (wellFormed : ScopedCodeWellFormedAlts index source)
      (listing : AltBinderList source binders)
      (unique : BinderNamesUnique binders)
      (transfer : BinderAbsenceTransfers binders final ambient) :
      ExactShadowAltListBinderReady ambient view := by
    cases view with
    | nil =>
        cases listing
        exact .nil
    | @ctor middle sourceBody targetBody _ sourceRest targetRest info body
        rest =>
        cases listing with
        | @ctor _ bodyBinders _ restBinders _ bodyListing restListing =>
            cases wellFormed with
            | ctor bodyTree restTree =>
                have bodyTransfer :
                    BinderAbsenceTransfers bodyBinders middle ambient := by
                  intro forbidden member absent
                  apply transfer forbidden (by simp [member])
                  have fresh :=
                    bodyListing.memberFreshForRoot bodyTree member
                  exact
                    shadowAltList_preserves_absent_of_binder_owned_to_left
                      restTree fresh.1 fresh.2 restListing unique member
                      absent rest.result
                have restTransfer :
                    BinderAbsenceTransfers restBinders final ambient :=
                  transfer.mono
                    (fun forbidden member => by simp [member])
                exact .ctor
                  (ExactShadowCodeView.binderReady body.toGraph.view
                    bodyTree bodyListing unique.left_of_append
                    bodyTransfer)
                  (ExactShadowAltListView.binderReady rest.view restTree
                    restListing unique.right_of_append restTransfer)
    | @default middle sourceBody targetBody _ sourceRest targetRest body
        rest =>
        cases listing with
        | @default _ bodyBinders _ restBinders bodyListing restListing =>
            cases wellFormed with
            | default bodyTree restTree =>
                have bodyTransfer :
                    BinderAbsenceTransfers bodyBinders middle ambient := by
                  intro forbidden member absent
                  apply transfer forbidden (by simp [member])
                  have fresh :=
                    bodyListing.memberFreshForRoot bodyTree member
                  exact
                    shadowAltList_preserves_absent_of_binder_owned_to_left
                      restTree fresh.1 fresh.2 restListing unique member
                      absent rest.result
                have restTransfer :
                    BinderAbsenceTransfers restBinders final ambient :=
                  transfer.mono
                    (fun forbidden member => by simp [member])
                exact .default
                  (ExactShadowCodeView.binderReady body.toGraph.view
                    bodyTree bodyListing unique.left_of_append
                    bodyTransfer)
                  (ExactShadowAltListView.binderReady rest.view restTree
                    restListing unique.right_of_append restTransfer)

  termination_by sizeOf source
  decreasing_by
    all_goals subst_vars
    all_goals first
      | exact binderReady_altCode_sizeOf_lt_cons _ _
      | (simp_wf <;> try omega)

end

/-- Root-level hereditary readiness from an explicit transparent binder
enumeration.  At the root the ambient liveness set is the exact final set, so
the transfer obligation is reflexive. -/
theorem ExactShadowCodeGraph.binderReady_of_listing
    (exact : ExactShadowCodeGraph fuel final source target)
    (wellFormed : ScopedCodeWellFormedTree index source)
    (listing : CodeBinderList source binders)
    (unique : BinderNamesUnique binders) :
    ExactShadowCodeBinderReady final exact.view :=
  ExactShadowCodeView.binderReady exact.view wellFormed listing unique
    (BinderAbsenceTransfers.refl binders final)

/-- Ownership-packaged spelling for downstream semantic proofs. -/
theorem ExactShadowCodeGraph.binderReady
    (exact : ExactShadowCodeGraph fuel final source target)
    (wellFormed : ScopedCodeWellFormedTree index source)
    (ownership : CodeBinderOwnership source) :
    ExactShadowCodeBinderReady final exact.view :=
  exact.binderReady_of_listing wellFormed ownership.listing
    ownership.unique

/-- Compiler-facing canonical spelling: checked scoping plus uniqueness of
the transparent `codeBinderIds` enumeration suffices for hereditary
readiness of every exact deletion branch. -/
theorem ExactShadowCodeGraph.binderReady_of_canonical
    (exact : ExactShadowCodeGraph fuel final source target)
    (wellFormed : ScopedCodeWellFormedTree index source)
    (unique : BinderNamesUnique (codeBinderIds source)) :
    ExactShadowCodeBinderReady final exact.view := by
  rcases CodeBinderList.canonicalExists source with ⟨listing⟩
  exact exact.binderReady_of_listing wellFormed listing unique

/-- Transparent replay of the let deletion decision at an exact traversal
seed.  `true` means the continuation succeeded, the binder was absent, and
the value passed `safeToElim`. -/
def shadowLetWasDeleted (fuel : Nat) (initial : UsedLocals)
    (declaration : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure) : Bool :=
  match fuel with
  | 0 => false
  | nextFuel + 1 =>
      match shadowCode? nextFuel initial continuation with
      | none => false
      | some (_, continuationUsed) =>
          !continuationUsed.contains declaration.fvarId &&
            safeToElim declaration.value

/-- Transparent replay of the join deletion decision. -/
def shadowJoinWasDeleted (fuel : Nat) (initial : UsedLocals)
    (declaration : LCNF.FunDecl .impure)
    (continuation : LCNF.Code .impure) : Bool :=
  match fuel with
  | 0 => false
  | nextFuel + 1 =>
      match shadowCode? nextFuel initial continuation with
      | none => false
      | some (_, continuationUsed) =>
          !continuationUsed.contains declaration.fvarId

/-- A successful exact let run selected as deleted exposes binder absence in
its exact final liveness set. -/
theorem ExactShadowCodeGraph.deletedLet_absent
    (exact : ExactShadowCodeGraph fuel final
      (.let declaration continuation) target)
    (deleted :
      shadowLetWasDeleted fuel exact.initial declaration continuation =
        true) :
    final.contains declaration.fvarId = false := by
  cases fuel with
  | zero => simp [shadowLetWasDeleted] at deleted
  | succ nextFuel =>
      cases continuationResult :
          shadowCode? nextFuel exact.initial continuation with
      | none => simp [shadowLetWasDeleted, continuationResult] at deleted
      | some output =>
          obtain ⟨targetContinuation, continuationUsed⟩ := output
          simp only [shadowLetWasDeleted, continuationResult,
            Bool.not_eq_true', Bool.and_eq_true] at deleted
          have keep :
              ¬(declaration.fvarId ∈ continuationUsed ∨
                safeToElim declaration.value = false) := by
            intro keep
            rcases keep with binderLive | notSafe <;> simp_all
          have exactResult := exact.result
          simp [shadowCode?, continuationResult, keep] at exactResult
          rcases exactResult with ⟨rfl, rfl⟩
          exact deleted.1

/-- A successful exact join run selected as deleted likewise exposes binder
absence in its exact final liveness set. -/
theorem ExactShadowCodeGraph.deletedJoin_absent
    (exact : ExactShadowCodeGraph fuel final
      (.jp declaration continuation) target)
    (deleted :
      shadowJoinWasDeleted fuel exact.initial declaration continuation =
        true) :
    final.contains declaration.fvarId = false := by
  cases declaration with
  | mk fvarId binderName params type body =>
      cases fuel with
      | zero => simp [shadowJoinWasDeleted] at deleted
      | succ nextFuel =>
          cases continuationResult :
              shadowCode? nextFuel exact.initial continuation with
          | none =>
              simp [shadowJoinWasDeleted, continuationResult] at deleted
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              simp only [shadowJoinWasDeleted, continuationResult,
                LCNF.FunDecl.fvarId, Bool.not_eq_true'] at deleted
              have keep : ¬fvarId ∈ continuationUsed := by
                simpa using deleted
              have exactResult := exact.result
              simp [shadowCode?, continuationResult, keep] at exactResult
              rcases exactResult with ⟨rfl, rfl⟩
              exact deleted

/-- Static active-node readiness for an exact graph.  The source equalities
avoid a dependent match and make the definition easy to consume from later
recursive graph certificates. -/
def ExactShadowCodeHeadBinderReady
    (exact : ExactShadowCodeGraph fuel final source target) : Prop :=
  (∀ declaration continuation,
      source = .let declaration continuation →
      shadowLetWasDeleted fuel exact.initial declaration continuation =
          true →
        final.contains declaration.fvarId = false) ∧
    ∀ declaration continuation,
      source = .jp declaration continuation →
      shadowJoinWasDeleted fuel exact.initial declaration continuation =
          true →
        final.contains declaration.fvarId = false

theorem ExactShadowCodeGraph.headBinderReady
    (exact : ExactShadowCodeGraph fuel final source target) :
    ExactShadowCodeHeadBinderReady exact := by
  constructor
  · intro declaration continuation sourceEq deleted
    subst source
    exact exact.deletedLet_absent deleted
  · intro declaration continuation sourceEq deleted
    subst source
    exact exact.deletedJoin_absent deleted

end Fir.LeanIR.Passes.ElimDead
