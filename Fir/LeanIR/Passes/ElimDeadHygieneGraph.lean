import Fir.LeanIR.Passes.ElimDeadHygiene
import Fir.LeanIR.Passes.ElimDeadProgram

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler

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
