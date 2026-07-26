import Fir.LeanIR.Passes.ElimDeadHygiene
import Fir.LeanIR.Passes.ElimDeadProgram

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.ImpureHygiene
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.NonLockstep.Structural
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

/-- Forget an exact run directly into larger operational fuel and liveness
indices.  Residual machine controls use this form because the compiler
decreases local traversal fuel while the global proof relation retains its
original bound. -/
theorem ExactShadowCodeGraph.toShadowCodeGraphAt
    (exact : ExactShadowCodeGraph fuel final source target)
    (fuelBound : fuel ≤ outerFuel)
    (usedBound : UsedSubset final ambient) :
    ShadowCodeGraph outerFuel ambient source target :=
  ⟨fuel, exact.initial, final, fuelBound, exact.result, usedBound⟩

/-- Declaration-facing exact relation.  Unlike `ShadowCodeRelated`, this
retains the full pass fuel and exact final liveness set produced from the
declaration seed, so later invocation proofs can recover the canonical view. -/
def ExactShadowCodeRelated (fuel : Nat)
    (source target : LCNF.Code .impure) : Prop :=
  ∃ final, Nonempty (ExactShadowCodeGraph fuel final source target)

/-- Forget exact declaration provenance into the monotone runtime relation. -/
theorem ExactShadowCodeRelated.toShadowCodeRelated
    (exact : ExactShadowCodeRelated fuel source target) :
    ShadowCodeRelated fuel source target := by
  rcases exact with ⟨final, ⟨graph⟩⟩
  exact ⟨final, graph.toShadowCodeGraph⟩

/-- Forget exact provenance inside one declaration value. -/
theorem forgetExactShadowDeclValue
    (related :
      DeclValueRelated (ExactShadowCodeRelated fuel) source target) :
    DeclValueRelated (ShadowCodeRelated fuel) source target := by
  cases related with
  | code exact => exact .code exact.toShadowCodeRelated
  | extern metadata => exact .extern metadata

/-- Pointwise declaration forgetting preserves every ABI field and changes
only the relation carried by an internal code body. -/
theorem forgetExactShadowDecl
    (related : DeclRelated (ExactShadowCodeRelated fuel) source target) :
    DeclRelated (ShadowCodeRelated fuel) source target := by
  exact {
    name_eq := related.name_eq
    levelParams_eq := related.levelParams_eq
    type_eq := related.type_eq
    params_eq := related.params_eq
    safe_eq := related.safe_eq
    value := forgetExactShadowDeclValue related.value
    recursive_eq := related.recursive_eq
    inlineAttr_eq := related.inlineAttr_eq
  }

/-- Whole-program forgetting from exact declaration bodies to the runtime
graph used by the non-lockstep machine relation. -/
theorem forgetExactShadowProgram
    (related : ProgramRelated (ExactShadowCodeRelated fuel) source target) :
    ProgramRelated (ShadowCodeRelated fuel) source target :=
  listRel_mono (fun declaration =>
    forgetExactShadowDecl declaration) related

/-- A successful declaration run retains the exact full-fuel traversal of an
internal body; external declarations are unchanged. -/
theorem shadowDecl_exactRelated
    (result : shadowDecl? fuel source = some target) :
    DeclRelated (ExactShadowCodeRelated fuel) source target := by
  cases valueEq : source.value with
  | extern metadata =>
      simp [shadowDecl?, valueEq] at result
      subst target
      exact {
        name_eq := rfl
        levelParams_eq := rfl
        type_eq := rfl
        params_eq := rfl
        safe_eq := rfl
        value := by
          rw [valueEq]
          exact .extern metadata
        recursive_eq := rfl
        inlineAttr_eq := rfl
      }
  | code code =>
      cases transformed : shadowCode? fuel {} code with
      | none => simp [shadowDecl?, valueEq, transformed] at result
      | some output =>
          obtain ⟨targetCode, final⟩ := output
          simp [shadowDecl?, valueEq, transformed] at result
          subst target
          exact {
            name_eq := rfl
            levelParams_eq := rfl
            type_eq := rfl
            params_eq := rfl
            safe_eq := rfl
            value := by
              rw [valueEq]
              exact .code ⟨final, ⟨⟨{}, transformed⟩⟩⟩
            recursive_eq := rfl
            inlineAttr_eq := rfl
          }

/-- The declaration-list traversal retains exact provenance pointwise. -/
theorem shadowDecls_exactRelated
    (result : shadowDecls? fuel sources = some targets) :
    ListRel (DeclRelated (ExactShadowCodeRelated fuel)) sources targets := by
  induction sources generalizing targets with
  | nil =>
      simp [shadowDecls?] at result
      subst targets
      exact .nil
  | cons source rest ih =>
      cases headResult : shadowDecl? fuel source with
      | none => simp [shadowDecls?, headResult] at result
      | some target =>
          cases tailResult : shadowDecls? fuel rest with
          | none => simp [shadowDecls?, headResult, tailResult] at result
          | some targetsRest =>
              simp [shadowDecls?, headResult, tailResult] at result
              subst targets
              exact .cons (shadowDecl_exactRelated headResult) (ih tailResult)

/-- A successful whole-program run preserves exact full-fuel provenance for
every transformed internal declaration body. -/
theorem shadowProgram_exactRelated
    (result : shadowProgram? fuel source = some target) :
    ProgramRelated (ExactShadowCodeRelated fuel) source target := by
  cases declarationsResult : shadowDecls? fuel source.decls.toList with
  | none => simp [shadowProgram?, declarationsResult] at result
  | some declarations =>
      simp [shadowProgram?, declarationsResult] at result
      subst target
      unfold ProgramRelated
      simpa using shadowDecls_exactRelated declarationsResult

/-- Exact declaration relation enriched with the two static source facts
consumed by canonical active-code readiness.  The scope index is existential
so residual bodies may retain the precise lexical index inherited from their
parent traversal. -/
def CanonicalExactShadowCodeRelated (fuel : Nat)
    (source target : LCNF.Code .impure) : Prop :=
  ∃ final,
    Nonempty (ExactShadowCodeGraph fuel final source target) ∧
      ∃ index,
        ScopedCodeWellFormedTree index source ∧
          BinderNamesUnique (codeBinderIds source)

/-- Forget the checked static package while retaining exact pass provenance. -/
theorem CanonicalExactShadowCodeRelated.toExact
    (canonical : CanonicalExactShadowCodeRelated fuel source target) :
    ExactShadowCodeRelated fuel source target := by
  rcases canonical with ⟨final, exact, index, wellFormed, unique⟩
  exact ⟨final, exact⟩

/-- Forget the canonical package inside one declaration value. -/
theorem forgetCanonicalExactShadowDeclValue
    (related :
      DeclValueRelated (CanonicalExactShadowCodeRelated fuel) source target) :
    DeclValueRelated (ExactShadowCodeRelated fuel) source target := by
  cases related with
  | code canonical => exact .code canonical.toExact
  | extern metadata => exact .extern metadata

/-- Pointwise program forgetting from canonical exact declaration bodies. -/
theorem forgetCanonicalExactShadowProgram
    (related :
      ProgramRelated (CanonicalExactShadowCodeRelated fuel) source target) :
    ProgramRelated (ExactShadowCodeRelated fuel) source target := by
  apply listRel_mono (related := related)
  intro left right declaration
  exact {
    name_eq := declaration.name_eq
    levelParams_eq := declaration.levelParams_eq
    type_eq := declaration.type_eq
    params_eq := declaration.params_eq
    safe_eq := declaration.safe_eq
    value := forgetCanonicalExactShadowDeclValue declaration.value
    recursive_eq := declaration.recursive_eq
    inlineAttr_eq := declaration.inlineAttr_eq
  }

/-- A checked declaration and its successful transparent run produce a
canonical exact body relation.  Declaration parameters are removed from the
global uniqueness list after establishing the body's own uniqueness. -/
theorem shadowDecl_canonicalExactRelated
    (wellFormed : DeclElimDeadWellFormed source)
    (result : shadowDecl? fuel source = some target) :
    DeclRelated (CanonicalExactShadowCodeRelated fuel) source target := by
  cases valueEq : source.value with
  | extern metadata =>
      simp [shadowDecl?, valueEq] at result
      subst target
      exact {
        name_eq := rfl
        levelParams_eq := rfl
        type_eq := rfl
        params_eq := rfl
        safe_eq := rfl
        value := by
          rw [valueEq]
          exact .extern metadata
        recursive_eq := rfl
        inlineAttr_eq := rfl
      }
  | code code =>
      have certificate := wellFormed.certificate
      rw [DeclElimDeadCertificate, valueEq] at certificate
      cases transformed : shadowCode? fuel {} code with
      | none => simp [shadowDecl?, valueEq, transformed] at result
      | some output =>
          obtain ⟨targetCode, final⟩ := output
          simp [shadowDecl?, valueEq, transformed] at result
          subst target
          exact {
            name_eq := rfl
            levelParams_eq := rfl
            type_eq := rfl
            params_eq := rfl
            safe_eq := rfl
            value := by
              rw [valueEq]
              exact .code ⟨final, ⟨⟨{}, transformed⟩⟩,
                ScopeIndex.empty.pushParams source.params,
                certificate.2.1,
                BinderNamesUnique.right_of_append certificate.2.2⟩
            recursive_eq := rfl
            inlineAttr_eq := rfl
          }

/-- Checked declaration lists retain canonical exact provenance pointwise. -/
theorem shadowDecls_canonicalExactRelated
    (wellFormed : ∀ declaration, declaration ∈ sources →
      DeclElimDeadWellFormed declaration)
    (result : shadowDecls? fuel sources = some targets) :
    ListRel (DeclRelated (CanonicalExactShadowCodeRelated fuel))
      sources targets := by
  induction sources generalizing targets with
  | nil =>
      simp [shadowDecls?] at result
      subst targets
      exact .nil
  | cons source rest ih =>
      cases headResult : shadowDecl? fuel source with
      | none => simp [shadowDecls?, headResult] at result
      | some target =>
          cases tailResult : shadowDecls? fuel rest with
          | none => simp [shadowDecls?, headResult, tailResult] at result
          | some targetsRest =>
              simp [shadowDecls?, headResult, tailResult] at result
              subst targets
              apply ListRel.cons
              · exact shadowDecl_canonicalExactRelated
                  (wellFormed source (by simp)) headResult
              · apply ih
                · intro declaration member
                  exact wellFormed declaration (by simp [member])
                · exact tailResult

/-- A successful whole-program run over a checked, transparently unique
source program retains exact branch provenance and canonical source facts for
every internal declaration body. -/
theorem shadowProgram_canonicalExactRelated
    (wellFormed : ProgramElimDeadWellFormed source)
    (result : shadowProgram? fuel source = some target) :
    ProgramRelated (CanonicalExactShadowCodeRelated fuel) source target := by
  cases declarationsResult : shadowDecls? fuel source.decls.toList with
  | none => simp [shadowProgram?, declarationsResult] at result
  | some declarations =>
      simp [shadowProgram?, declarationsResult] at result
      subst target
      unfold ProgramRelated
      apply shadowDecls_canonicalExactRelated
        (result := declarationsResult)
      intro declaration member
      exact (wellFormed.declaration member)

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

/-- Forget a child exact run into any enclosing operational fuel/liveness
index justified by the two monotonicity bounds. -/
theorem ExactShadowCodeRun.toShadowCodeGraphAt
    (run : ExactShadowCodeRun fuel initial final source target)
    (fuelBound : fuel ≤ outerFuel)
    (usedBound : UsedSubset final ambient) :
    ShadowCodeGraph outerFuel ambient source target :=
  ⟨fuel, initial, final, fuelBound, run.result, usedBound⟩

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

/-- Reconstruct the canonical exact graph from a proof-relevant branch view.
This is the inverse direction needed by semantic consumers: after inspecting
the branch in `Type`, they can forget it to the operational graph without
asking a proof-irrelevant residual which branch occurred. -/
def ExactShadowCodeView.toGraph
    (view : ExactShadowCodeView initial fuel final source target) :
    ExactShadowCodeGraph fuel final source target := by
  cases view with
  | letRetained continuation keep =>
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, keep]⟩
  | @letDeleted nextFuel continuationUsed sourceContinuation
      targetContinuation declaration continuation absent safe =>
      have notMember :
          ¬declaration.fvarId ∈ final := by
        simpa using absent
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, notMember, safe]⟩
  | @joinRetained nextFuel continuationUsed sourceContinuation
      targetContinuation fvarId bodyUsed sourceBody targetBody binderName
      params type continuation live body =>
      have member : fvarId ∈ continuationUsed := by
        simpa using live
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, member, body.result]⟩
  | @joinDeleted nextFuel continuationUsed sourceContinuation
      targetContinuation fvarId binderName params type sourceBody
      continuation absent =>
      have notMember : ¬fvarId ∈ final := by
        simpa using absent
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, notMember]⟩
  | cases alternatives =>
      exact ⟨initial, by
        simp [shadowCode?, alternatives.result]⟩
  | jump =>
      exact ⟨initial, by cases fuel <;> simp [shadowCode?]⟩
  | «return» =>
      exact ⟨initial, by cases fuel <;> simp [shadowCode?]⟩
  | unreachable =>
      exact ⟨initial, by cases fuel <;> simp [shadowCode?]⟩
  | @objectSetRetained nextFuel continuationUsed sourceContinuation
      targetContinuation object field fieldIndex continuation live =>
      have member : object ∈ continuationUsed := by
        simpa using live
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, member]⟩
  | @objectSetDeleted nextFuel continuationUsed sourceContinuation
      targetContinuation object field fieldIndex continuation absent =>
      have notMember : ¬object ∈ final := by
        simpa using absent
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, notMember]⟩
  | @usizeSetRetained nextFuel continuationUsed sourceContinuation
      targetContinuation object field fieldIndex continuation live =>
      have member : object ∈ continuationUsed := by
        simpa using live
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, member]⟩
  | @usizeSetDeleted nextFuel continuationUsed sourceContinuation
      targetContinuation object field fieldIndex continuation absent =>
      have notMember : ¬object ∈ final := by
        simpa using absent
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, notMember]⟩
  | @scalarSetRetained nextFuel continuationUsed sourceContinuation
      targetContinuation object field width offset type continuation live =>
      have member : object ∈ continuationUsed := by
        simpa using live
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, member]⟩
  | @scalarSetDeleted nextFuel continuationUsed sourceContinuation
      targetContinuation object field width offset type continuation absent =>
      have notMember : ¬object ∈ final := by
        simpa using absent
      exact ⟨initial, by
        simp [shadowCode?, continuation.result, notMember]⟩
  | tagSet continuation =>
      exact ⟨initial, by
        simp [shadowCode?, continuation.result]⟩
  | increment continuation =>
      exact ⟨initial, by
        simp [shadowCode?, continuation.result]⟩
  | decrement continuation =>
      exact ⟨initial, by
        simp [shadowCode?, continuation.result]⟩
  | delete continuation =>
      exact ⟨initial, by
        simp [shadowCode?, continuation.result]⟩

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

set_option autoImplicit false in
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
        {initial continuationUsed : UsedLocals}
        {nextFuel : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {declaration : LCNF.LetDecl .impure}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {keep :
          declaration.fvarId ∈ continuationUsed ∨
            safeToElim declaration.value = false}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.letRetained continuation keep)
    | letDeleted
        {initial continuationUsed : UsedLocals}
        {nextFuel : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {declaration : LCNF.LetDecl .impure}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {absent :
          continuationUsed.contains declaration.fvarId = false}
        {safe : safeToElim declaration.value = true}
        (ambientAbsent :
          ambient.contains declaration.fvarId = false)
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.letDeleted
            (declaration := declaration) continuation absent safe)
    | joinRetained
        {initial continuationUsed bodyUsed : UsedLocals}
        {nextFuel : Nat}
        {sourceContinuation targetContinuation sourceBody targetBody :
          LCNF.Code .impure}
        {fvarId : FVarId} {binderName : Name}
        {params : Array (LCNF.Param .impure)} {type : Expr}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {live : continuationUsed.contains fvarId = true}
        {body :
          ExactShadowCodeRun nextFuel continuationUsed bodyUsed
            sourceBody targetBody}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view)
        (bodyReady :
          ExactShadowCodeBinderReady ambient body.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.joinRetained
            (binderName := binderName) (params := params) (type := type)
            continuation live body)
    | joinDeleted
        {initial continuationUsed : UsedLocals}
        {nextFuel : Nat}
        {sourceContinuation targetContinuation sourceBody :
          LCNF.Code .impure}
        {fvarId : FVarId} {binderName : Name}
        {params : Array (LCNF.Param .impure)} {type : Expr}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {absent : continuationUsed.contains fvarId = false}
        (ambientAbsent : ambient.contains fvarId = false)
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.joinDeleted
            (binderName := binderName) (params := params) (type := type)
            (sourceBody := sourceBody) continuation absent)
    | cases
        {initial beforeDiscr : UsedLocals}
        {nextFuel : Nat}
        {sourceAlternatives : Array (LCNF.Alt .impure)}
        {targetAlternatives : List (LCNF.Alt .impure)}
        {discr : FVarId} {typeName : Name} {resultType : Expr}
        {alternatives :
          ExactShadowAltListRun nextFuel initial beforeDiscr
            sourceAlternatives.toList targetAlternatives}
        (alternativesReady :
          ExactShadowAltListBinderReady ambient alternatives.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.cases
            (discr := discr) (typeName := typeName)
            (resultType := resultType) alternatives)
    | jump
        {initial : UsedLocals} {fuel : Nat}
        {join : FVarId} {arguments : Array (LCNF.Arg .impure)} :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.jump
            (initial := initial) (fuel := fuel)
            (join := join) (arguments := arguments))
    | return
        {initial : UsedLocals} {fuel : Nat} {result : FVarId} :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.return
            (initial := initial) (fuel := fuel) (result := result))
    | unreachable
        {initial : UsedLocals} {fuel : Nat} {type : Expr} :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.unreachable
            (initial := initial) (fuel := fuel) (type := type))
    | objectSetRetained
        {initial continuationUsed : UsedLocals}
        {nextFuel index : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object : FVarId} {field : LCNF.Arg .impure}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {live : continuationUsed.contains object = true}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.objectSetRetained
            (index := index) (field := field) continuation live)
    | objectSetDeleted
        {initial continuationUsed : UsedLocals}
        {nextFuel index : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object : FVarId} {field : LCNF.Arg .impure}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {absent : continuationUsed.contains object = false}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.objectSetDeleted
            (index := index) (field := field) continuation absent)
    | usizeSetRetained
        {initial continuationUsed : UsedLocals}
        {nextFuel index : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object field : FVarId}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {live : continuationUsed.contains object = true}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.usizeSetRetained
            (index := index) (field := field) continuation live)
    | usizeSetDeleted
        {initial continuationUsed : UsedLocals}
        {nextFuel index : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object field : FVarId}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {absent : continuationUsed.contains object = false}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.usizeSetDeleted
            (index := index) (field := field) continuation absent)
    | scalarSetRetained
        {initial continuationUsed : UsedLocals}
        {nextFuel width offset : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object field : FVarId} {type : Expr}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {live : continuationUsed.contains object = true}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.scalarSetRetained
            (field := field) (width := width) (offset := offset)
            (type := type) continuation live)
    | scalarSetDeleted
        {initial continuationUsed : UsedLocals}
        {nextFuel width offset : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object field : FVarId} {type : Expr}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        {absent : continuationUsed.contains object = false}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.scalarSetDeleted
            (field := field) (width := width) (offset := offset)
            (type := type) continuation absent)
    | tagSet
        {initial continuationUsed : UsedLocals}
        {nextFuel tag : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object : FVarId}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.tagSet
            (object := object) (tag := tag) continuation)
    | increment
        {initial continuationUsed : UsedLocals}
        {nextFuel amount : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object : FVarId} {check persistent : Bool}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.increment
            (object := object) (amount := amount)
            (check := check) (persistent := persistent) continuation)
    | decrement
        {initial continuationUsed : UsedLocals}
        {nextFuel amount : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object : FVarId} {check persistent : Bool}
        {objects : Option Nat}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.decrement
            (object := object) (amount := amount)
            (check := check) (persistent := persistent)
            (objects := objects) continuation)
    | delete
        {initial continuationUsed : UsedLocals}
        {nextFuel : Nat}
        {sourceContinuation targetContinuation : LCNF.Code .impure}
        {object : FVarId}
        {continuation :
          ExactShadowCodeRun nextFuel initial continuationUsed
            sourceContinuation targetContinuation}
        (continuationReady :
          ExactShadowCodeBinderReady ambient
            continuation.toGraph.view) :
        ExactShadowCodeBinderReady ambient
          (ExactShadowCodeView.delete (object := object) continuation)

  /-- Alternative-list counterpart of `ExactShadowCodeBinderReady`. -/
  inductive ExactShadowAltListBinderReady (ambient : UsedLocals) :
      {fuel : Nat} → {initial final : UsedLocals} →
        {source target : List (LCNF.Alt .impure)} →
          ExactShadowAltListView fuel initial final source target → Prop where
    | nil
        {fuel : Nat} {initial : UsedLocals} :
        ExactShadowAltListBinderReady ambient ExactShadowAltListView.nil
    | ctor
        {fuel : Nat} {initial middle final : UsedLocals}
        {sourceBody targetBody : LCNF.Code .impure}
        {sourceRest targetRest : List (LCNF.Alt .impure)}
        {info : LCNF.CtorInfo}
        {body :
          ExactShadowCodeRun fuel initial middle sourceBody targetBody}
        {rest :
          ExactShadowAltListRun fuel middle final sourceRest targetRest}
        (bodyReady :
          ExactShadowCodeBinderReady ambient body.toGraph.view)
        (restReady :
          ExactShadowAltListBinderReady ambient rest.view) :
        ExactShadowAltListBinderReady ambient
          (ExactShadowAltListView.ctor (info := info) body rest)
    | default
        {fuel : Nat} {initial middle final : UsedLocals}
        {sourceBody targetBody : LCNF.Code .impure}
        {sourceRest targetRest : List (LCNF.Alt .impure)}
        {body :
          ExactShadowCodeRun fuel initial middle sourceBody targetBody}
        {rest :
          ExactShadowAltListRun fuel middle final sourceRest targetRest}
        (bodyReady :
          ExactShadowCodeBinderReady ambient body.toGraph.view)
        (restReady :
          ExactShadowAltListBinderReady ambient rest.view) :
        ExactShadowAltListBinderReady ambient
          (ExactShadowAltListView.default body rest)

end

/-- A deleted-let readiness certificate records absence for the binder in the
exact view itself.  This projection is also a kernel regression guard against
accidentally indexing the certificate by an unrelated declaration. -/
theorem ExactShadowCodeBinderReady.letDeleted_ambientAbsent
    {ambient initial continuationUsed : UsedLocals}
    {nextFuel : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {declaration : LCNF.LetDecl .impure}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {absent : continuationUsed.contains declaration.fvarId = false}
    {safe : safeToElim declaration.value = true}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.letDeleted continuation absent safe)) :
    ambient.contains declaration.fvarId = false := by
  cases ready with
  | letDeleted ambientAbsent _ => exact ambientAbsent

/-- Join-point counterpart of `letDeleted_ambientAbsent`: the projected
absence is tied to the join binder named by the exact deleted branch. -/
theorem ExactShadowCodeBinderReady.joinDeleted_ambientAbsent
    {ambient initial continuationUsed : UsedLocals}
    {nextFuel : Nat}
    {sourceContinuation targetContinuation sourceBody : LCNF.Code .impure}
    {fvarId : FVarId} {binderName : Name}
    {params : Array (LCNF.Param .impure)} {type : Expr}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {absent : continuationUsed.contains fvarId = false}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.joinDeleted
          (binderName := binderName) (params := params) (type := type)
          (sourceBody := sourceBody) continuation absent)) :
    ambient.contains fvarId = false := by
  cases ready with
  | joinDeleted ambientAbsent _ => exact ambientAbsent

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
                exact .letDeleted (absent := absent) (safe := safe)
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
                  (binderName := binderName) (params := params) (type := type)
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
                exact .joinDeleted (absent := absent)
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
                exact .cases (discr := discr) (typeName := typeName)
                  (resultType := resultType)
                  (ExactShadowAltListView.binderReady alternatives.view
                    alternativesTree alternativesListing unique
                    alternativesTransfer)
    | @jump terminalFuel join arguments =>
        cases listing
        exact .jump (initial := initial) (fuel := fuel)
          (join := join) (arguments := arguments)
    | @«return» terminalFuel result =>
        cases listing
        exact .return (initial := initial) (fuel := fuel)
          (result := result)
    | @unreachable terminalFuel type =>
        cases listing
        exact .unreachable (initial := initial) (fuel := fuel)
          (type := type)
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
                  (index := fieldIndex) (field := field)
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | @objectSetDeleted nextFuel continuationUsed sourceContinuation
        targetContinuation object objectIndex field continuation absent =>
        cases listing with
        | objectSet continuationListing =>
            cases wellFormed with
            | oset objectScoped fieldScoped continuationTree =>
                exact .objectSetDeleted
                  (index := objectIndex) (field := field)
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
                  (index := fieldIndex) (field := field)
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | @usizeSetDeleted nextFuel continuationUsed sourceContinuation
        targetContinuation object objectIndex field continuation absent =>
        cases listing with
        | usizeSet continuationListing =>
            cases wellFormed with
            | uset objectScoped fieldScoped continuationTree =>
                exact .usizeSetDeleted
                  (index := objectIndex) (field := field)
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
                  (field := field) (width := width) (offset := offset)
                  (type := type)
                  (ExactShadowCodeView.binderReady
                    continuation.toGraph.view continuationTree
                    continuationListing unique childTransfer)
    | @scalarSetDeleted nextFuel continuationUsed sourceContinuation
        targetContinuation object width offset field type continuation
        absent =>
        cases listing with
        | scalarSet continuationListing =>
            cases wellFormed with
            | sset objectScoped fieldScoped continuationTree =>
                exact .scalarSetDeleted
                  (field := field) (width := width) (offset := offset)
                  (type := type)
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
                exact .tagSet (object := object) (tag := tag)
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
                  (object := object) (amount := amount)
                  (check := check) (persistent := persistent)
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
                  (object := object) (amount := amount)
                  (check := check) (persistent := persistent)
                  (objects := objects)
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
                exact .delete (object := object)
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
        exact .nil (fuel := fuel) (initial := initial)
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
                exact .ctor (info := info)
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

/-- Exact code relation with the hereditary static deletion certificate
already constructed.  Runtime preservation can carry this smaller package
without retaining the original scope index or rebuilding binder ownership. -/
def BinderReadyExactShadowCodeRelated (fuel : Nat)
    (source target : LCNF.Code .impure) : Prop :=
  ∃ final, ∃ exact : ExactShadowCodeGraph fuel final source target,
    ExactShadowCodeBinderReady final exact.view

/-- Canonical checked source facts construct the hereditary exact relation. -/
theorem CanonicalExactShadowCodeRelated.toBinderReadyExact
    (canonical : CanonicalExactShadowCodeRelated fuel source target) :
    BinderReadyExactShadowCodeRelated fuel source target := by
  rcases canonical with
    ⟨final, ⟨exact⟩, index, wellFormed, unique⟩
  exact ⟨final, exact,
    exact.binderReady_of_canonical wellFormed unique⟩

/-- Lift canonical-to-hereditary forgetting through one declaration value. -/
theorem canonicalExactShadowDeclValue_toBinderReadyExact
    (related :
      DeclValueRelated (CanonicalExactShadowCodeRelated fuel) source target) :
    DeclValueRelated
      (BinderReadyExactShadowCodeRelated fuel) source target := by
  cases related with
  | code canonical => exact .code canonical.toBinderReadyExact
  | extern metadata => exact .extern metadata

/-- Lift canonical-to-hereditary forgetting through a whole program. -/
theorem canonicalExactShadowProgram_toBinderReadyExact
    (related :
      ProgramRelated (CanonicalExactShadowCodeRelated fuel) source target) :
    ProgramRelated
      (BinderReadyExactShadowCodeRelated fuel) source target := by
  apply listRel_mono (related := related)
  intro left right declaration
  exact {
    name_eq := declaration.name_eq
    levelParams_eq := declaration.levelParams_eq
    type_eq := declaration.type_eq
    params_eq := declaration.params_eq
    safe_eq := declaration.safe_eq
    value :=
      canonicalExactShadowDeclValue_toBinderReadyExact declaration.value
    recursive_eq := declaration.recursive_eq
    inlineAttr_eq := declaration.inlineAttr_eq
  }

/-- Compiler-run source theorem with all hereditary static body certificates
materialized pointwise in the program relation. -/
theorem shadowProgram_binderReadyExactRelated
    (wellFormed : ProgramElimDeadWellFormed source)
    (result : shadowProgram? fuel source = some target) :
    ProgramRelated
      (BinderReadyExactShadowCodeRelated fuel) source target :=
  canonicalExactShadowProgram_toBinderReadyExact
    (shadowProgram_canonicalExactRelated wellFormed result)

/-- Immediate hereditary certificates selected by the control-changing
`let`, `join`, and `cases` branches of an exact compiler view.  Matching on
the view, rather than inverting its indexed readiness proof, keeps computed
liveness indices such as `collectLetValue` opaque. -/
def ExactShadowCodeView.controlResidualBinderReady
    (ambient : UsedLocals)
    {initial : UsedLocals} {fuel : Nat} {final : UsedLocals}
    {source target : LCNF.Code .impure}
    (view : ExactShadowCodeView initial fuel final source target) : Prop :=
  match view with
  | .letRetained continuation _ =>
      ExactShadowCodeBinderReady ambient continuation.toGraph.view
  | .letDeleted continuation _ _ =>
      ExactShadowCodeBinderReady ambient continuation.toGraph.view
  | .joinRetained continuation _ body =>
      ExactShadowCodeBinderReady ambient continuation.toGraph.view ∧
        ExactShadowCodeBinderReady ambient body.toGraph.view
  | .joinDeleted continuation _ =>
      ExactShadowCodeBinderReady ambient continuation.toGraph.view
  | .cases alternatives =>
      ExactShadowAltListBinderReady ambient alternatives.view
  | .objectSetRetained continuation _
  | .objectSetDeleted continuation _
  | .usizeSetRetained continuation _
  | .usizeSetDeleted continuation _
  | .scalarSetRetained continuation _
  | .scalarSetDeleted continuation _
  | .tagSet continuation
  | .increment continuation
  | .decrement continuation
  | .delete continuation =>
      ExactShadowCodeBinderReady ambient continuation.toGraph.view
  | _ => True

/-- Hereditary readiness supplies the immediate residual certificates
described by its exact branch view. -/
theorem ExactShadowCodeBinderReady.controlResidualBinderReady
    (ready : ExactShadowCodeBinderReady ambient view) :
    view.controlResidualBinderReady ambient := by
  cases ready with
  | letRetained continuationReady => exact continuationReady
  | letDeleted _ continuationReady => exact continuationReady
  | joinRetained continuationReady bodyReady =>
      exact ⟨continuationReady, bodyReady⟩
  | joinDeleted _ continuationReady => exact continuationReady
  | cases alternativesReady => exact alternativesReady
  | objectSetRetained continuationReady
  | objectSetDeleted continuationReady
  | usizeSetRetained continuationReady
  | usizeSetDeleted continuationReady
  | scalarSetRetained continuationReady
  | scalarSetDeleted continuationReady
  | tagSet continuationReady
  | increment continuationReady
  | decrement continuationReady
  | delete continuationReady =>
      exact continuationReady
  | jump | «return» | unreachable => trivial

/-- Hereditary exact provenance embedded in the two monotonicity indices used
by runtime controls.  Child traversals consume less fuel, while their exact
final liveness set may be widened to the ambient set carried by an
environment, join table, or saved frame. -/
def BinderReadyShadowCodeGraph (fuel : Nat) (used : UsedLocals)
    (source target : LCNF.Code .impure) : Prop :=
  ∃ remaining final, remaining ≤ fuel ∧
    ∃ exact : ExactShadowCodeGraph remaining final source target,
      UsedSubset final used ∧
        ExactShadowCodeBinderReady used exact.view

/-- Hereditary alternative relation.  Metadata is unchanged and each body
retains an exact binder-ready compiler graph under the enclosing machine
fuel and liveness indices. -/
inductive BinderReadyShadowAltRelated (fuel : Nat) (used : UsedLocals) :
    LCNF.Alt .impure → LCNF.Alt .impure → Prop where
  | ctor (info : LCNF.CtorInfo)
      (body : BinderReadyShadowCodeGraph fuel used sourceBody targetBody) :
      BinderReadyShadowAltRelated fuel used
        (.ctorAlt info sourceBody) (.ctorAlt info targetBody)
  | default
      (body : BinderReadyShadowCodeGraph fuel used sourceBody targetBody) :
      BinderReadyShadowAltRelated fuel used
        (.default sourceBody) (.default targetBody)

def BinderReadyShadowAltListRelated (fuel : Nat) (used : UsedLocals)
    (source target : List (LCNF.Alt .impure)) : Prop :=
  ListRel (BinderReadyShadowAltRelated fuel used) source target

/-- Embed one exact child run into the bounded hereditary graph used by
runtime controls.  Keeping this constructor at the exact-run boundary avoids
reconstructing the child's seed when an operational step selects a residual
continuation or installed join body. -/
theorem ExactShadowCodeRun.toBinderReadyShadowCodeGraphAt
    (run : ExactShadowCodeRun childFuel initial final source target)
    (fuelBound : childFuel ≤ outerFuel)
    (usedBound : UsedSubset final ambient)
    (ready : ExactShadowCodeBinderReady ambient run.toGraph.view) :
    BinderReadyShadowCodeGraph outerFuel ambient source target :=
  ⟨childFuel, final, fuelBound, run.toGraph, usedBound, ready⟩

/-- Project an exact, binder-ready alternative traversal pointwise.  The
tail's liveness monotonicity widens each preceding body to the list's final
ambient index, matching the compiler's left-to-right liveness threading. -/
theorem ExactShadowAltListBinderReady.toRelated
    {childFuel outerFuel : Nat}
    {initial final ambient : UsedLocals}
    {source target : List (LCNF.Alt .impure)}
    {view :
      ExactShadowAltListView childFuel initial final source target}
    (ready : ExactShadowAltListBinderReady ambient view)
    (fuelBound : childFuel ≤ outerFuel)
    (usedBound : UsedSubset final ambient) :
    BinderReadyShadowAltListRelated outerFuel ambient source target := by
  induction source generalizing initial final target with
  | nil =>
      cases view
      exact .nil
  | cons alternative sourceRest ih =>
      cases view with
      | @ctor middle sourceBody targetBody _ sourceRest targetRest info body
          rest =>
          cases ready with
          | ctor bodyReady restReady =>
              have restSpec := shadowAltList_spec
                (transformCode := shadowCode? childFuel)
                (transformSpec := fun _ _ _ _ bodyRun =>
                  shadowCode_spec bodyRun)
                (result := rest.result)
              have bodyGraph :
                  BinderReadyShadowCodeGraph outerFuel ambient
                    sourceBody targetBody :=
                body.toBinderReadyShadowCodeGraphAt fuelBound
                  (restSpec.2.trans usedBound) bodyReady
              exact .cons (.ctor info bodyGraph)
                (ih (view := rest.view) restReady usedBound)
      | @default middle sourceBody targetBody _ sourceRest targetRest body
          rest =>
          cases ready with
          | default bodyReady restReady =>
              have restSpec := shadowAltList_spec
                (transformCode := shadowCode? childFuel)
                (transformSpec := fun _ _ _ _ bodyRun =>
                  shadowCode_spec bodyRun)
                (result := rest.result)
              have bodyGraph :
                  BinderReadyShadowCodeGraph outerFuel ambient
                    sourceBody targetBody :=
                body.toBinderReadyShadowCodeGraphAt fuelBound
                  (restSpec.2.trans usedBound) bodyReady
              exact .cons (.default bodyGraph)
                (ih (view := rest.view) restReady usedBound)

theorem BinderReadyShadowAltListRelated.findCtor
    (related :
      BinderReadyShadowAltListRelated fuel used source target) :
    OptionalRel (BinderReadyShadowCodeGraph fuel used)
      (findCtorAlt tag source) (findCtorAlt tag target) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      cases head with
      | ctor info body =>
          by_cases tagMatches : info.cidx == tag
          · simpa [findCtorAlt, tagMatches] using OptionalRel.some body
          · simpa [findCtorAlt, tagMatches] using ih
      | default body => simpa [findCtorAlt] using ih

theorem BinderReadyShadowAltListRelated.findDefault
    (related :
      BinderReadyShadowAltListRelated fuel used source target) :
    OptionalRel (BinderReadyShadowCodeGraph fuel used)
      (findDefaultAlt source) (findDefaultAlt target) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      cases head with
      | ctor info body => simpa [findDefaultAlt] using ih
      | default body =>
          simpa [findDefaultAlt] using OptionalRel.some body

theorem BinderReadyShadowAltListRelated.choose
    (related :
      BinderReadyShadowAltListRelated fuel used source target) :
    OptionalRel (BinderReadyShadowCodeGraph fuel used)
      (chooseAlt tag source) (chooseAlt tag target) := by
  unfold chooseAlt
  have constructors := related.findCtor (tag := tag)
  generalize sourceFoundEq : findCtorAlt tag source = sourceFound
    at constructors ⊢
  generalize targetFoundEq : findCtorAlt tag target = targetFound
    at constructors ⊢
  cases constructors with
  | none => exact related.findDefault
  | some body => exact .some body

/-- The exact `cases` view exposes a hereditary relation for every residual
alternative under the parent graph's bounds. -/
theorem ExactShadowCodeBinderReady.cases_alternativesRelated
    {initial beforeDiscr ambient : UsedLocals}
    {nextFuel outerFuel : Nat}
    {sourceAlternatives : Array (LCNF.Alt .impure)}
    {targetAlternatives : List (LCNF.Alt .impure)}
    {discr : FVarId} {typeName : Name} {resultType : Expr}
    {alternatives :
      ExactShadowAltListRun nextFuel initial beforeDiscr
        sourceAlternatives.toList targetAlternatives}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.cases
          (discr := discr) (typeName := typeName) (resultType := resultType)
          alternatives))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset (beforeDiscr.insert discr) ambient) :
    BinderReadyShadowAltListRelated outerFuel ambient
      sourceAlternatives.toList targetAlternatives := by
  have alternativesReady :
      ExactShadowAltListBinderReady ambient alternatives.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact alternativesReady.toRelated
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    ((usedSubset_insert beforeDiscr discr).trans usedBound)

/-- A retained let's exact hereditary certificate projects to its selected
continuation under the enclosing graph's fuel and liveness bounds. -/
theorem ExactShadowCodeBinderReady.letRetained_continuationGraph
    {initial continuationUsed : UsedLocals}
    {nextFuel outerFuel : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {declaration : LCNF.LetDecl .impure}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {keep :
      declaration.fvarId ∈ continuationUsed ∨
        safeToElim declaration.value = false}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.letRetained continuation keep))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound :
      UsedSubset
        (collectLetValue continuationUsed declaration.value) ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    ((collectLetValue_subset continuationUsed declaration.value).trans
      usedBound)
    continuationReady

/-- A deleted let's target is already its selected continuation, whose exact
certificate therefore becomes the post-step active-code graph directly. -/
theorem ExactShadowCodeBinderReady.letDeleted_continuationGraph
    {initial continuationUsed : UsedLocals}
    {nextFuel outerFuel : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {declaration : LCNF.LetDecl .impure}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {absent :
      continuationUsed.contains declaration.fvarId = false}
    {safe : safeToElim declaration.value = true}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.letDeleted continuation absent safe))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset continuationUsed ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    usedBound continuationReady

/-- A retained join first executes its continuation.  Liveness monotonicity
of the subsequently traversed body embeds that continuation's final set into
the enclosing final set. -/
theorem ExactShadowCodeBinderReady.joinRetained_continuationGraph
    {initial continuationUsed bodyUsed : UsedLocals}
    {nextFuel outerFuel : Nat}
    {sourceContinuation targetContinuation sourceBody targetBody :
      LCNF.Code .impure}
    {fvarId : FVarId} {binderName : Name}
    {params : Array (LCNF.Param .impure)} {type : Expr}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {live : continuationUsed.contains fvarId = true}
    {body :
      ExactShadowCodeRun nextFuel continuationUsed bodyUsed
        sourceBody targetBody}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.joinRetained
          (binderName := binderName) (params := params) (type := type)
          continuation live body))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset bodyUsed ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view :=
    ready.controlResidualBinderReady.1
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    ((shadowCode_spec body.result).2.trans usedBound)
    continuationReady

/-- The body installed by a retained join inherits the same enclosing fuel
and final-liveness bounds as the parent exact graph. -/
theorem ExactShadowCodeBinderReady.joinRetained_bodyGraph
    {initial continuationUsed bodyUsed : UsedLocals}
    {nextFuel outerFuel : Nat}
    {sourceContinuation targetContinuation sourceBody targetBody :
      LCNF.Code .impure}
    {fvarId : FVarId} {binderName : Name}
    {params : Array (LCNF.Param .impure)} {type : Expr}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {live : continuationUsed.contains fvarId = true}
    {body :
      ExactShadowCodeRun nextFuel continuationUsed bodyUsed
        sourceBody targetBody}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.joinRetained
          (binderName := binderName) (params := params) (type := type)
          continuation live body))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset bodyUsed ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient sourceBody targetBody := by
  have bodyReady :
      ExactShadowCodeBinderReady ambient body.toGraph.view :=
    ready.controlResidualBinderReady.2
  exact body.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    usedBound bodyReady

/-- A deleted join leaves only its exact continuation, with the parent's final
liveness set unchanged. -/
theorem ExactShadowCodeBinderReady.joinDeleted_continuationGraph
    {initial continuationUsed : UsedLocals}
    {nextFuel outerFuel : Nat}
    {sourceContinuation targetContinuation sourceBody : LCNF.Code .impure}
    {fvarId : FVarId} {binderName : Name}
    {params : Array (LCNF.Param .impure)} {type : Expr}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {absent : continuationUsed.contains fvarId = false}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.joinDeleted
          (binderName := binderName) (params := params) (type := type)
          (sourceBody := sourceBody) continuation absent))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset continuationUsed ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    usedBound continuationReady

/-- A retained object-field write widens its child liveness by the written
argument while preserving hereditary provenance in the continuation. -/
theorem ExactShadowCodeBinderReady.objectSetRetained_continuationGraph
    {initial continuationUsed ambient : UsedLocals}
    {nextFuel outerFuel index : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {object : FVarId} {field : LCNF.Arg .impure}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {live : continuationUsed.contains object = true}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.objectSetRetained
          (index := index) (field := field) continuation live))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset (collectArg continuationUsed field) ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    ((collectArg_subset continuationUsed field).trans usedBound)
    continuationReady

/-- A deleted object-field write selects its unchanged child liveness and
retains the child's hereditary provenance directly. -/
theorem ExactShadowCodeBinderReady.objectSetDeleted_continuationGraph
    {initial continuationUsed ambient : UsedLocals}
    {nextFuel outerFuel index : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {object : FVarId} {field : LCNF.Arg .impure}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    {absent : continuationUsed.contains object = false}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.objectSetDeleted
          (index := index) (field := field) continuation absent))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset continuationUsed ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    usedBound continuationReady

/-- An exact tag update widens only the operand liveness; its recursively
transformed continuation retains hereditary provenance under the parent
bounds. -/
theorem ExactShadowCodeBinderReady.tagSet_continuationGraph
    {initial continuationUsed ambient : UsedLocals}
    {nextFuel outerFuel tag : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {object : FVarId}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.tagSet
          (object := object) (tag := tag) continuation))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset (continuationUsed.insert object) ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    ((usedSubset_insert continuationUsed object).trans usedBound)
    continuationReady

/-- Hereditary continuation projection for a reference-count increment. -/
theorem ExactShadowCodeBinderReady.increment_continuationGraph
    {initial continuationUsed ambient : UsedLocals}
    {nextFuel outerFuel amount : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {object : FVarId} {check persistent : Bool}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.increment
          (object := object) (amount := amount)
          (check := check) (persistent := persistent) continuation))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset (continuationUsed.insert object) ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    ((usedSubset_insert continuationUsed object).trans usedBound)
    continuationReady

/-- Hereditary continuation projection for a reference-count decrement. -/
theorem ExactShadowCodeBinderReady.decrement_continuationGraph
    {initial continuationUsed ambient : UsedLocals}
    {nextFuel outerFuel amount : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {object : FVarId} {check persistent : Bool}
    {objects : Option Nat}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.decrement
          (object := object) (amount := amount)
          (check := check) (persistent := persistent)
          (objects := objects) continuation))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset (continuationUsed.insert object) ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    ((usedSubset_insert continuationUsed object).trans usedBound)
    continuationReady

/-- Hereditary continuation projection for a retained delete. -/
theorem ExactShadowCodeBinderReady.delete_continuationGraph
    {initial continuationUsed ambient : UsedLocals}
    {nextFuel outerFuel : Nat}
    {sourceContinuation targetContinuation : LCNF.Code .impure}
    {object : FVarId}
    {continuation :
      ExactShadowCodeRun nextFuel initial continuationUsed
        sourceContinuation targetContinuation}
    (ready :
      ExactShadowCodeBinderReady ambient
        (ExactShadowCodeView.delete
          (object := object) continuation))
    (fuelBound : nextFuel + 1 ≤ outerFuel)
    (usedBound : UsedSubset (continuationUsed.insert object) ambient) :
    BinderReadyShadowCodeGraph outerFuel ambient
      sourceContinuation targetContinuation := by
  have continuationReady :
      ExactShadowCodeBinderReady ambient continuation.toGraph.view := by
    simpa [ExactShadowCodeView.controlResidualBinderReady] using
      ready.controlResidualBinderReady
  exact continuation.toBinderReadyShadowCodeGraphAt
    (Nat.le_trans (Nat.le_succ nextFuel) fuelBound)
    ((usedSubset_insert continuationUsed object).trans usedBound)
    continuationReady

/-- Existential runtime-facing form for declaration bodies. -/
def BinderReadyShadowCodeRelated (fuel : Nat)
    (source target : LCNF.Code .impure) : Prop :=
  ∃ used, BinderReadyShadowCodeGraph fuel used source target

/-- Join declaration relation retaining hereditary exact provenance for every
live installed body. -/
structure BinderReadyShadowFunDeclRelated (fuel : Nat) (used : UsedLocals)
    (source target : LCNF.FunDecl .impure) : Prop where
  fvarId_eq : source.fvarId = target.fvarId
  binderName_eq : source.binderName = target.binderName
  params_eq : source.params = target.params
  type_eq : source.type = target.type
  value : BinderReadyShadowCodeGraph fuel used source.value target.value

/-- Extensional live-join relation whose observable entries retain hereditary
exact provenance.  Source-only entries remain permitted for join declarations
that the pass deleted and whose identifiers are absent from `used`. -/
def BinderReadyShadowJoinEnvRelated (fuel : Nat) (used : UsedLocals)
    (source target : JoinEnv) : Prop :=
  ∀ key, used.contains key = true →
    OptionalRel (BinderReadyShadowFunDeclRelated fuel used)
      (findJoinPoint? source key) (findJoinPoint? target key)

/-- Erase hereditary exact provenance while retaining the same bounded
runtime graph and ambient liveness set. -/
theorem BinderReadyShadowCodeGraph.toShadowCodeGraph
    (graph : BinderReadyShadowCodeGraph fuel used source target) :
    ShadowCodeGraph fuel used source target := by
  rcases graph with
    ⟨remaining, final, bounded, exact, subset, static⟩
  exact ⟨remaining, exact.initial, final, bounded, exact.result, subset⟩

/-- Declaration-facing erasure to the operational shadow relation. -/
theorem BinderReadyShadowCodeRelated.toShadowCodeRelated
    (related : BinderReadyShadowCodeRelated fuel source target) :
    ShadowCodeRelated fuel source target := by
  rcases related with ⟨used, graph⟩
  exact ⟨used, graph.toShadowCodeGraph⟩

/-- Erase hereditary provenance from one related live join declaration. -/
theorem BinderReadyShadowFunDeclRelated.toShadowFunDeclRelated
    (related :
      BinderReadyShadowFunDeclRelated fuel used source target) :
    ShadowFunDeclRelated fuel used source target := {
  fvarId_eq := related.fvarId_eq
  binderName_eq := related.binderName_eq
  params_eq := related.params_eq
  type_eq := related.type_eq
  value := related.value.toShadowCodeGraph
}

/-- Erase hereditary provenance pointwise from the live join environment. -/
theorem BinderReadyShadowJoinEnvRelated.toShadowJoinEnvRelated
    (related :
      BinderReadyShadowJoinEnvRelated fuel used source target) :
    ShadowJoinEnvRelated fuel used source target := by
  intro key member
  have found := related key member
  generalize sourceFound :
      findJoinPoint? source key = sourceResult at found ⊢
  generalize targetFound :
      findJoinPoint? target key = targetResult at found ⊢
  cases found with
  | none => exact .none
  | some declaration =>
      exact .some declaration.toShadowFunDeclRelated

/-- Empty join tables satisfy the hereditary live relation. -/
theorem BinderReadyShadowJoinEnvRelated.empty
    (fuel : Nat) (used : UsedLocals) :
    BinderReadyShadowJoinEnvRelated fuel used [] [] := by
  intro key member
  exact .none

/-- Install the same live key with hereditarily related bodies. -/
theorem BinderReadyShadowJoinEnvRelated.consBoth
    (declaration :
      BinderReadyShadowFunDeclRelated fuel used
        sourceDeclaration targetDeclaration)
    (rest :
      BinderReadyShadowJoinEnvRelated fuel used sourceJoins targetJoins) :
    BinderReadyShadowJoinEnvRelated fuel used
      ((key, sourceDeclaration) :: sourceJoins)
      ((key, targetDeclaration) :: targetJoins) := by
  intro target member
  by_cases sameName : key.name == target.name
  · simpa [findJoinPoint?, sameName] using
      (OptionalRel.some declaration)
  · simpa [findJoinPoint?, sameName] using rest target member

/-- Install equal live keys with hereditarily related bodies. -/
theorem BinderReadyShadowJoinEnvRelated.consBothOfKeys
    (keyEq : sourceKey = targetKey)
    (declaration :
      BinderReadyShadowFunDeclRelated fuel used
        sourceDeclaration targetDeclaration)
    (rest :
      BinderReadyShadowJoinEnvRelated fuel used sourceJoins targetJoins) :
    BinderReadyShadowJoinEnvRelated fuel used
      ((sourceKey, sourceDeclaration) :: sourceJoins)
      ((targetKey, targetDeclaration) :: targetJoins) := by
  subst targetKey
  exact rest.consBoth declaration

/-- Installing a source-only dead join preserves all observable lookups. -/
theorem BinderReadyShadowJoinEnvRelated.consSourceOfAbsent
    (absent : used.contains key = false)
    (rest :
      BinderReadyShadowJoinEnvRelated fuel used sourceJoins targetJoins) :
    BinderReadyShadowJoinEnvRelated fuel used
      ((key, sourceDeclaration) :: sourceJoins) targetJoins := by
  intro target member
  have different : key.name ≠ target.name :=
    fvarId_name_ne_of_contains_of_absent used target key member absent
  have sameName : (key.name == target.name) = false := by
    simp [different]
  simpa [findJoinPoint?, sameName] using rest target member

/-- A successful source declaration lookup returns the corresponding target
declaration together with its hereditary body relation. -/
theorem binderReadyShadowProgram_findDecl_of_some
    (programs :
      ProgramRelated (BinderReadyShadowCodeRelated fuel) source target)
    (sourceFound : source.findDecl? name = some sourceDeclaration) :
    ∃ targetDeclaration,
      target.findDecl? name = some targetDeclaration ∧
        DeclRelated (BinderReadyShadowCodeRelated fuel)
          sourceDeclaration targetDeclaration := by
  have found := programs.findDecl? name
  rw [sourceFound] at found
  generalize targetFound :
      target.findDecl? name = targetResult at found
  cases found with
  | some declaration =>
      exact ⟨_, rfl, declaration⟩

/-- A successful live source join lookup returns the corresponding target
join and its hereditary body graph. -/
theorem BinderReadyShadowJoinEnvRelated.find_of_some
    (related :
      BinderReadyShadowJoinEnvRelated fuel used source target)
    (member : used.contains key = true)
    (sourceFound :
      findJoinPoint? source key = some sourceDeclaration) :
    ∃ targetDeclaration,
      findJoinPoint? target key = some targetDeclaration ∧
        BinderReadyShadowFunDeclRelated fuel used
          sourceDeclaration targetDeclaration := by
  have found := related key member
  rw [sourceFound] at found
  generalize targetFound :
      findJoinPoint? target key = targetResult at found
  cases found with
  | some declaration =>
      exact ⟨_, rfl, declaration⟩

/-- A full-fuel exact certificate embeds into the bounded runtime relation
with reflexive fuel and liveness widenings. -/
theorem BinderReadyExactShadowCodeRelated.toBinderReadyShadowCodeRelated
    (related : BinderReadyExactShadowCodeRelated fuel source target) :
    BinderReadyShadowCodeRelated fuel source target := by
  rcases related with ⟨final, exact, static⟩
  exact ⟨final, fuel, final, Nat.le_refl fuel, exact,
    UsedSubset.refl final, static⟩

/-- Erase bounded hereditary provenance inside one declaration value. -/
theorem forgetBinderReadyShadowDeclValue
    (related :
      DeclValueRelated (BinderReadyShadowCodeRelated fuel) source target) :
    DeclValueRelated (ShadowCodeRelated fuel) source target := by
  cases related with
  | code body => exact .code body.toShadowCodeRelated
  | extern metadata => exact .extern metadata

/-- Lift exact-to-bounded embedding through one declaration value. -/
theorem binderReadyExactShadowDeclValue_toBinderReadyShadow
    (related :
      DeclValueRelated
        (BinderReadyExactShadowCodeRelated fuel) source target) :
    DeclValueRelated
      (BinderReadyShadowCodeRelated fuel) source target := by
  cases related with
  | code body =>
      exact .code body.toBinderReadyShadowCodeRelated
  | extern metadata => exact .extern metadata

/-- Erase bounded hereditary program provenance pointwise. -/
theorem forgetBinderReadyShadowProgram
    (related :
      ProgramRelated (BinderReadyShadowCodeRelated fuel) source target) :
    ProgramRelated (ShadowCodeRelated fuel) source target := by
  apply listRel_mono (related := related)
  intro left right declaration
  exact {
    name_eq := declaration.name_eq
    levelParams_eq := declaration.levelParams_eq
    type_eq := declaration.type_eq
    params_eq := declaration.params_eq
    safe_eq := declaration.safe_eq
    value := forgetBinderReadyShadowDeclValue declaration.value
    recursive_eq := declaration.recursive_eq
    inlineAttr_eq := declaration.inlineAttr_eq
  }

/-- Embed exact hereditary program provenance into the bounded relation used
by all future runtime code locations. -/
theorem binderReadyExactShadowProgram_toBinderReadyShadow
    (related :
      ProgramRelated
        (BinderReadyExactShadowCodeRelated fuel) source target) :
    ProgramRelated (BinderReadyShadowCodeRelated fuel) source target := by
  apply listRel_mono (related := related)
  intro left right declaration
  exact {
    name_eq := declaration.name_eq
    levelParams_eq := declaration.levelParams_eq
    type_eq := declaration.type_eq
    params_eq := declaration.params_eq
    safe_eq := declaration.safe_eq
    value :=
      binderReadyExactShadowDeclValue_toBinderReadyShadow declaration.value
    recursive_eq := declaration.recursive_eq
    inlineAttr_eq := declaration.inlineAttr_eq
  }

/-- Successful checked compiler run in the bounded hereditary relation. -/
theorem shadowProgram_binderReadyShadowRelated
    (wellFormed : ProgramElimDeadWellFormed source)
    (result : shadowProgram? fuel source = some target) :
    ProgramRelated
      (BinderReadyShadowCodeRelated fuel) source target :=
  binderReadyExactShadowProgram_toBinderReadyShadow
    (shadowProgram_binderReadyExactRelated wellFormed result)

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
