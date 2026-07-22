import Fir.LeanIR.Passes.ElimDeadRelation
import Fir.LeanIR.Passes.Structural

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.NonLockstep.Structural

/-!
The declaration/program graph for the transparent `elimDeadVars` shadow.

This layer records only what the traversal produced.  Semantic admissibility
of an eliminated operation remains a separate phase premise: in particular,
the existing raw-observation contract cannot validate dead allocations whose
unreachable heap cells remain visible.
-/

/-- One residual edge in the transparent traversal graph.  Its output used
set is an explicit index because execution needs precisely that set for
environment agreement and installed-join coverage. -/
def ShadowCodeGraph (fuel : Nat) (used : UsedLocals)
    (source target : LCNF.Code .impure) : Prop :=
  ∃ remaining initial final, remaining ≤ fuel ∧
    shadowCode? remaining initial source = some (target, final) ∧
    UsedSubset final used

/-- Existential presentation used by structural declarations and programs.
Active controls and saved frames expose the hidden used set again. -/
def ShadowCodeRelated (fuel : Nat)
    (source target : LCNF.Code .impure) : Prop :=
  ∃ used, ShadowCodeGraph fuel used source target

theorem ShadowCodeGraph.covered
    (graph : ShadowCodeGraph fuel used source target) :
    CodeCovered used target := by
  rcases graph with ⟨remaining, initial, final, bounded, result, subset⟩
  exact (shadowCode_spec result).1.mono subset

theorem ShadowCodeGraph.initialSubset
    (graph : ShadowCodeGraph fuel used source target) :
    ∃ initial, UsedSubset initial used := by
  rcases graph with ⟨remaining, initial, final, bounded, result, subset⟩
  exact ⟨initial, (shadowCode_spec result).2.trans subset⟩

theorem ShadowCodeGraph.mono
    (subset : UsedSubset used larger)
    (graph : ShadowCodeGraph fuel used source target) :
    ShadowCodeGraph fuel larger source target := by
  rcases graph with ⟨remaining, initial, final, bounded, result, coveredBy⟩
  exact ⟨remaining, initial, final, bounded, result, coveredBy.trans subset⟩

theorem ShadowCodeGraph.jumpTarget
    (graph : ShadowCodeGraph fuel used (.jmp join arguments) target) :
    target = .jmp join arguments := by
  rcases graph with ⟨remaining, initial, final, bounded, result, subset⟩
  cases remaining <;> simp [shadowCode?] at result <;> exact result.1.symm

theorem ShadowCodeGraph.returnTarget
    (graph : ShadowCodeGraph fuel used (.return value) target) :
    target = .return value := by
  rcases graph with ⟨remaining, initial, final, bounded, result, subset⟩
  cases remaining <;> simp [shadowCode?] at result <;> exact result.1.symm

theorem ShadowCodeGraph.unreachTarget
    (graph : ShadowCodeGraph fuel used (.unreach type) target) :
    target = .unreach type := by
  rcases graph with ⟨remaining, initial, final, bounded, result, subset⟩
  cases remaining <;> simp [shadowCode?] at result <;> exact result.1.symm

/-- The two residual shapes produced when the source graph starts with a let:
the declaration is retained on both sides, or it is absent from the target
and only the recursively transformed continuation remains. -/
inductive ShadowLetResidual (fuel : Nat) (used : UsedLocals)
    (declaration : LCNF.LetDecl .impure)
    (sourceContinuation : LCNF.Code .impure) :
    LCNF.Code .impure → Prop where
  | retained (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (covered : LetValueCovered used declaration.value) :
      ShadowLetResidual fuel used declaration sourceContinuation
        (.let declaration targetContinuation)
  | deleted (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation) :
      ShadowLetResidual fuel used declaration sourceContinuation
        targetContinuation

/-- Inversion of a transparent shadow edge at a let node.  This theorem is
purely syntactic; the deleted branch deliberately leaves runtime neutrality
and scope-sensitive absence to the execution readiness invariant. -/
theorem ShadowCodeGraph.letResidual
    (graph : ShadowCodeGraph fuel used
      (.let declaration sourceContinuation) target) :
    ShadowLetResidual fuel used declaration sourceContinuation target := by
  rcases graph with ⟨remaining, initial, final, bounded, result, subset⟩
  cases remaining with
  | zero => simp [shadowCode?] at result
  | succ nextFuel =>
      cases continuationResult :
          shadowCode? nextFuel initial sourceContinuation with
      | none => simp [shadowCode?, continuationResult] at result
      | some output =>
          obtain ⟨targetContinuation, continuationUsed⟩ := output
          have continuationBound : nextFuel ≤ fuel :=
            Nat.le_trans (Nat.le_succ nextFuel) bounded
          by_cases keep :
              declaration.fvarId ∈ continuationUsed ∨
                safeToElim declaration.value = false
          · simp [shadowCode?, continuationResult, keep] at result
            rcases result with ⟨rfl, rfl⟩
            apply ShadowLetResidual.retained targetContinuation
            · exact ⟨nextFuel, initial, continuationUsed,
                continuationBound, continuationResult,
                (collectLetValue_subset continuationUsed
                  declaration.value).trans subset⟩
            · exact (collectLetValue_covers continuationUsed
                declaration.value).mono subset
          · simp [shadowCode?, continuationResult, keep] at result
            rcases result with ⟨rfl, rfl⟩
            exact .deleted targetContinuation ⟨nextFuel, initial,
              continuationUsed, continuationBound, continuationResult, subset⟩

/-- Semantic readiness is indexed by the actual residual edge.  Retained lets
need no extra premise.  Deleted lets must be runtime-neutral for the current
state, and their binder must remain absent from the enlarged active liveness
index.  The latter is the precise scoping fact needed when enclosing join
bodies enlarge that index. -/
inductive ShadowLetReadyAt (fuel : Nat) (used : UsedLocals)
    (declaration : LCNF.LetDecl .impure)
    (sourceContinuation : LCNF.Code .impure) (state : MachineState) :
    {target : LCNF.Code .impure} →
      ShadowLetResidual fuel used declaration sourceContinuation target →
        Prop where
  | retained (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (covered : LetValueCovered used declaration.value) :
      ShadowLetReadyAt fuel used declaration sourceContinuation state
        (.retained targetContinuation continuation covered)
  | deleted (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (absent : used.contains declaration.fvarId = false)
      (neutral : RuntimeNeutralAt state declaration) :
      ShadowLetReadyAt fuel used declaration sourceContinuation state
        (.deleted targetContinuation continuation)

/-- Case alternatives keep their tag/default metadata and relate only their
recursively transformed code bodies. -/
inductive ShadowAltRelated (fuel : Nat) (used : UsedLocals) :
    LCNF.Alt .impure → LCNF.Alt .impure → Prop where
  | ctor (info : LCNF.CtorInfo)
      (body : ShadowCodeGraph fuel used sourceBody targetBody) :
      ShadowAltRelated fuel used
        (.ctorAlt info sourceBody) (.ctorAlt info targetBody)
  | default
      (body : ShadowCodeGraph fuel used sourceBody targetBody) :
      ShadowAltRelated fuel used
        (.default sourceBody) (.default targetBody)

def ShadowAltListRelated (fuel : Nat) (used : UsedLocals)
    (source target : List (LCNF.Alt .impure)) : Prop :=
  ListRel (ShadowAltRelated fuel used) source target

/-- The alternative traversal produces pointwise-related bodies under any
larger active liveness index that contains its final threaded set. -/
theorem shadowAltList_related
    (result : shadowAltList? (shadowCode? remaining) initial source =
      some (target, final))
    (bounded : remaining ≤ fuel)
    (subset : UsedSubset final used) :
    ShadowAltListRelated fuel used source target := by
  induction source generalizing initial target final with
  | nil =>
      simp only [shadowAltList?] at result
      rcases result with ⟨rfl, rfl⟩
      exact .nil
  | cons alternative rest ih =>
      cases bodyResult :
          shadowCode? remaining initial alternative.getCode with
      | none => simp [shadowAltList?, bodyResult] at result
      | some bodyOutput =>
          obtain ⟨targetBody, middle⟩ := bodyOutput
          cases restResult :
              shadowAltList? (shadowCode? remaining) middle rest with
          | none => simp [shadowAltList?, bodyResult, restResult] at result
          | some restOutput =>
              obtain ⟨targetRest, threadedFinal⟩ := restOutput
              simp [shadowAltList?, bodyResult, restResult] at result
              rcases result with ⟨rfl, rfl⟩
              have restSpec := shadowAltList_spec
                (transformCode := shadowCode? remaining)
                (transformSpec := fun _ _ _ _ bodyRun =>
                  shadowCode_spec bodyRun)
                (result := restResult)
              have bodyGraph : ShadowCodeGraph fuel used
                  alternative.getCode targetBody :=
                ⟨remaining, initial, middle, bounded, bodyResult,
                  restSpec.2.trans subset⟩
              have headRelated : ShadowAltRelated fuel used alternative
                  (updateAltCode alternative targetBody) := by
                cases alternative with
                | ctorAlt info body => exact .ctor info bodyGraph
                | default body => exact .default bodyGraph
                | alt _ _ _ impossible => nomatch impossible
              exact .cons headRelated (ih restResult subset)

theorem ShadowAltListRelated.findCtor
    (related : ShadowAltListRelated fuel used source target) :
    OptionalRel (ShadowCodeGraph fuel used)
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

theorem ShadowAltListRelated.findDefault
    (related : ShadowAltListRelated fuel used source target) :
    OptionalRel (ShadowCodeGraph fuel used)
      (findDefaultAlt source) (findDefaultAlt target) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      cases head with
      | ctor info body => simpa [findDefaultAlt] using ih
      | default body =>
          simpa [findDefaultAlt] using OptionalRel.some body

theorem ShadowAltListRelated.choose
    (related : ShadowAltListRelated fuel used source target) :
    OptionalRel (ShadowCodeGraph fuel used)
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

/-- Inversion of a transparent shadow edge at a case table.  Discriminant and
case metadata remain exact, while every alternative body retains a residual
graph under the final active liveness index. -/
theorem ShadowCodeGraph.casesResidual
    (graph : ShadowCodeGraph fuel used
      (.cases (.mk typeName resultType discr sourceAlternatives)) target) :
    ∃ targetAlternatives,
      target = .cases (.mk typeName resultType discr targetAlternatives) ∧
      ShadowAltListRelated fuel used sourceAlternatives.toList
        targetAlternatives.toList ∧
      used.contains discr = true := by
  rcases graph with ⟨remaining, initial, final, bounded, result, subset⟩
  cases remaining with
  | zero => simp [shadowCode?] at result
  | succ nextFuel =>
      cases alternativesResult : shadowAltList? (shadowCode? nextFuel)
          initial sourceAlternatives.toList with
      | none => simp [shadowCode?, alternativesResult] at result
      | some output =>
          obtain ⟨targetAlternatives, beforeDiscr⟩ := output
          simp [shadowCode?, alternativesResult] at result
          rcases result with ⟨rfl, rfl⟩
          have continuationBound : nextFuel ≤ fuel :=
            Nat.le_trans (Nat.le_succ nextFuel) bounded
          have beforeSubset : UsedSubset beforeDiscr used :=
            (usedSubset_insert beforeDiscr discr).trans subset
          refine ⟨targetAlternatives.toArray, rfl, ?_, subset discr (by simp)⟩
          simpa using shadowAltList_related alternativesResult
            continuationBound beforeSubset

/-- Every target body in the program graph carries the liveness coverage
proved for the transparent traversal. -/
theorem ShadowCodeRelated.covered
    (related : ShadowCodeRelated fuel source target) :
    ∃ final, CodeCovered final target := by
  rcases related with ⟨used, graph⟩
  exact ⟨used, graph.covered⟩

/-- A successful declaration traversal preserves all declaration metadata and
either keeps identical external metadata or relates the two internal bodies. -/
theorem shadowDecl_related
    (result : shadowDecl? fuel source = some target) :
    DeclRelated (ShadowCodeRelated fuel) source target := by
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
              exact .code ⟨final, fuel, {}, final, Nat.le_refl fuel,
                transformed, .refl final⟩
            recursive_eq := rfl
            inlineAttr_eq := rfl
          }

/-- The declaration-list traversal is pointwise related for lists of arbitrary
length. -/
theorem shadowDecls_related
    (result : shadowDecls? fuel sources = some targets) :
    ListRel (DeclRelated (ShadowCodeRelated fuel)) sources targets := by
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
              exact .cons (shadowDecl_related headResult) (ih tailResult)

/-- A successful whole-program shadow traversal preserves ordered declaration
lookup and relates every internal body produced by the same fuel bound. -/
theorem shadowProgram_related
    (result : shadowProgram? fuel source = some target) :
    ProgramRelated (ShadowCodeRelated fuel) source target := by
  cases declarationsResult : shadowDecls? fuel source.decls.toList with
  | none => simp [shadowProgram?, declarationsResult] at result
  | some declarations =>
      simp [shadowProgram?, declarationsResult] at result
      subst target
      unfold ProgramRelated
      simpa using shadowDecls_related declarationsResult

/-- Covered let-value evaluation is insensitive to transformed declaration
bodies.  Partial application is the only program-sensitive form; pointwise
program relatedness supplies its equal parameter arity. -/
theorem evalLetValue_shadowRelated
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      source.program target.program)
    (runtimeEq : source.runtime = target.runtime)
    (agree : EnvsAgreeOn used source.env target.env)
    (covered : LetValueCovered used declaration.value) :
    evalLetValue source declaration = evalLetValue target declaration := by
  cases declaration with
  | mk fvarId binderName type value =>
      cases value with
      | lit literal | erased =>
          simp only [evalLetValue]
          rw [runtimeEq]
      | fvar function arguments =>
          simp only [evalLetValue]
          rw [agree function covered.1]
          rw [evalArgs_eq_of_covered agree covered.2]
          rw [runtimeEq]
      | ctor info arguments =>
          simp only [evalLetValue]
          rw [evalArgs_eq_of_covered agree covered]
          rw [runtimeEq]
      | oproj index object | uproj index object | sproj index offset object
      | reset index object | box type object | unbox object | isShared object =>
          simp only [evalLetValue]
          rw [agree object covered]
          rw [runtimeEq]
      | fap name arguments =>
          simp only [evalLetValue]
          rw [evalArgs_eq_of_covered agree covered]
          rw [runtimeEq]
      | pap name arguments =>
          simp only [evalLetValue]
          rw [evalArgs_eq_of_covered agree covered]
          generalize argumentsRead : evalArgs target.env arguments = result
          cases result with
          | error fault => rfl
          | ok values =>
              have found := programs.findDecl? name
              generalize sourceFound :
                source.program.findDecl? name = sourceDeclaration at found ⊢
              generalize targetFound :
                target.program.findDecl? name = targetDeclaration at found ⊢
              cases found with
              | none => rfl
              | some declarations =>
                  dsimp
                  rw [declarations.params_eq, runtimeEq]
      | reuse token info updateHeader arguments =>
          simp only [evalLetValue]
          rw [agree token covered.1]
          rw [evalArgs_eq_of_covered agree covered.2]
          rw [runtimeEq]
      | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible

/-! ## Program-aware liveness relation -/

/-- Join declarations preserve their binder and ABI while their bodies retain
the active liveness index. -/
structure ShadowFunDeclRelated (fuel : Nat) (used : UsedLocals)
    (source target : LCNF.FunDecl .impure) : Prop where
  fvarId_eq : source.fvarId = target.fvarId
  binderName_eq : source.binderName = target.binderName
  params_eq : source.params = target.params
  type_eq : source.type = target.type
  value : ShadowCodeGraph fuel used source.value target.value

/-- Extensional join lookup relation.  Only identifiers covered by the active
used set can be observed by a jump, which permits source-only entries created
by executing join declarations deleted from the target. -/
def ShadowJoinEnvRelated (fuel : Nat) (used : UsedLocals)
    (source target : JoinEnv) : Prop :=
  ∀ key, used.contains key = true →
    OptionalRel (ShadowFunDeclRelated fuel used)
      (findJoinPoint? source key) (findJoinPoint? target key)

theorem ShadowJoinEnvRelated.empty (fuel : Nat) (used : UsedLocals) :
    ShadowJoinEnvRelated fuel used [] [] := by
  intro key member
  exact .none

theorem ShadowJoinEnvRelated.consBoth
    (declaration : ShadowFunDeclRelated fuel used sourceDeclaration
      targetDeclaration)
    (rest : ShadowJoinEnvRelated fuel used sourceJoins targetJoins) :
    ShadowJoinEnvRelated fuel used
      ((key, sourceDeclaration) :: sourceJoins)
      ((key, targetDeclaration) :: targetJoins) := by
  intro target member
  by_cases sameName : key.name == target.name
  · simpa [findJoinPoint?, sameName] using
      (OptionalRel.some declaration)
  · simpa [findJoinPoint?, sameName] using rest target member

theorem ShadowJoinEnvRelated.consBothOfKeys
    (keyEq : sourceKey = targetKey)
    (declaration : ShadowFunDeclRelated fuel used sourceDeclaration
      targetDeclaration)
    (rest : ShadowJoinEnvRelated fuel used sourceJoins targetJoins) :
    ShadowJoinEnvRelated fuel used
      ((sourceKey, sourceDeclaration) :: sourceJoins)
      ((targetKey, targetDeclaration) :: targetJoins) := by
  subst targetKey
  exact rest.consBoth declaration

theorem ShadowJoinEnvRelated.consSourceOfAbsent
    (absent : used.contains key = false)
    (rest : ShadowJoinEnvRelated fuel used sourceJoins targetJoins) :
    ShadowJoinEnvRelated fuel used
      ((key, sourceDeclaration) :: sourceJoins) targetJoins := by
  intro target member
  have different : key.name ≠ target.name :=
    fvarId_name_ne_of_contains_of_absent used target key member absent
  have sameName : (key.name == target.name) = false := by
    simp [different]
  simpa [findJoinPoint?, sameName] using rest target member

/-- The two residual shapes produced when the source graph starts with a join:
retained declarations have related recursively transformed bodies, while a
dead declaration disappears and leaves only its transformed continuation. -/
inductive ShadowJoinResidual (fuel : Nat) (used : UsedLocals)
    (sourceDeclaration : LCNF.FunDecl .impure)
    (sourceContinuation : LCNF.Code .impure) :
    LCNF.Code .impure → Prop where
  | retained (targetDeclaration : LCNF.FunDecl .impure)
      (targetContinuation : LCNF.Code .impure)
      (declaration : ShadowFunDeclRelated fuel used
        sourceDeclaration targetDeclaration)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation) :
      ShadowJoinResidual fuel used sourceDeclaration sourceContinuation
        (.jp targetDeclaration targetContinuation)
  | deleted (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation) :
      ShadowJoinResidual fuel used sourceDeclaration sourceContinuation
        targetContinuation

/-- Inversion of a transparent shadow edge at a join declaration. -/
theorem ShadowCodeGraph.joinResidual
    (graph : ShadowCodeGraph fuel used
      (.jp sourceDeclaration sourceContinuation) target) :
    ShadowJoinResidual fuel used sourceDeclaration sourceContinuation target := by
  cases sourceDeclaration with
  | mk fvarId binderName params type body =>
      rcases graph with ⟨remaining, initial, final, bounded, result, subset⟩
      cases remaining with
      | zero => simp [shadowCode?] at result
      | succ nextFuel =>
          cases continuationResult :
              shadowCode? nextFuel initial sourceContinuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some output =>
              obtain ⟨targetContinuation, continuationUsed⟩ := output
              have continuationBound : nextFuel ≤ fuel :=
                Nat.le_trans (Nat.le_succ nextFuel) bounded
              by_cases keep : fvarId ∈ continuationUsed
              · cases bodyResult :
                    shadowCode? nextFuel continuationUsed body with
                | none =>
                    simp [shadowCode?, continuationResult, keep, bodyResult]
                      at result
                | some output =>
                    obtain ⟨targetBody, bodyUsed⟩ := output
                    simp [shadowCode?, continuationResult, keep, bodyResult]
                      at result
                    rcases result with ⟨rfl, rfl⟩
                    have bodySpec := shadowCode_spec bodyResult
                    apply ShadowJoinResidual.retained
                      (.mk fvarId binderName params type targetBody)
                      targetContinuation
                    · exact {
                        fvarId_eq := rfl
                        binderName_eq := rfl
                        params_eq := rfl
                        type_eq := rfl
                        value := ⟨nextFuel, continuationUsed, bodyUsed,
                          continuationBound, bodyResult, subset⟩
                      }
                    · exact ⟨nextFuel, initial, continuationUsed,
                        continuationBound, continuationResult,
                        bodySpec.2.trans subset⟩
              · simp [shadowCode?, continuationResult, keep] at result
                rcases result with ⟨rfl, rfl⟩
                exact .deleted targetContinuation ⟨nextFuel, initial,
                  continuationUsed, continuationBound, continuationResult,
                  subset⟩

/-- Join readiness is again indexed by the concrete residual edge.  Retained
joins are unconditional; a deleted source-only entry must be absent from the
active liveness index so no related target jump can observe it. -/
inductive ShadowJoinReadyAt (fuel : Nat) (used : UsedLocals)
    (sourceDeclaration : LCNF.FunDecl .impure)
    (sourceContinuation : LCNF.Code .impure) :
    {target : LCNF.Code .impure} →
      ShadowJoinResidual fuel used sourceDeclaration sourceContinuation target →
        Prop where
  | retained (targetDeclaration : LCNF.FunDecl .impure)
      (targetContinuation : LCNF.Code .impure)
      (declaration : ShadowFunDeclRelated fuel used
        sourceDeclaration targetDeclaration)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation) :
      ShadowJoinReadyAt fuel used sourceDeclaration sourceContinuation
        (.retained targetDeclaration targetContinuation declaration
          continuation)
  | deleted (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (absent : used.contains sourceDeclaration.fvarId = false) :
      ShadowJoinReadyAt fuel used sourceDeclaration sourceContinuation
        (.deleted targetContinuation continuation)

/-- The currently certified exact-runtime fragment of the shadow graph.
Heap-effect nodes are intentionally absent until the runtime relation is
weakened from raw equality to reachable-heap equivalence. -/
inductive ShadowCodeReadyAt (fuel : Nat) (used : UsedLocals)
    (state : MachineState) :
    {source target : LCNF.Code .impure} →
      ShadowCodeGraph fuel used source target → Prop where
  | letE
      (graph : ShadowCodeGraph fuel used
        (.let declaration sourceContinuation) target)
      (ready : ShadowLetReadyAt fuel used declaration sourceContinuation
        state graph.letResidual) :
      ShadowCodeReadyAt fuel used state graph
  | join
      (graph : ShadowCodeGraph fuel used
        (.jp declaration sourceContinuation) target)
      (ready : ShadowJoinReadyAt fuel used declaration sourceContinuation
        graph.joinResidual) :
      ShadowCodeReadyAt fuel used state graph
  | cases
      (graph : ShadowCodeGraph fuel used
        (.cases caseInfo) target) :
      ShadowCodeReadyAt fuel used state graph
  | jump
      (graph : ShadowCodeGraph fuel used (.jmp join arguments) target) :
      ShadowCodeReadyAt fuel used state graph
  | ret
      (graph : ShadowCodeGraph fuel used (.return value) target) :
      ShadowCodeReadyAt fuel used state graph
  | unreachable
      (graph : ShadowCodeGraph fuel used (.unreach type) target) :
      ShadowCodeReadyAt fuel used state graph

/-- Readiness for an arbitrary control override.  Only code controls impose an
obligation, and they impose it on the exact graph carried by the structural
control relation. -/
def ShadowControlReadyAt (fuel : Nat) (sourceState : MachineState)
    (sourceControl targetControl : Control) : Prop :=
  ∀ {used sourceCode targetCode},
    sourceControl = .code sourceCode →
    targetControl = .code targetCode →
    (graph : ShadowCodeGraph fuel used sourceCode targetCode) →
      ShadowCodeReadyAt fuel used sourceState graph

/-- A saved call continuation retains its residual shadow edge, captured
environment agreement, and the transformed join graph it will resume with.
Apply and cache frames remain exact. -/
inductive ShadowFrameRelated (fuel : Nat) : Frame → Frame → Prop where
  | bind
      (graph : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (joins : ShadowJoinEnvRelated fuel used sourceJoins targetJoins)
      (agree : EnvsAgreeOn used sourceEnv targetEnv) :
      ShadowFrameRelated fuel
        (.bind fvarId sourceContinuation sourceEnv sourceJoins)
        (.bind fvarId targetContinuation targetEnv targetJoins)
  | apply (arguments : Array Value) :
      ShadowFrameRelated fuel (.apply arguments) (.apply arguments)
  | cache (name : Name) :
      ShadowFrameRelated fuel (.cache name) (.cache name)

def ShadowFramesRelated (fuel : Nat) (source target : List Frame) : Prop :=
  ListRel (ShadowFrameRelated fuel) source target

theorem ShadowFramesRelated.prepareCall
    (name : Name) (params : Array (LCNF.Param .impure))
    (arguments extraArguments : Array Value)
    (related : ShadowFramesRelated fuel sourceFrames targetFrames) :
    ShadowFramesRelated fuel
      (let frames := if extraArguments.isEmpty then sourceFrames
        else .apply extraArguments :: sourceFrames
       if params.isEmpty && arguments.isEmpty then .cache name :: frames
       else frames)
      (let frames := if extraArguments.isEmpty then targetFrames
        else .apply extraArguments :: targetFrames
       if params.isEmpty && arguments.isEmpty then .cache name :: frames
       else frames) := by
  unfold ShadowFramesRelated at related ⊢
  by_cases extraEmpty : extraArguments.isEmpty
  · by_cases cache : params.isEmpty && arguments.isEmpty
    · simpa [extraEmpty, cache] using
        ListRel.cons (ShadowFrameRelated.cache name) related
    · simpa [extraEmpty, cache] using related
  · by_cases cache : params.isEmpty && arguments.isEmpty
    · simpa [extraEmpty, cache] using
        ListRel.cons (ShadowFrameRelated.cache name)
          (ListRel.cons (ShadowFrameRelated.apply extraArguments) related)
    · simpa [extraEmpty, cache] using
        ListRel.cons (ShadowFrameRelated.apply extraArguments) related

/-- Active controls combine the recursive syntax graph with the liveness
invariant.  Environments and joins are deliberately irrelevant while a value
or invocation is in flight; all resumable lexical data lives in frames. -/
inductive ShadowControlRelated (fuel : Nat) :
    Env → JoinEnv → Control → Env → JoinEnv → Control → Prop where
  | code
      (graph : ShadowCodeGraph fuel used sourceCode targetCode)
      (joins : ShadowJoinEnvRelated fuel used sourceJoins targetJoins)
      (agree : EnvsAgreeOn used sourceEnv targetEnv) :
      ShadowControlRelated fuel
        sourceEnv sourceJoins (.code sourceCode)
        targetEnv targetJoins (.code targetCode)
  | yielded (value : Value) :
      ShadowControlRelated fuel
        sourceEnv sourceJoins (.yielded value)
        targetEnv targetJoins (.yielded value)
  | invokeName (name : Name) (arguments : Array Value) :
      ShadowControlRelated fuel
        sourceEnv sourceJoins (.invokeName name arguments)
        targetEnv targetJoins (.invokeName name arguments)
  | invokeValue (function : Value) (arguments : Array Value) :
      ShadowControlRelated fuel
        sourceEnv sourceJoins (.invokeValue function arguments)
        targetEnv targetJoins (.invokeValue function arguments)

/-- Declaration entry resets both lexical contexts.  Related controls can be
reindexed at that common empty-join environment without losing their graph. -/
theorem ShadowControlRelated.exactAt
    (related : ShadowControlRelated fuel
      sourceEnv sourceJoins sourceControl
      targetEnv targetJoins targetControl)
    (env : Env) :
    ShadowControlRelated fuel env [] sourceControl env [] targetControl := by
  cases related with
  | code graph joins agree =>
      exact .code graph (.empty fuel _) (.refl _ env)
  | yielded value => exact .yielded value
  | invokeName name arguments => exact .invokeName name arguments
  | invokeValue function arguments => exact .invokeValue function arguments

/-- Machines may execute different residual programs and carry environments
that differ on dead binders, but they share runtime data and preserve every
code-bearing location through the bounded shadow graph. -/
structure ShadowMachineRelated (fuel : Nat)
    (source target : MachineState) : Prop where
  programs : ProgramRelated (ShadowCodeRelated fuel)
    source.program target.program
  runtime_eq : source.runtime = target.runtime
  frames : ShadowFramesRelated fuel source.frames target.frames
  control : ShadowControlRelated fuel
    source.env source.joins source.control
    target.env target.joins target.control

/-- Core results preserve the program-aware shadow relation.  External
requests and terminal observations are exact because both are observable. -/
inductive ShadowCoreResultRelated (fuel : Nat) :
    CoreResult → CoreResult → Prop where
  | next (related : ShadowMachineRelated fuel source target) :
      ShadowCoreResultRelated fuel (.next source) (.next target)
  | external (request : ExternalRequest)
      (related : ShadowMachineRelated fuel source target) :
      ShadowCoreResultRelated fuel
        (.external request source) (.external request target)
  | done (observation : Observation) :
      ShadowCoreResultRelated fuel (.done observation) (.done observation)

/-- One related machine pair either advances with related core results or
performs one source-only step removed by the target program. -/
inductive ShadowMachineProgress (fuel : Nat)
    (source target : MachineState) : Prop where
  | lockstep
      (results : ShadowCoreResultRelated fuel
        (coreStep source) (coreStep target)) :
      ShadowMachineProgress fuel source target
  | sourceOnly (sourceAfter : MachineState)
      (transition : coreStep source = .next sourceAfter)
      (related : ShadowMachineRelated fuel sourceAfter target) :
      ShadowMachineProgress fuel source target

theorem ShadowCoreResultRelated.done_right
    (related : ShadowCoreResultRelated fuel (.done observation) target) :
    target = .done observation := by
  cases related
  rfl

theorem shadowFail_related
    (runtimeEq : source.runtime = target.runtime)
    (fault : RuntimeFault) :
    ShadowCoreResultRelated fuel (fail source fault) (fail target fault) := by
  unfold fail
  rw [observe_eq_of_runtime_eq_live runtimeEq]
  exact .done _

/-- A retained let evaluates identically on both sides.  Ordinary values bind
on both sides, while calls save recursively related continuations in the two
frame stacks. -/
theorem coreStep_retainedLet_shadowRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env)
    (covered : LetValueCovered used declaration.value) :
    ShadowCoreResultRelated fuel
      (coreStep { sourceState with
        control := .code (.let declaration sourceContinuation) })
      (coreStep { targetState with
        control := .code (.let declaration targetContinuation) }) := by
  let sourceCurrent := { sourceState with
    control := .code (.let declaration sourceContinuation) }
  let targetCurrent := { targetState with
    control := .code (.let declaration targetContinuation) }
  have evaluationEq :
      evalLetValue sourceCurrent declaration =
        evalLetValue targetCurrent declaration :=
    evalLetValue_shadowRelated programs runtimeEq agree covered
  simp only [coreStep]
  rw [evaluationEq]
  generalize evaluated : evalLetValue targetCurrent declaration = result
  cases result with
  | error fault => exact shadowFail_related runtimeEq fault
  | ok result =>
      rcases result with ⟨nextRuntime, action⟩
      cases action with
      | value value =>
          exact .next {
            programs
            runtime_eq := rfl
            frames := framesRelated
            control := .code continuation joins agree.bindBoth
          }
      | invokeName name arguments =>
          exact .next {
            programs
            runtime_eq := rfl
            frames := .cons (.bind continuation joins agree) framesRelated
            control := .invokeName name arguments
          }
      | invokeValue function arguments =>
          exact .next {
            programs
            runtime_eq := rfl
            frames := .cons (.bind continuation joins agree) framesRelated
            control := .invokeValue function arguments
          }

/-- The semantic source-only rule for a deleted let.  Runtime neutrality
accounts for raw observations, while absence from the active liveness index
permits the source's extra environment binding. -/
theorem coreStep_deletedLet_shadowProgress
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env)
    (absent : used.contains declaration.fvarId = false)
    (evaluated : evalLetValue sourceState declaration =
      .ok (sourceState.runtime, .value value)) :
    ShadowMachineProgress fuel
      { sourceState with
        control := .code (.let declaration sourceContinuation) }
      { targetState with control := .code targetContinuation } := by
  let sourceAfter :=
    { sourceState with
      env := bind sourceState.env declaration.fvarId value
      control := .code sourceContinuation }
  apply ShadowMachineProgress.sourceOnly sourceAfter
  · exact coreStep_runtimeNeutralLet evaluated
  · exact {
      programs
      runtime_eq := runtimeEq
      frames := framesRelated
      control := .code continuation joins
        (agree.bindLeft_of_absent absent)
    }

/-- Complete one-node progress theorem for a source let edge in the
transparent graph.  Inversion chooses lockstep retained execution or the
single source step justified by `ShadowLetReadyAt`. -/
theorem coreStep_let_shadowProgress
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (graph : ShadowCodeGraph fuel used
      (.let declaration sourceContinuation) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env)
    (ready : ShadowLetReadyAt fuel used declaration sourceContinuation
      sourceState graph.letResidual) :
    ShadowMachineProgress fuel
      { sourceState with
        control := .code (.let declaration sourceContinuation) }
      { targetState with control := .code targetCode } := by
  cases ready with
  | retained targetContinuation continuation covered =>
      apply ShadowMachineProgress.lockstep
      exact coreStep_retainedLet_shadowRelated sourceState targetState
        programs runtimeEq framesRelated continuation joins agree covered
  | deleted targetContinuation continuation absent neutral =>
      rcases neutral with ⟨value, evaluated⟩
      exact coreStep_deletedLet_shadowProgress sourceState targetState
        programs runtimeEq framesRelated continuation joins agree absent
          evaluated

/-- A retained join declaration takes the same administrative step on both
sides and installs related source/target bodies under their equal identifiers. -/
theorem coreStep_retainedJoin_shadowRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (declaration : ShadowFunDeclRelated fuel used
      sourceDeclaration targetDeclaration)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env) :
    ShadowCoreResultRelated fuel
      (coreStep { sourceState with
        control := .code (.jp sourceDeclaration sourceContinuation) })
      (coreStep { targetState with
        control := .code (.jp targetDeclaration targetContinuation) }) := by
  simp only [coreStep]
  exact .next {
    programs
    runtime_eq := runtimeEq
    frames := framesRelated
    control := .code continuation
      (joins.consBothOfKeys declaration.fvarId_eq declaration) agree
  }

/-- A deleted join declaration takes one source-only administrative step.
The added source entry is invisible because its identifier is absent from the
active liveness index. -/
theorem coreStep_deletedJoin_shadowProgress
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env)
    (absent : used.contains sourceDeclaration.fvarId = false) :
    ShadowMachineProgress fuel
      { sourceState with
        control := .code (.jp sourceDeclaration sourceContinuation) }
      { targetState with control := .code targetContinuation } := by
  let sourceAfter :=
    { sourceState with
      joins := (sourceDeclaration.fvarId, sourceDeclaration) ::
        sourceState.joins
      control := .code sourceContinuation }
  apply ShadowMachineProgress.sourceOnly sourceAfter
  · rfl
  · exact {
      programs
      runtime_eq := runtimeEq
      frames := framesRelated
      control := .code continuation
        (joins.consSourceOfAbsent absent) agree
    }

/-- Complete one-node progress theorem for a source join edge. -/
theorem coreStep_join_shadowProgress
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (graph : ShadowCodeGraph fuel used
      (.jp sourceDeclaration sourceContinuation) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env)
    (ready : ShadowJoinReadyAt fuel used sourceDeclaration
      sourceContinuation graph.joinResidual) :
    ShadowMachineProgress fuel
      { sourceState with
        control := .code (.jp sourceDeclaration sourceContinuation) }
      { targetState with control := .code targetCode } := by
  cases ready with
  | retained targetDeclaration targetContinuation declaration continuation =>
      apply ShadowMachineProgress.lockstep
      exact coreStep_retainedJoin_shadowRelated sourceState targetState
        programs runtimeEq framesRelated declaration continuation joins agree
  | deleted targetContinuation continuation absent =>
      exact coreStep_deletedJoin_shadowProgress sourceState targetState
        programs runtimeEq framesRelated continuation joins agree absent

/-- Return nodes are unchanged by the pass.  Coverage makes their value
lookup equal even when dead source bindings make the environments differ. -/
theorem coreStep_return_shadowRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (graph : ShadowCodeGraph fuel used (.return value) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env) :
    ShadowCoreResultRelated fuel
      (coreStep { sourceState with control := .code (.return value) })
      (coreStep { targetState with control := .code targetCode }) := by
  have targetEq := graph.returnTarget
  subst targetCode
  have covered := graph.covered
  cases covered with
  | ret member =>
      simp only [coreStep]
      rw [agree value member]
      generalize valueRead : lookupValue targetState.env value = result
      cases result with
      | error fault => exact shadowFail_related runtimeEq fault
      | ok result =>
          exact .next {
            programs
            runtime_eq := runtimeEq
            frames := framesRelated
            control := .yielded result
          }

/-- Unreachable nodes are unchanged and expose the same terminal fault because
raw observations depend only on the equal runtime states. -/
theorem coreStep_unreach_shadowRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (graph : ShadowCodeGraph fuel used (.unreach type) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env) :
    ShadowCoreResultRelated fuel
      (coreStep { sourceState with control := .code (.unreach type) })
      (coreStep { targetState with control := .code targetCode }) := by
  have targetEq := graph.unreachTarget
  subst targetCode
  exact shadowFail_related runtimeEq .unreachable

/-- Jump nodes are unchanged.  Extensional join lookup supplies related
declarations, covered arguments evaluate equally, and parameter binding
preserves agreement on the active liveness index. -/
theorem coreStep_jump_shadowRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (graph : ShadowCodeGraph fuel used (.jmp join arguments) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env) :
    ShadowCoreResultRelated fuel
      (coreStep { sourceState with control := .code (.jmp join arguments) })
      (coreStep { targetState with control := .code targetCode }) := by
  have targetEq := graph.jumpTarget
  subst targetCode
  have covered := graph.covered
  cases covered with
  | jump targetMember argumentsCovered =>
      have found := joins join targetMember
      generalize sourceFoundEq :
        findJoinPoint? sourceState.joins join = sourceFound at found
      generalize targetFoundEq :
        findJoinPoint? targetState.joins join = targetFound at found
      simp only [coreStep]
      rw [sourceFoundEq, targetFoundEq]
      cases found with
      | none => exact shadowFail_related runtimeEq (.unknownJoinPoint join)
      | some declarations =>
          rename_i sourceDeclaration targetDeclaration
          dsimp
          have argumentsEq : evalArgs sourceState.env arguments =
              evalArgs targetState.env arguments :=
            evalArgs_eq_of_covered agree argumentsCovered
          rw [argumentsEq]
          generalize argumentsRead :
            evalArgs targetState.env arguments = argumentResult
          cases argumentResult with
          | error fault =>
              simp only
              exact shadowFail_related runtimeEq fault
          | ok values =>
              simp only
              rw [declarations.params_eq]
              have binding := bindParamsOver_liveRelated
                (used := used) (params := targetDeclaration.params)
                (arguments := values) agree
              generalize sourceBindingEq : bindParamsOver sourceState.env
                targetDeclaration.params values = sourceBinding at binding ⊢
              generalize targetBindingEq : bindParamsOver targetState.env
                targetDeclaration.params values = targetBinding at binding ⊢
              cases binding with
              | error fault =>
                  simp only
                  exact shadowFail_related runtimeEq fault
              | ok nextAgree =>
                  simp only
                  exact .next {
                    programs
                    runtime_eq := runtimeEq
                    frames := framesRelated
                    control := .code declarations.value joins nextAgree
                  }

/-- Case dispatch reads the same covered discriminant and runtime tag, then
selects pointwise-related transformed alternative bodies. -/
theorem coreStep_cases_shadowRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (graph : ShadowCodeGraph fuel used
      (.cases (.mk typeName resultType discr sourceAlternatives)) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env) :
    ShadowCoreResultRelated fuel
      (coreStep { sourceState with
        control := .code (.cases
          (.mk typeName resultType discr sourceAlternatives)) })
      (coreStep { targetState with control := .code targetCode }) := by
  rcases graph.casesResidual with
    ⟨targetAlternatives, targetEq, alternatives, discrMember⟩
  subst targetCode
  simp only [coreStep]
  have discrEq :
      lookupValue sourceState.env
          (LCNF.Cases.mk typeName resultType discr sourceAlternatives).discr =
        lookupValue targetState.env
          (LCNF.Cases.mk typeName resultType discr targetAlternatives).discr :=
    agree discr discrMember
  rw [discrEq]
  generalize discrRead : lookupValue targetState.env
    (LCNF.Cases.mk typeName resultType discr targetAlternatives).discr =
      discrResult
  cases discrResult with
  | error fault =>
      simp only
      exact shadowFail_related runtimeEq fault
  | ok value =>
      simp only
      have tagEq : getTag sourceState.runtime value =
          getTag targetState.runtime value :=
        congrArg (fun runtime => getTag runtime value) runtimeEq
      rw [tagEq]
      generalize tagRead : getTag targetState.runtime value = tagResult
      cases tagResult with
      | error fault =>
          simp only
          exact shadowFail_related runtimeEq fault
      | ok tag =>
          simp only
          generalize sourceChoiceEq :
            chooseAlt tag
              (LCNF.Cases.mk typeName resultType discr
                sourceAlternatives).alts.toList = sourceChoice
          generalize targetChoiceEq :
            chooseAlt tag
              (LCNF.Cases.mk typeName resultType discr
                targetAlternatives).alts.toList = targetChoice
          have selected : OptionalRel (ShadowCodeGraph fuel used)
              sourceChoice targetChoice := by
            rw [← sourceChoiceEq, ← targetChoiceEq]
            exact alternatives.choose
          cases selected with
          | none =>
              simp only
              exact shadowFail_related runtimeEq .invalidCases
          | some body =>
              simp only
              exact .next {
                programs
                runtime_eq := runtimeEq
                frames := framesRelated
                control := .code body joins agree
              }

theorem coreStep_casesInfo_shadowRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel
      sourceState.frames targetState.frames)
    (graph : ShadowCodeGraph fuel used (.cases caseInfo) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (agree : EnvsAgreeOn used sourceState.env targetState.env) :
    ShadowCoreResultRelated fuel
      (coreStep { sourceState with control := .code (.cases caseInfo) })
      (coreStep { targetState with control := .code targetCode }) := by
  cases caseInfo with
  | mk typeName resultType discr alternatives =>
      exact coreStep_cases_shadowRelated sourceState targetState programs
        runtimeEq framesRelated graph joins agree

/-- Equal external responses preserve related waiting stacks and restore the
same yielded value. -/
theorem shadowResumeExternal_related
    (related : ShadowMachineRelated fuel source target) :
    ShadowMachineRelated fuel
      (resumeExternal request source response)
      (resumeExternal request target response) := {
  programs := related.programs
  runtime_eq := by
    simp [resumeExternal, MachineState.withValue, related.runtime_eq]
  frames := related.frames
  control := .yielded response.value
}

/-- Yielding either terminates equally or restores the graph, liveness set,
and environment agreement saved by the top related frame. -/
theorem coreStep_yielded_shadowRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (runtimeEq : sourceState.runtime = targetState.runtime)
    (framesRelated : ShadowFramesRelated fuel sourceFrames targetFrames) :
    ShadowCoreResultRelated fuel
      (coreStep { sourceState with
        frames := sourceFrames, control := .yielded value })
      (coreStep { targetState with
        frames := targetFrames, control := .yielded value }) := by
  cases framesRelated with
  | nil =>
      simp only [coreStep]
      rw [observe_eq_of_runtime_eq_live
        (left := { sourceState with
          frames := [], control := .yielded value })
        (right := { targetState with
          frames := [], control := .yielded value }) runtimeEq]
      exact .done _
  | cons frameRelated restRelated =>
      cases frameRelated with
      | bind graph joins agree =>
          exact .next {
            programs
            runtime_eq := runtimeEq
            frames := restRelated
            control := .code graph joins agree.bindBoth
          }
      | apply arguments =>
          exact .next {
            programs
            runtime_eq := runtimeEq
            frames := restRelated
            control := .invokeValue value arguments
          }
      | cache name =>
          exact .next {
            programs
            runtime_eq := congrArg
              (fun runtime => runtime.setGlobal name value) runtimeEq
            frames := restRelated
            control := .yielded value
          }

/-- Calling related top-level declarations preserves the shadow relation
through partial application, exact parameter entry, external waiting, and
faults. -/
theorem invokeDecl_shadowRelated
    (related : ShadowMachineRelated fuel source target) :
    ShadowCoreResultRelated fuel
      (invokeDecl source name arguments)
      (invokeDecl target name arguments) := by
  have found := related.programs.findDecl? name
  generalize sourceFoundEq : source.program.findDecl? name = sourceFound at found
  generalize targetFoundEq : target.program.findDecl? name = targetFound at found
  unfold invokeDecl
  rw [sourceFoundEq, targetFoundEq]
  cases found with
  | none => exact shadowFail_related related.runtime_eq (.unknownDecl name)
  | some declarations =>
      rename_i sourceDeclaration targetDeclaration
      rcases declarations with
        ⟨nameEq, levelParamsEq, typeEq, paramsEq, safeEq, valueRelated,
          recursiveEq, inlineAttrEq⟩
      simp only
      rw [paramsEq]
      by_cases tooFew : arguments.size < targetDeclaration.params.size
      · simp only [tooFew, ↓reduceIte]
        rw [related.runtime_eq]
        generalize allocation :
          alloc target.runtime
            (.closure name targetDeclaration.params.size arguments) = allocated
        obtain ⟨nextRuntime, reference⟩ := allocated
        exact .next {
          programs := related.programs
          runtime_eq := rfl
          frames := related.frames
          control := .yielded (.object reference)
        }
      · simp only [tooFew, ↓reduceIte]
        let callArguments :=
          arguments.extract 0 targetDeclaration.params.size
        let extraArguments :=
          arguments.extract targetDeclaration.params.size arguments.size
        let sourcePreparedFrames :=
          let frames := if extraArguments.isEmpty then source.frames
            else .apply extraArguments :: source.frames
          if targetDeclaration.params.isEmpty && arguments.isEmpty then
            .cache name :: frames
          else frames
        let targetPreparedFrames :=
          let frames := if extraArguments.isEmpty then target.frames
            else .apply extraArguments :: target.frames
          if targetDeclaration.params.isEmpty && arguments.isEmpty then
            .cache name :: frames
          else frames
        have preparedFrames : ShadowFramesRelated fuel
            sourcePreparedFrames targetPreparedFrames :=
          related.frames.prepareCall name targetDeclaration.params arguments
            extraArguments
        generalize binding :
          bindParams targetDeclaration.params callArguments = bound
        cases bound with
        | error fault => exact shadowFail_related related.runtime_eq fault
        | ok env =>
            generalize sourceValueEq :
              sourceDeclaration.value = sourceValue at valueRelated ⊢
            generalize targetValueEq :
              targetDeclaration.value = targetValue at valueRelated ⊢
            cases valueRelated with
            | code bodyRelated =>
                rcases bodyRelated with ⟨used, graph⟩
                exact .next {
                  programs := related.programs
                  runtime_eq := related.runtime_eq
                  frames := preparedFrames
                  control := .code graph (.empty fuel used) (.refl used env)
                }
            | extern metadata =>
                rw [typeEq]
                exact .external {
                  name
                  paramTypes := targetDeclaration.params.map (·.type)
                  resultType := targetDeclaration.type
                  args := callArguments
                } {
                  programs := related.programs
                  runtime_eq := related.runtime_eq
                  frames := preparedFrames
                  control := related.control.exactAt env
                }

theorem invokeClosure_shadowRelated
    (related : ShadowMachineRelated fuel source target)
    (function : Value) (arguments : Array Value) :
    ShadowCoreResultRelated fuel
      (invokeClosure
        { source with control := .invokeValue function arguments }
        function arguments)
      (invokeClosure
        { target with control := .invokeValue function arguments }
        function arguments) := by
  let sourceInvoke :=
    { source with control := .invokeValue function arguments }
  let targetInvoke :=
    { target with control := .invokeValue function arguments }
  have invokeRelated :
      ShadowMachineRelated fuel sourceInvoke targetInvoke := {
    programs := related.programs
    runtime_eq := related.runtime_eq
    frames := related.frames
    control := .invokeValue function arguments
  }
  have failure (fault : RuntimeFault) :
      ShadowCoreResultRelated fuel
        (fail sourceInvoke fault) (fail targetInvoke fault) :=
    shadowFail_related related.runtime_eq fault
  unfold invokeClosure
  cases function with
  | object reference =>
      cases reference with
      | tagged payload =>
          simp only
          exact failure .expectedClosure
      | heap location =>
          simp only
          have cellEq : getLiveCell source.runtime location =
              getLiveCell target.runtime location :=
            congrArg (fun runtime => getLiveCell runtime location)
              related.runtime_eq
          rw [cellEq]
          generalize cellRead : getLiveCell target.runtime location = result
          cases result with
          | error fault =>
              simp only
              exact failure fault
          | ok cell =>
              simp only
              cases cell.object with
              | closure name arity fixed =>
                  exact invokeDecl_shadowRelated invokeRelated
              | ctor object => exact failure .expectedClosure
              | boxed type value => exact failure .expectedClosure
              | string value => exact failure .expectedClosure
              | natural value => exact failure .expectedClosure
              | integer value => exact failure .expectedClosure
              | byteArray value => exact failure .expectedClosure
              | «opaque» typeName => exact failure .expectedClosure
  | usize value =>
      simp only
      exact failure .expectedClosure
  | scalar value =>
      simp only
      exact failure .expectedClosure
  | erased =>
      simp only
      exact failure .expectedClosure
  | reuseToken location =>
      simp only
      exact failure .expectedClosure

theorem coreStep_invokeName_shadowRelated
    (related : ShadowMachineRelated fuel source target)
    (name : Name) (arguments : Array Value) :
    ShadowCoreResultRelated fuel
      (coreStep { source with control := .invokeName name arguments })
      (coreStep { target with control := .invokeName name arguments }) := by
  let sourceInvoke := { source with control := .invokeName name arguments }
  let targetInvoke := { target with control := .invokeName name arguments }
  have invokeRelated :
      ShadowMachineRelated fuel sourceInvoke targetInvoke := {
    programs := related.programs
    runtime_eq := related.runtime_eq
    frames := related.frames
    control := .invokeName name arguments
  }
  by_cases argumentsEmpty : arguments.isEmpty
  · simp only [coreStep, argumentsEmpty]
    have globalEq : findGlobal? source.runtime.globals name =
        findGlobal? target.runtime.globals name :=
      congrArg (fun runtime => findGlobal? runtime.globals name)
        related.runtime_eq
    rw [globalEq]
    generalize globalRead : findGlobal? target.runtime.globals name = global
    cases global with
    | none => exact invokeDecl_shadowRelated invokeRelated
    | some value =>
        exact .next {
          programs := related.programs
          runtime_eq := related.runtime_eq
          frames := related.frames
          control := .yielded value
        }
  · simp only [coreStep, argumentsEmpty]
    exact invokeDecl_shadowRelated invokeRelated

theorem coreStep_invokeValue_shadowRelated
    (related : ShadowMachineRelated fuel source target)
    (function : Value) (arguments : Array Value) :
    ShadowCoreResultRelated fuel
      (coreStep { source with control := .invokeValue function arguments })
      (coreStep { target with control := .invokeValue function arguments }) := by
  simpa only [coreStep] using
    invokeClosure_shadowRelated related function arguments

/-- Progress for an arbitrary related control override.  The certified code
fragment dispatches to its node theorem; values and invocations are already
lockstep-related independently of lexical environments. -/
theorem shadowMachineProgress_withControl
    (related : ShadowMachineRelated fuel source target)
    (control : ShadowControlRelated fuel
      source.env source.joins sourceControl
      target.env target.joins targetControl)
    (ready : ShadowControlReadyAt fuel source sourceControl targetControl) :
    ShadowMachineProgress fuel
      { source with control := sourceControl }
      { target with control := targetControl } := by
  cases control with
  | code graph joins agree =>
      have codeReady := ready rfl rfl graph
      cases codeReady with
      | letE graph headReady =>
          exact coreStep_let_shadowProgress source target related.programs
            related.runtime_eq related.frames graph joins agree headReady
      | join graph headReady =>
          exact coreStep_join_shadowProgress source target related.programs
            related.runtime_eq related.frames graph joins agree headReady
      | cases graph =>
          apply ShadowMachineProgress.lockstep
          exact coreStep_casesInfo_shadowRelated source target
            related.programs related.runtime_eq related.frames graph joins
              agree
      | jump graph =>
          apply ShadowMachineProgress.lockstep
          exact coreStep_jump_shadowRelated source target related.programs
            related.runtime_eq related.frames graph joins agree
      | ret graph =>
          apply ShadowMachineProgress.lockstep
          exact coreStep_return_shadowRelated source target related.programs
            related.runtime_eq related.frames graph joins agree
      | unreachable graph =>
          apply ShadowMachineProgress.lockstep
          exact coreStep_unreach_shadowRelated source target related.programs
            related.runtime_eq related.frames graph joins agree
  | yielded value =>
      apply ShadowMachineProgress.lockstep
      exact coreStep_yielded_shadowRelated source target related.programs
        related.runtime_eq related.frames
  | invokeName name arguments =>
      let current : ShadowMachineRelated fuel
          { source with control := .invokeName name arguments }
          { target with control := .invokeName name arguments } := {
        programs := related.programs
        runtime_eq := related.runtime_eq
        frames := related.frames
        control := .invokeName name arguments
      }
      apply ShadowMachineProgress.lockstep
      exact coreStep_invokeName_shadowRelated current name arguments
  | invokeValue function arguments =>
      let current : ShadowMachineRelated fuel
          { source with control := .invokeValue function arguments }
          { target with control := .invokeValue function arguments } := {
        programs := related.programs
        runtime_eq := related.runtime_eq
        frames := related.frames
        control := .invokeValue function arguments
      }
      apply ShadowMachineProgress.lockstep
      exact coreStep_invokeValue_shadowRelated current function arguments

theorem shadowMachineProgress
    (related : ShadowMachineRelated fuel source target)
    (ready : ShadowControlReadyAt fuel source
      source.control target.control) :
    ShadowMachineProgress fuel source target := by
  simpa using shadowMachineProgress_withControl related related.control ready

/-- A lockstep-related core result matches a semantic source step, including
the same externally supplied response. -/
theorem shadowMatchCoreResult
    (beforeRelated : ShadowMachineRelated fuel sourceBefore targetBefore)
    (results : ShadowCoreResultRelated fuel
      (coreStep sourceBefore) (coreStep targetBefore))
    (step : Step externals sourceBefore sourceAfter) :
    ∃ targetAfter, NonLockstep.Reaches externals targetBefore targetAfter ∧
      ShadowMachineRelated fuel sourceAfter targetAfter := by
  generalize sourceResultEq : coreStep sourceBefore = sourceResult at results
  generalize targetResultEq : coreStep targetBefore = targetResult at results
  cases results with
  | next afterRelated =>
      cases step with
      | internal transition =>
          rw [sourceResultEq] at transition
          cases transition
          exact ⟨_, NonLockstep.reaches_of_step (.internal targetResultEq),
            afterRelated⟩
      | external transition externalProof =>
          rw [sourceResultEq] at transition
          contradiction
  | external request waitingRelated =>
      rename_i sourceWaiting targetWaiting
      cases step with
      | internal transition =>
          rw [sourceResultEq] at transition
          contradiction
      | external transition externalProof =>
          rw [sourceResultEq] at transition
          cases transition
          rename_i response
          have targetExternal :
              externals request targetBefore.runtime response := by
            rw [← beforeRelated.runtime_eq]
            exact externalProof
          exact ⟨resumeExternal request targetWaiting response,
            NonLockstep.reaches_of_step
              (.external targetResultEq targetExternal),
            shadowResumeExternal_related waitingRelated⟩
  | done observation =>
      cases step with
      | internal transition =>
          rw [sourceResultEq] at transition
          contradiction
      | external transition externalProof =>
          rw [sourceResultEq] at transition
          contradiction

/-- Equal terminal observations provide a zero-step target evaluation. -/
theorem shadowTerminalCoreResult
    (results : ShadowCoreResultRelated fuel
      (coreStep source) (coreStep target))
    (done : coreStep source = .done observation) :
    SimpCase.EvaluatesState externals target observation := by
  generalize sourceResultEq : coreStep source = sourceResult at results
  generalize targetResultEq : coreStep target = targetResult at results
  cases results with
  | next related =>
      rw [sourceResultEq] at done
      contradiction
  | external request related =>
      rw [sourceResultEq] at done
      contradiction
  | done result =>
      rw [sourceResultEq] at done
      cases done
      exact ⟨0, target, .refl target, targetResultEq⟩

structure ShadowMachineRelatedWith (fuel : Nat)
    (invariant : MachineState → MachineState → Prop)
    (source target : MachineState) : Prop where
  structural : ShadowMachineRelated fuel source target
  invariant : invariant source target

/-- Laws required of the semantic invariant for the exact-runtime fragment.
It establishes active readiness and is preserved along the finite paths built
by the structural simulation. -/
structure ShadowInvariantLaws (externals : ExternalSpec) (fuel : Nat)
    (invariant : MachineState → MachineState → Prop) : Prop where
  ready : ∀ {source target}
    (_ : ShadowMachineRelated fuel source target),
    invariant source target →
      ShadowControlReadyAt fuel source source.control target.control
  stable : ∀ {sourceBefore targetBefore sourceAfter targetAfter},
    invariant sourceBefore targetBefore →
    ShadowMachineRelated fuel sourceBefore targetBefore →
    NonLockstep.Reaches externals sourceBefore sourceAfter →
    NonLockstep.Reaches externals targetBefore targetAfter →
    ShadowMachineRelated fuel sourceAfter targetAfter →
      invariant sourceAfter targetAfter

/-- Forward finite-stuttering simulation for the currently certified
exact-runtime fragment.  Deleted lets and joins consume one source step and
zero target steps; every other certified node advances lockstep. -/
theorem shadowRecursiveForward
    (laws : ShadowInvariantLaws externals fuel invariant) :
    NonLockstep.StutteringSimulation externals
      (ShadowMachineRelatedWith fuel invariant) where
  terminal := by
    intro source target observation refined done
    have ready : ShadowControlReadyAt fuel source
        source.control target.control :=
      laws.ready refined.structural refined.invariant
    have progress := shadowMachineProgress refined.structural ready
    cases progress with
    | lockstep results => exact shadowTerminalCoreResult results done
    | sourceOnly sourceAfter transition afterRelated =>
        rw [transition] at done
        contradiction
  advance := by
    intro sourceBefore sourceAfter target refined step
    have ready : ShadowControlReadyAt fuel sourceBefore
        sourceBefore.control target.control :=
      laws.ready refined.structural refined.invariant
    have progress := shadowMachineProgress refined.structural ready
    cases progress with
    | lockstep results =>
        rcases shadowMatchCoreResult refined.structural results step with
          ⟨targetAfter, targetPath, afterStructural⟩
        have sourcePath := NonLockstep.reaches_of_step step
        have afterInvariant := laws.stable refined.invariant
          refined.structural sourcePath targetPath afterStructural
        exact ⟨targetAfter, targetPath, {
          structural := afterStructural
          invariant := afterInvariant
        }⟩
    | sourceOnly expected transition afterStructural =>
        cases step with
        | internal actual =>
            rw [transition] at actual
            cases actual
            have sourcePath : NonLockstep.Reaches externals
                sourceBefore sourceAfter :=
              NonLockstep.reaches_of_step
                (Step.internal transition)
            have targetPath : NonLockstep.Reaches externals target target :=
              NonLockstep.reaches_refl target
            have afterInvariant := laws.stable refined.invariant
              refined.structural sourcePath targetPath afterStructural
            exact ⟨target, targetPath, {
              structural := afterStructural
              invariant := afterInvariant
            }⟩
        | external actual externalProof =>
            rw [transition] at actual
            contradiction

/-- Whole-program graph relatedness supplies every initial invocation state;
no semantic entry premise is needed until an eliminable operation is reached. -/
theorem shadowInitialState_related
    (programs : ProgramRelated (ShadowCodeRelated fuel) source target) :
    ShadowMachineRelated fuel
      (initialState source entry arguments)
      (initialState target entry arguments) := {
  programs
  runtime_eq := rfl
  frames := .nil
  control := .invokeName entry arguments
}

end Fir.LeanIR.Passes.ElimDead
