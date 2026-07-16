import Fir.LeanIR.PassCorrectness

namespace Fir.LeanIR.Passes.SimpCase

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure

/-- Termination from an arbitrary machine state, rather than a program entry. -/
def EvaluatesState (externals : ExternalSpec) (initial : MachineState)
    (observation : Observation) : Prop :=
  ∃ count final,
    Steps externals count initial final ∧
    coreStep final = .done observation

/-- Prefixing an evaluation by one deterministic internal step is unobservable. -/
theorem evaluatesState_internal_iff
    (transition : coreStep before = .next after) :
    EvaluatesState externals before observation ↔
      EvaluatesState externals after observation := by
  constructor
  · rintro ⟨count, final, execution, done⟩
    cases execution with
    | refl _ => simp [transition] at done
    | step head tail =>
        cases head with
        | internal actual =>
            rw [transition] at actual
            cases actual
            exact ⟨_, _, tail, done⟩
        | external actual _ => simp [transition] at actual
  · rintro ⟨count, final, execution, done⟩
    exact ⟨count + 1, final, .step (.internal transition) execution, done⟩

/-- The pure specification kernel corresponding to `simpCase`'s first rewrite. -/
def isUnreachable : LCNF.Code .impure → Bool
  | .unreach _ => true
  | _ => false

def removeUnreachable : List (LCNF.Alt .impure) → List (LCNF.Alt .impure)
  | [] => []
  | alt :: rest =>
      if isUnreachable alt.getCode then
        removeUnreachable rest
      else
        alt :: removeUnreachable rest

def removeUnreachableCases (caseInfo : LCNF.Cases .impure) : LCNF.Cases .impure :=
  caseInfo.updateAlts (removeUnreachable caseInfo.alts.toList).toArray

@[simp] theorem removeUnreachableCases_discr (caseInfo : LCNF.Cases .impure) :
    (removeUnreachableCases caseInfo).discr = caseInfo.discr := by
  cases caseInfo
  rfl

@[simp] theorem removeUnreachableCases_alts (caseInfo : LCNF.Cases .impure) :
    (removeUnreachableCases caseInfo).alts.toList =
      removeUnreachable caseInfo.alts.toList := by
  cases caseInfo
  simp [removeUnreachableCases, LCNF.Cases.updateAlts, LCNF.Cases.alts]

theorem findCtorAlt_removeUnreachable_some
    (found : findCtorAlt tag alts = some branch)
    (reachable : isUnreachable branch = false) :
    findCtorAlt tag (removeUnreachable alts) = some branch := by
  induction alts with
  | nil => simp [findCtorAlt] at found
  | cons alt rest ih =>
      cases alt with
      | ctorAlt info code =>
          by_cases tagMatch : info.cidx == tag
          · simp [findCtorAlt, tagMatch] at found
            cases found
            simp [removeUnreachable, LCNF.Alt.getCode, reachable, findCtorAlt, tagMatch]
          · have tailFound : findCtorAlt tag rest = some branch := by
              simpa [findCtorAlt, tagMatch] using found
            have tailResult := ih tailFound
            by_cases unreachable : isUnreachable code
            · simp [removeUnreachable, LCNF.Alt.getCode, unreachable, tailResult]
            · simp [removeUnreachable, LCNF.Alt.getCode, unreachable,
                findCtorAlt, tagMatch, tailResult]
      | default code =>
          have tailFound : findCtorAlt tag rest = some branch := by
            simpa [findCtorAlt] using found
          have tailResult := ih tailFound
          by_cases unreachable : isUnreachable code
          · simp [removeUnreachable, LCNF.Alt.getCode, unreachable, tailResult]
          · simp [removeUnreachable, LCNF.Alt.getCode, unreachable,
              findCtorAlt, tailResult]
      | alt _ _ _ impossible => nomatch impossible

theorem findCtorAlt_removeUnreachable_none
    (notFound : findCtorAlt tag alts = none) :
    findCtorAlt tag (removeUnreachable alts) = none := by
  induction alts with
  | nil => rfl
  | cons alt rest ih =>
      cases alt with
      | ctorAlt info code =>
          by_cases tagMatch : info.cidx == tag
          · simp [findCtorAlt, tagMatch] at notFound
          · have tailNotFound : findCtorAlt tag rest = none := by
              simpa [findCtorAlt, tagMatch] using notFound
            have tailResult := ih tailNotFound
            by_cases unreachable : isUnreachable code
            · simp [removeUnreachable, LCNF.Alt.getCode, unreachable, tailResult]
            · simp [removeUnreachable, LCNF.Alt.getCode, unreachable,
                findCtorAlt, tagMatch, tailResult]
      | default code =>
          have tailNotFound : findCtorAlt tag rest = none := by
            simpa [findCtorAlt] using notFound
          have tailResult := ih tailNotFound
          by_cases unreachable : isUnreachable code
          · simp [removeUnreachable, LCNF.Alt.getCode, unreachable, tailResult]
          · simp [removeUnreachable, LCNF.Alt.getCode, unreachable,
              findCtorAlt, tailResult]
      | alt _ _ _ impossible => nomatch impossible

theorem findDefaultAlt_removeUnreachable_some
    (found : findDefaultAlt alts = some branch)
    (reachable : isUnreachable branch = false) :
    findDefaultAlt (removeUnreachable alts) = some branch := by
  induction alts with
  | nil => simp [findDefaultAlt] at found
  | cons alt rest ih =>
      cases alt with
      | ctorAlt info code =>
          have tailFound : findDefaultAlt rest = some branch := by
            simpa [findDefaultAlt] using found
          have tailResult := ih tailFound
          by_cases unreachable : isUnreachable code
          · simp [removeUnreachable, LCNF.Alt.getCode, unreachable, tailResult]
          · simp [removeUnreachable, LCNF.Alt.getCode, unreachable,
              findDefaultAlt, tailResult]
      | default code =>
          simp [findDefaultAlt] at found
          cases found
          simp [removeUnreachable, LCNF.Alt.getCode, reachable, findDefaultAlt]
      | alt _ _ _ impossible => nomatch impossible

theorem chooseAlt_removeUnreachable_of_selected
    (selected : chooseAlt tag alts = some branch)
    (reachable : isUnreachable branch = false) :
    chooseAlt tag (removeUnreachable alts) = some branch := by
  cases foundCtor : findCtorAlt tag alts with
  | some code =>
      have codeEq : code = branch := by
        simpa [chooseAlt, foundCtor] using selected
      subst code
      have preserved := findCtorAlt_removeUnreachable_some foundCtor reachable
      simp [chooseAlt, preserved]
  | none =>
      have foundDefault : findDefaultAlt alts = some branch := by
        simpa [chooseAlt, foundCtor] using selected
      have noCtor := findCtorAlt_removeUnreachable_none foundCtor
      have preserved := findDefaultAlt_removeUnreachable_some foundDefault reachable
      simp [chooseAlt, noCtor, preserved]

/--
The semantic kernel of single-arm case elimination: when a case selects
`branch`, entering that branch directly preserves every complete observation.
-/
theorem selected_case_elimination_correct
    {state : MachineState} {caseInfo : LCNF.Cases .impure}
    {discr : Value} {tag : Nat} {branch : LCNF.Code .impure}
    {externals : ExternalSpec} {observation : Observation}
    (lookupDiscr : lookupValue state.env caseInfo.discr = .ok discr)
    (readTag : getTag state.runtime discr = .ok tag)
    (selected : chooseAlt tag caseInfo.alts.toList = some branch) :
    EvaluatesState externals
        { state with control := .code (.cases caseInfo) } observation ↔
      EvaluatesState externals
        { state with control := .code branch } observation := by
  apply evaluatesState_internal_iff
  simp [coreStep, lookupDiscr, readTag, selected]

/--
Removing syntactically unreachable arms preserves an execution whenever the
arm selected by the phase invariant is itself reachable.
-/
theorem remove_unreachable_correct_of_selected
    {state : MachineState} {caseInfo : LCNF.Cases .impure}
    {discr : Value} {tag : Nat} {branch : LCNF.Code .impure}
    {externals : ExternalSpec} {observation : Observation}
    (lookupDiscr : lookupValue state.env caseInfo.discr = .ok discr)
    (readTag : getTag state.runtime discr = .ok tag)
    (selected : chooseAlt tag caseInfo.alts.toList = some branch)
    (reachable : isUnreachable branch = false) :
    EvaluatesState externals
        { state with control := .code (.cases caseInfo) } observation ↔
      EvaluatesState externals
        { state with control := .code (.cases (removeUnreachableCases caseInfo)) }
        observation := by
  have filteredLookup :
      lookupValue state.env (removeUnreachableCases caseInfo).discr = .ok discr := by
    simpa using lookupDiscr
  have filteredSelection :
      chooseAlt tag (removeUnreachableCases caseInfo).alts.toList = some branch := by
    simpa using
      chooseAlt_removeUnreachable_of_selected selected reachable
  calc
    EvaluatesState externals
        { state with control := .code (.cases caseInfo) } observation ↔
      EvaluatesState externals
        { state with control := .code branch } observation :=
          selected_case_elimination_correct lookupDiscr readTag selected
    _ ↔ EvaluatesState externals
        { state with control := .code (.cases (removeUnreachableCases caseInfo)) }
        observation :=
          (selected_case_elimination_correct filteredLookup readTag filteredSelection).symm

/-- A singleton default arm is selected for every well-typed discriminant. -/
theorem singleton_default_elimination_correct
    {state : MachineState} {caseInfo : LCNF.Cases .impure}
    {discr : Value} {tag : Nat} {branch : LCNF.Code .impure}
    {externals : ExternalSpec} {observation : Observation}
    (lookupDiscr : lookupValue state.env caseInfo.discr = .ok discr)
    (readTag : getTag state.runtime discr = .ok tag)
    (alts : caseInfo.alts = #[.default branch]) :
    EvaluatesState externals
        { state with control := .code (.cases caseInfo) } observation ↔
      EvaluatesState externals
        { state with control := .code branch } observation := by
  apply selected_case_elimination_correct lookupDiscr readTag
  simp [alts, chooseAlt, findCtorAlt, findDefaultAlt]

/-- A singleton constructor arm is removable when its tag invariant holds. -/
theorem singleton_constructor_elimination_correct
    {state : MachineState} {caseInfo : LCNF.Cases .impure}
    {discr : Value} {info : LCNF.CtorInfo} {branch : LCNF.Code .impure}
    {externals : ExternalSpec} {observation : Observation}
    (lookupDiscr : lookupValue state.env caseInfo.discr = .ok discr)
    (readTag : getTag state.runtime discr = .ok info.cidx)
    (alts : caseInfo.alts = #[.ctorAlt info branch]) :
    EvaluatesState externals
        { state with control := .code (.cases caseInfo) } observation ↔
      EvaluatesState externals
        { state with control := .code branch } observation := by
  apply selected_case_elimination_correct lookupDiscr readTag
  simp [alts, chooseAlt, findCtorAlt]

end Fir.LeanIR.Passes.SimpCase
