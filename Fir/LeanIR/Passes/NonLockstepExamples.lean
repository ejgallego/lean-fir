import Fir.LeanIR.Passes.SimpCaseCompilerBridge
import Fir.LeanIR.InterpreterExamples
import Lean.Elab.Command

namespace Fir.LeanIR.Passes.NonLockstepExamples

open Lean
open Lean.Elab.Command
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples
open Fir.LeanIR.Passes.NonLockstep
open Fir.LeanIR.Passes.NonLockstep.Structural
open Fir.LeanIR.Passes.SimpCase
open Fir.LeanIR.Passes.SimpCaseCompilerBridge
open Fir.LeanIR.Passes.SimpCaseRelation

/-!
This fixture is deliberately closed over its case discriminant. Consequently
the program theorem quantifies over every raw entry argument without needing a
typing premise: the declaration constructs the valid tag itself.
-/

def closedCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[.default (.return x)]

def sourceTail : LCNF.Code .impure :=
  .let (letDecl x objType .erased) (.cases closedCases)

def targetTail : LCNF.Code .impure :=
  .let (letDecl x objType .erased) (.return x)

def sourceBody : LCNF.Code .impure :=
  .let (letDecl c objType (.lit (.nat 0))) sourceTail

def targetBody : LCNF.Code .impure :=
  .let (letDecl c objType (.lit (.nat 0))) targetTail

def sourceProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code sourceBody)] }

def targetProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code targetBody)] }

/-- Every natural tag is admissible for the closed singleton-default fixture.
The runtime-readiness component below separately proves that the discriminant
is a valid tagged object when the eliminated case becomes active. -/
def closedValidCase (_ : LCNF.Cases .impure) (_ : Nat) : Prop := True

abbrev ClosedCodeRel := CodeRel closedValidCase

theorem closedReturnRelated :
    ClosedCodeRel (.return x) (.return x) :=
  .aligned (.return x)

theorem closedCaseEliminated :
    ClosedCodeRel (.cases closedCases) (.return x) := by
  apply CodeRel.eliminate closedCases (.return x)
  intro tag valid
  change ElimSelectionRel closedValidCase (.return x) (some (.return x))
  exact .some closedReturnRelated

theorem closedTailRelated : ClosedCodeRel sourceTail targetTail := by
  exact .aligned (.let (letDecl x objType .erased) closedCaseEliminated)

theorem closedBodyRelated : ClosedCodeRel sourceBody targetBody := by
  exact .aligned
    (.let (letDecl c objType (.lit (.nat 0))) closedTailRelated)

theorem closedProgramsRelated :
    ProgramRelated ClosedCodeRel sourceProgram targetProgram := by
  exact .cons {
    name_eq := rfl
    levelParams_eq := rfl
    type_eq := rfl
    params_eq := rfl
    safe_eq := rfl
    value := .code closedBodyRelated
    recursive_eq := rfl
    inlineAttr_eq := rfl
  } .nil

def structuralMainDeclaration : LCNF.Decl .impure :=
  decl `main #[] objType (.code sourceBody)

def helperBody : LCNF.Code .impure :=
  .unreach objType

def structuralHelperDeclaration : LCNF.Decl .impure :=
  decl `helper #[] objType (.code helperBody)

def multiSourceProgram : ImpureProgram :=
  { decls := #[
      { structuralMainDeclaration with value := .code sourceBody },
      { structuralHelperDeclaration with value := .code helperBody }] }

def multiTargetProgram : ImpureProgram :=
  { decls := #[
      { structuralMainDeclaration with value := .code targetBody },
      { structuralHelperDeclaration with value := .code helperBody }] }

inductive FixtureCodeRel :
    LCNF.Code .impure → LCNF.Code .impure → Prop where
  | transformed : FixtureCodeRel sourceBody targetBody
  | helper : FixtureCodeRel helperBody helperBody

theorem multiProgramsRelated :
    ProgramRelated FixtureCodeRel multiSourceProgram multiTargetProgram := by
  simpa [multiSourceProgram, multiTargetProgram] using
    two_code_declarations_related
      (firstDeclaration := structuralMainDeclaration)
      (secondDeclaration := structuralHelperDeclaration)
      FixtureCodeRel.transformed FixtureCodeRel.helper

theorem multiHelperLookupRelated :
    OptionalRel (DeclRelated FixtureCodeRel)
      (multiSourceProgram.findDecl? `helper)
      (multiTargetProgram.findDecl? `helper) :=
  multiProgramsRelated.findDecl? `helper

theorem multiInitialStateRelated (entry : Name) (args : Array Value) :
    MachineRelated FixtureCodeRel
      (initialState multiSourceProgram entry args)
      (initialState multiTargetProgram entry args) :=
  initialState_related multiProgramsRelated

def entryFrames (args : Array Value) : List Frame :=
  if args.isEmpty then [.cache `main] else [.apply args]

theorem entryFramesClosedRelated (args : Array Value) :
    FramesRelated ClosedCodeRel (entryFrames args) (entryFrames args) := by
  simp only [entryFrames]
  split
  · exact .cons (.cache `main) .nil
  · exact .cons (.apply args) .nil

def afterDiscrEnv : Env :=
  bind [] c (.object (.tagged 0))

def branchEnv : Env :=
  bind afterDiscrEnv x .erased

def bodyState (program : ImpureProgram) (body : LCNF.Code .impure)
    (args : Array Value) : MachineState :=
  { program, control := .code body, frames := entryFrames args }

def afterDiscrState (program : ImpureProgram) (tail : LCNF.Code .impure)
    (args : Array Value) : MachineState :=
  { program
    control := .code tail
    env := afterDiscrEnv
    frames := entryFrames args }

def branchState (program : ImpureProgram) (code : LCNF.Code .impure)
    (args : Array Value) : MachineState :=
  { program
    control := .code code
    env := branchEnv
    frames := entryFrames args }

def yieldedState (program : ImpureProgram) (args : Array Value) : MachineState :=
  { program, control := .yielded .erased, env := branchEnv,
    frames := entryFrames args }

def cachedState (program : ImpureProgram) : MachineState :=
  { program
    control := .yielded .erased
    env := branchEnv
    runtime := ({} : RuntimeState).setGlobal `main .erased }

def invokingState (program : ImpureProgram) (args : Array Value) : MachineState :=
  { program
    control := .invokeValue .erased args
    env := branchEnv }

theorem source_entry_step (args : Array Value) :
    coreStep (initialState sourceProgram `main args) =
      .next (bodyState sourceProgram sourceBody args) := by
  by_cases empty : args = #[] <;>
    simp_all [initialState, coreStep, sourceProgram, Program.findDecl?,
      invokeDecl, bodyState, entryFrames, decl, bindParams, findGlobal?]

theorem target_entry_step (args : Array Value) :
    coreStep (initialState targetProgram `main args) =
      .next (bodyState targetProgram targetBody args) := by
  by_cases empty : args = #[] <;>
    simp_all [initialState, coreStep, targetProgram, Program.findDecl?,
      invokeDecl, bodyState, entryFrames, decl, bindParams, findGlobal?]

theorem source_body_step (args : Array Value) :
    coreStep (bodyState sourceProgram sourceBody args) =
      .next (afterDiscrState sourceProgram sourceTail args) := by
  rfl

theorem target_body_step (args : Array Value) :
    coreStep (bodyState targetProgram targetBody args) =
      .next (afterDiscrState targetProgram targetTail args) := by
  rfl

theorem source_discr_step (args : Array Value) :
    coreStep (afterDiscrState sourceProgram sourceTail args) =
      .next (branchState sourceProgram (.cases closedCases) args) := by
  rfl

theorem target_discr_step (args : Array Value) :
    coreStep (afterDiscrState targetProgram targetTail args) =
      .next (branchState targetProgram (.return x) args) := by
  rfl

theorem source_case_step (args : Array Value) :
    coreStep (branchState sourceProgram (.cases closedCases) args) =
      .next (branchState sourceProgram (.return x) args) := by
  rfl

theorem source_return_step (args : Array Value) :
    coreStep (branchState sourceProgram (.return x) args) =
      .next (yieldedState sourceProgram args) := by
  simp [coreStep, branchState, yieldedState, branchEnv, afterDiscrEnv,
    entryFrames, lookupValue]

theorem target_return_step (args : Array Value) :
    coreStep (branchState targetProgram (.return x) args) =
      .next (yieldedState targetProgram args) := by
  simp [coreStep, branchState, yieldedState, branchEnv, afterDiscrEnv,
    entryFrames, lookupValue]

theorem source_yielded_step_empty :
    coreStep (yieldedState sourceProgram #[]) =
      .next (cachedState sourceProgram) := by
  rfl

theorem target_yielded_step_empty :
    coreStep (yieldedState targetProgram #[]) =
      .next (cachedState targetProgram) := by
  rfl

theorem source_yielded_step_nonempty (notEmpty : args ≠ #[]) :
    coreStep (yieldedState sourceProgram args) =
      .next (invokingState sourceProgram args) := by
  simp [coreStep, yieldedState, entryFrames, notEmpty, invokingState]

theorem target_yielded_step_nonempty (notEmpty : args ≠ #[]) :
    coreStep (yieldedState targetProgram args) =
      .next (invokingState targetProgram args) := by
  simp [coreStep, yieldedState, entryFrames, notEmpty, invokingState]

theorem cached_coreStep_eq :
    coreStep (cachedState sourceProgram) =
      coreStep (cachedState targetProgram) := by
  rfl

theorem invoking_coreStep_eq (args : Array Value) :
    coreStep (invokingState sourceProgram args) =
      coreStep (invokingState targetProgram args) := by
  rfl

theorem evaluates_zero_of_coreStep_eq
    (same : coreStep right = coreStep left)
    (done : coreStep left = .done observation) :
    EvaluatesState externals right observation :=
  ⟨0, right, .refl right, same.trans done⟩

theorem match_next
    (relation : MachineState → MachineState → Prop)
    (leftTransition : coreStep left = .next leftAfter)
    (rightTransition : coreStep right = .next rightAfter)
    (afterRelated : relation leftAfter rightAfter)
    (step : Step externals left actual) :
    ∃ targetAfter, Reaches externals right targetAfter ∧
      relation actual targetAfter := by
  cases step with
  | internal actualTransition =>
      rw [leftTransition] at actualTransition
      cases actualTransition
      exact ⟨rightAfter, reaches_of_step (.internal rightTransition), afterRelated⟩
  | external actualTransition external =>
      simp [leftTransition] at actualTransition

theorem match_zero
    (relation : MachineState → MachineState → Prop)
    (leftTransition : coreStep left = .next leftAfter)
    (afterRelated : relation leftAfter right)
    (step : Step externals left actual) :
    ∃ targetAfter, Reaches externals right targetAfter ∧
      relation actual targetAfter := by
  cases step with
  | internal actualTransition =>
      rw [leftTransition] at actualTransition
      cases actualTransition
      exact ⟨right, reaches_refl right, afterRelated⟩
  | external actualTransition external =>
      simp [leftTransition] at actualTransition

theorem no_step_of_done
    (done : coreStep before = .done observation)
    (step : Step externals before after) : False := by
  cases step with
  | internal transition => simp [done] at transition
  | external transition external => simp [done] at transition

/-- Reachable states of two programs that differ by one eliminated case node.
The `caseBranch` constructor is the non-lockstep point. -/
inductive ProgramStateRel : MachineState → MachineState → Prop where
  | entry (args : Array Value) :
      ProgramStateRel
        (initialState sourceProgram `main args)
        (initialState targetProgram `main args)
  | body (args : Array Value) :
      ProgramStateRel
        (bodyState sourceProgram sourceBody args)
        (bodyState targetProgram targetBody args)
  | afterDiscr (args : Array Value) :
      ProgramStateRel
        (afterDiscrState sourceProgram sourceTail args)
        (afterDiscrState targetProgram targetTail args)
  | caseBranch (args : Array Value) :
      ProgramStateRel
        (branchState sourceProgram (.cases closedCases) args)
        (branchState targetProgram (.return x) args)
  | branch (args : Array Value) :
      ProgramStateRel
        (branchState sourceProgram (.return x) args)
        (branchState targetProgram (.return x) args)
  | yielded (args : Array Value) :
      ProgramStateRel
        (yieldedState sourceProgram args)
        (yieldedState targetProgram args)
  | cached :
      ProgramStateRel (cachedState sourceProgram) (cachedState targetProgram)
  | invoking (args : Array Value) :
      ProgramStateRel
        (invokingState sourceProgram args)
        (invokingState targetProgram args)

/-- Every state in the concrete bisimulation is an instance of the recursive
code graph lifted through programs, frames, joins, and controls. -/
theorem programStateStructural
    (related : ProgramStateRel left right) :
    MachineRelated ClosedCodeRel left right := by
  cases related with
  | entry args => exact initialState_related closedProgramsRelated
  | body args =>
      exact {
        programs := closedProgramsRelated
        runtime_eq := rfl
        env_eq := rfl
        joins := .nil
        frames := entryFramesClosedRelated args
        control := .code closedBodyRelated
      }
  | afterDiscr args =>
      exact {
        programs := closedProgramsRelated
        runtime_eq := rfl
        env_eq := rfl
        joins := .nil
        frames := entryFramesClosedRelated args
        control := .code closedTailRelated
      }
  | caseBranch args =>
      exact {
        programs := closedProgramsRelated
        runtime_eq := rfl
        env_eq := rfl
        joins := .nil
        frames := entryFramesClosedRelated args
        control := .code closedCaseEliminated
      }
  | branch args =>
      exact {
        programs := closedProgramsRelated
        runtime_eq := rfl
        env_eq := rfl
        joins := .nil
        frames := entryFramesClosedRelated args
        control := .code closedReturnRelated
      }
  | yielded args =>
      exact {
        programs := closedProgramsRelated
        runtime_eq := rfl
        env_eq := rfl
        joins := .nil
        frames := entryFramesClosedRelated args
        control := .yielded .erased
      }
  | cached =>
      exact {
        programs := closedProgramsRelated
        runtime_eq := rfl
        env_eq := rfl
        joins := .nil
        frames := .nil
        control := .yielded .erased
      }
  | invoking args =>
      exact {
        programs := closedProgramsRelated
        runtime_eq := rfl
        env_eq := rfl
        joins := .nil
        frames := .nil
        control := .invokeValue .erased args
      }

theorem programStateReady
    (related : ProgramStateRel left right) :
    ControlReadyAt closedValidCase left left.control right.control := by
  cases related with
  | entry args => simp [ControlReadyAt, initialState]
  | body args =>
      simp [ControlReadyAt, CodeReadyAt, bodyState, sourceBody, targetBody]
  | afterDiscr args =>
      simp [ControlReadyAt, CodeReadyAt, afterDiscrState, sourceTail, targetTail]
  | caseBranch args =>
      change ∃ value tag,
        lookupValue branchEnv c = .ok value ∧
        getTag ({} : RuntimeState) value = .ok tag ∧ True
      refine ⟨.object (.tagged 0), 0, ?_, rfl, trivial⟩
      have xNotC : (`x == `c) = false := by decide
      simp [branchEnv, afterDiscrEnv, lookupValue, Impure.bind, Impure.lookup,
        x, c, xNotC]
  | branch args => simp [ControlReadyAt, CodeReadyAt, branchState]
  | yielded args => simp [ControlReadyAt, yieldedState]
  | cached => simp [ControlReadyAt, cachedState]
  | invoking args => simp [ControlReadyAt, invokingState]

theorem refinedProgramState_iff (left right : MachineState) :
    MachineRelatedWith ClosedCodeRel ProgramStateRel left right ↔
      ProgramStateRel left right := by
  constructor
  · exact fun related => related.invariant
  · intro related
    exact { structural := programStateStructural related, invariant := related }

theorem programForward (externals : ExternalSpec) :
    StutteringSimulation externals ProgramStateRel where
  terminal := by
    intro left right observation related done
    cases related with
    | entry args => rw [source_entry_step] at done; contradiction
    | body args => rw [source_body_step] at done; contradiction
    | afterDiscr args => rw [source_discr_step] at done; contradiction
    | caseBranch args => rw [source_case_step] at done; contradiction
    | branch args => rw [source_return_step] at done; contradiction
    | yielded args =>
        by_cases empty : args = #[]
        · subst args
          rw [source_yielded_step_empty] at done
          contradiction
        · rw [source_yielded_step_nonempty empty] at done
          contradiction
    | cached => exact evaluates_zero_of_coreStep_eq cached_coreStep_eq done
    | invoking args =>
        exact evaluates_zero_of_coreStep_eq (invoking_coreStep_eq args) done
  advance := by
    intro leftBefore leftAfter right related step
    cases related with
    | entry args =>
        exact match_next ProgramStateRel
          (source_entry_step args) (target_entry_step args) (.body args) step
    | body args =>
        exact match_next ProgramStateRel
          (source_body_step args) (target_body_step args) (.afterDiscr args) step
    | afterDiscr args =>
        exact match_next ProgramStateRel
          (source_discr_step args) (target_discr_step args) (.caseBranch args) step
    | caseBranch args =>
        exact match_zero ProgramStateRel
          (source_case_step args) (.branch args) step
    | branch args =>
        exact match_next ProgramStateRel
          (source_return_step args) (target_return_step args) (.yielded args) step
    | yielded args =>
        by_cases empty : args = #[]
        · subst args
          exact match_next ProgramStateRel source_yielded_step_empty
            target_yielded_step_empty .cached step
        · exact match_next ProgramStateRel
            (source_yielded_step_nonempty empty)
            (target_yielded_step_nonempty empty) (.invoking args) step
    | cached =>
        exact (no_step_of_done (by rfl) step).elim
    | invoking args =>
        exact (no_step_of_done (by rfl) step).elim

theorem programBackward (externals : ExternalSpec) :
    StutteringSimulation externals
      (fun target source => ProgramStateRel source target) where
  terminal := by
    intro target source observation related done
    cases related with
    | entry args => rw [target_entry_step] at done; contradiction
    | body args => rw [target_body_step] at done; contradiction
    | afterDiscr args => rw [target_discr_step] at done; contradiction
    | caseBranch args => rw [target_return_step] at done; contradiction
    | branch args => rw [target_return_step] at done; contradiction
    | yielded args =>
        by_cases empty : args = #[]
        · subst args
          rw [target_yielded_step_empty] at done
          contradiction
        · rw [target_yielded_step_nonempty empty] at done
          contradiction
    | cached => exact evaluates_zero_of_coreStep_eq cached_coreStep_eq done
    | invoking args =>
        exact evaluates_zero_of_coreStep_eq (invoking_coreStep_eq args) done
  advance := by
    intro targetBefore targetAfter source related step
    cases related with
    | entry args =>
        exact match_next (fun target source => ProgramStateRel source target)
          (target_entry_step args) (source_entry_step args) (.body args) step
    | body args =>
        exact match_next (fun target source => ProgramStateRel source target)
          (target_body_step args) (source_body_step args) (.afterDiscr args) step
    | afterDiscr args =>
        exact match_next (fun target source => ProgramStateRel source target)
          (target_discr_step args) (source_discr_step args) (.caseBranch args) step
    | caseBranch args =>
        cases step with
        | internal actualTransition =>
            rw [target_return_step] at actualTransition
            cases actualTransition
            exact ⟨yieldedState sourceProgram args,
              (reaches_of_step (.internal (source_case_step args))).trans
                (reaches_of_step (.internal (source_return_step args))),
              .yielded args⟩
        | external actualTransition external =>
            simp [target_return_step] at actualTransition
    | branch args =>
        exact match_next (fun target source => ProgramStateRel source target)
          (target_return_step args) (source_return_step args) (.yielded args) step
    | yielded args =>
        by_cases empty : args = #[]
        · subst args
          exact match_next (fun target source => ProgramStateRel source target)
            target_yielded_step_empty source_yielded_step_empty .cached step
        · exact match_next (fun target source => ProgramStateRel source target)
            (target_yielded_step_nonempty empty)
            (source_yielded_step_nonempty empty) (.invoking args) step
    | cached =>
        exact (no_step_of_done (by rfl) step).elim
    | invoking args =>
        exact (no_step_of_done (by rfl) step).elim

theorem programBisimulation (externals : ExternalSpec) :
    StutteringBisimulation externals ProgramStateRel where
  forward := programForward externals
  backward := programBackward externals

/-- The existing execution proof reindexed through the recursive code graph
and the generic `MachineRelatedWith` structural lifting. -/
theorem recursiveProgramBisimulation (externals : ExternalSpec) :
    StutteringBisimulation externals
      (MachineRelatedWith ClosedCodeRel ProgramStateRel) where
  forward := (programForward externals).reindex (by
    intro left right
    exact refinedProgramState_iff left right)
  backward := (programBackward externals).reindex (by
    intro right left
    exact refinedProgramState_iff left right)

theorem recursiveInitialInvariant :
    InitialInvariantOn (fun _ _ => True) ProgramStateRel
      sourceProgram targetProgram #[`main] := by
  intro entry member args accepted
  have entryEq : entry = `main := by simpa using member
  subst entry
  exact .entry args

theorem initialStatesRelated :
    InitialStatesRelated ProgramStateRel sourceProgram targetProgram #[`main] := by
  intro entry member args
  have entryEq : entry = `main := by simpa using member
  subst entry
  exact .entry args

/-- Whole-program correctness for a declaration whose recursive traversal
eliminates a closed singleton case. The programs are syntactically different,
and the proof quantifies over every entry argument array. -/
theorem closed_singleton_default_program_correct (externals : ExternalSpec) :
    SamePhaseCorrect (Impure.semantics externals)
      sourceProgram targetProgram #[`main] :=
  samePhaseCorrect_of_stuttering
    (programBisimulation externals) initialStatesRelated

/-- The same whole-program result through the new recursive relation and the
typed-entry lifting interface.  This is the first end-to-end instantiation of
the graph that future generic core-step closure will consume. -/
theorem closed_singleton_default_recursive_relation_correct
    (externals : ExternalSpec) :
    SamePhaseCorrectOn (Impure.semantics externals)
      sourceProgram targetProgram #[`main] (fun _ _ => True) :=
  samePhaseCorrectOn_of_refined_machine_bisimulation
    closedProgramsRelated recursiveInitialInvariant
    (recursiveProgramBisimulation externals)

/-- The closed fixture instantiated directly through the generic recursive
bisimulation.  Its entry predicate states the reusable hereditary readiness
condition; the concrete theorem above separately discharges the stronger
all-arguments claim with the fixture's explicit reachable-state relation. -/
theorem closed_singleton_default_generic_relation_correct
    (externals : ExternalSpec) :
    SamePhaseCorrectOn (Impure.semantics externals)
      sourceProgram targetProgram #[`main]
      (ReachablyReadyAdmissible externals closedValidCase
        sourceProgram targetProgram) :=
  samePhaseCorrectOn_reachablyReady closedProgramsRelated

/-- Execute Lean's actual recursive pass over the declaration fixture. This
keeps the compiler/specification bridge executable while the upstream pass
graph remains private. -/
theorem closedShadowRun :
    shadowProgram? 4 sourceProgram = some targetProgram := by
  rfl

def checkActualClosedTraversal : CoreM Unit :=
  checkActualAgreement 4 sourceProgram

elab "#check_closed_simp_case_traversal" : command =>
  liftCoreM checkActualClosedTraversal

#check_closed_simp_case_traversal

end Fir.LeanIR.Passes.NonLockstepExamples
