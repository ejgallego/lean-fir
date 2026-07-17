import Fir.LeanIR.Passes.NonLockstep
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
open Fir.LeanIR.Passes.SimpCase

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

def entryFrames (args : Array Value) : List Frame :=
  if args.isEmpty then [.cache `main] else [.apply args]

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

/-- Execute Lean's actual recursive pass over the declaration fixture. This
keeps the compiler/specification bridge executable while the upstream pass
graph remains private. -/
def checkActualClosedTraversal : CoreM Unit := do
  let output ← LCNF.CompilerM.run
    (LCNF.simpCase.run sourceProgram.decls) (phase := .impure)
  unless output == targetProgram.decls do
    throwError "simpCase did not produce the proved closed target program"

elab "#check_closed_simp_case_traversal" : command =>
  liftCoreM checkActualClosedTraversal

#check_closed_simp_case_traversal

end Fir.LeanIR.Passes.NonLockstepExamples
