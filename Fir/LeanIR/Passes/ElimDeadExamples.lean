import Fir.LeanIR.Passes.ElimDeadProgram
import Fir.LeanIR.InterpreterExamples
import Lean.Compiler.LCNF.ElimDead
import Lean.Elab.Command

namespace Fir.LeanIR.Passes.ElimDeadExamples

open Lean
open Lean.Elab.Command
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples
open Fir.LeanIR.Passes.ElimDead
open Fir.LeanIR.Passes.SimpCase
open Fir.LeanIR.Passes.NonLockstep.Structural

def live : FVarId := ⟨`live⟩
def dead : FVarId := ⟨`dead⟩

def liveDecl : LCNF.LetDecl .impure :=
  letDecl live objType .erased

def deadErasedDecl : LCNF.LetDecl .impure :=
  letDecl dead objType .erased

def deadCopyDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.fvar live #[])

def oneFieldInfo : LCNF.CtorInfo :=
  { name := `Dead.one, cidx := 0, size := 1, usize := 0, ssize := 0 }

def deadCtorDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.ctor oneFieldInfo #[.fvar live])

def neutralBefore : LCNF.Code .impure :=
  .let liveDecl <| .let deadErasedDecl <| .return live

def neutralAfter : LCNF.Code .impure :=
  .let liveDecl <| .return live

def usedBefore : LCNF.Code .impure :=
  .let deadErasedDecl <| .return dead

def unsafeBefore : LCNF.Code .impure :=
  .let liveDecl <| .let deadCopyDecl <| .return live

def allocatingBefore : LCNF.Code .impure :=
  .let liveDecl <| .let deadCtorDecl <| .return live

def allocatingAfter : LCNF.Code .impure := neutralAfter

#guard safeToElim deadErasedDecl.value
#guard safeToElim deadCtorDecl.value
#guard !safeToElim deadCopyDecl.value

def fixtureDecl (name : Name) (code : LCNF.Code .impure) :
    LCNF.Decl .impure :=
  decl name #[] objType (.code code)

def checkActualElimDead (name : Name) (before expected : LCNF.Code .impure) :
    CoreM Unit := do
  let some (shadow, _) := shadowCode? 64 {} before |
    throwError "elimDeadVars shadow fixture {name} exhausted its fuel"
  unless shadow == expected do
    throwError "elimDeadVars shadow fixture {name} did not produce the expected code"
  let actual ← LCNF.CompilerM.run
    (fixtureDecl name before).elimDeadVars (phase := .impure)
  let .code actualCode := actual.value |
    throwError "elimDeadVars fixture {name} ceased to be code"
  unless actualCode == shadow do
    throwError "elimDeadVars fixture {name} disagreed with the transparent shadow"

def traversalCodes : Array (LCNF.Code .impure) := #[
  literalCode,
  erasedCode,
  ctorProjectionCode,
  caseCode,
  directCallCode,
  closureCallCode,
  joinCode,
  scalarBoxCode,
  mutationCode,
  usizeProjectionCode,
  objectMutationCode,
  tagMutationCode,
  defaultCaseCode,
  rcCode,
  persistentRcCode,
  isSharedCaseCode,
  resetReuseCode,
  sharedResetCode,
  deletedCode,
  externalCode,
  .unreach objType
]

def traversalCorpus : ImpureProgram :=
  { decls := traversalCodes.mapIdx fun index code =>
      fixtureDecl (Name.mkSimple s!"elimDeadShadow{index}") code }

def checkActualAgreement (fuel : Nat) (program : ImpureProgram) : CoreM Unit := do
  let some shadow := shadowProgram? fuel program |
    throwError "elimDeadVars program shadow exhausted its fuel"
  let actual ← program.decls.mapM fun declaration =>
    LCNF.CompilerM.run declaration.elimDeadVars (phase := .impure)
  unless actual == shadow.decls do
    throwError "elimDeadVars program disagreed with the transparent shadow"

def checkFixtures : CoreM Unit := do
  checkActualElimDead `elimDeadNeutral neutralBefore neutralAfter
  checkActualElimDead `elimDeadUsed usedBefore usedBefore
  checkActualElimDead `elimDeadUnsafe unsafeBefore unsafeBefore
  checkActualElimDead `elimDeadAllocating allocatingBefore allocatingAfter
  checkActualAgreement 128 traversalCorpus

elab "#check_elim_dead_fixtures" : command =>
  liftCoreM checkFixtures

#check_elim_dead_fixtures

def neutralBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main neutralBefore] }

def neutralAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main neutralAfter] }

def allocatingBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main allocatingBefore] }

def allocatingAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main allocatingAfter] }

def neutralUsed : UsedLocals :=
  ({} : UsedLocals).insert live

theorem neutralShadowRun :
    shadowCode? 3 {} neutralBefore = some (neutralAfter, neutralUsed) := by
  change shadowCode? 3 {} neutralBefore =
    some (neutralAfter, ({} : UsedLocals).insert live)
  have liveMember : live ∈ ({} : UsedLocals).insert live := by native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by native_decide
  simp [neutralBefore, neutralAfter, liveDecl, deadErasedDecl, letDecl,
    shadowCode?, safeToElim, collectLetValue, liveMember, deadAbsent]

/-- The transparent declaration/program lifting relates the complete neutral
fixture, rather than only its local code output. -/
theorem neutralProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 3)
      neutralBeforeProgram neutralAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?, neutralBeforeProgram,
    neutralAfterProgram, fixtureDecl, decl, neutralShadowRun]

theorem neutralInitialShadowRelated (entry : Name)
    (arguments : Array Value) :
    ShadowMachineRelated 3
      (initialState neutralBeforeProgram entry arguments)
      (initialState neutralAfterProgram entry arguments) :=
  shadowInitialState_related neutralProgramShadowRelated

def liveEnv : Env :=
  bind [] live .erased

def deadExtendedEnv : Env :=
  bind liveEnv dead (.usize 42)

/-- A binding absent from the backwards used set can be added to one side
without changing any lookup the transformed suffix is allowed to perform. -/
theorem deadBindingOutsideCtorLiveness :
    EnvsAgreeOn (collectLetValue {} deadCtorDecl.value)
      deadExtendedEnv liveEnv := by
  apply EnvsAgreeOn.bindLeft_of_absent (EnvsAgreeOn.refl _ liveEnv)
  native_decide

/-- The semantic counterpart of the concrete liveness regression: evaluating
the constructor value is insensitive to the dead environment binding. -/
theorem deadCtorEvalIgnoresDeadBinding (state : MachineState) :
    evalLetValue { state with env := deadExtendedEnv } deadCtorDecl =
      evalLetValue { state with env := liveEnv } deadCtorDecl := by
  exact evalLetValue_eq_of_covered state deadBindingOutsideCtorLiveness
    (collectLetValue_covers {} deadCtorDecl.value)

/- The executable shadow reports precisely the expected live-variable boundary
on the complete backwards-elimination fixture. -/
#guard (match shadowCode? 64 {} neutralBefore with
  | some (code, used) =>
      code == neutralAfter && used.contains live && !used.contains dead
  | none => false)

/-- Any successful execution of that fixture inherits the generic syntactic
coverage guarantee used by the later machine simulation. -/
theorem neutralShadowCovered
    (result : shadowCode? 64 {} neutralBefore = some output) :
    CodeCovered output.2 output.1 :=
  (shadowCode_spec result).1

theorem neutralAfterCovered :
    CodeCovered (({} : UsedLocals).insert live) neutralAfter := by
  apply CodeCovered.letE
  · trivial
  · exact .ret (by simp)

def neutralLiveState : MachineState :=
  { program := neutralAfterProgram
    control := .code neutralAfter
    env := liveEnv }

/-- The liveness-indexed machine relation accepts the concrete environment
difference introduced by executing and then deleting the dead binding. -/
theorem deadBindingMachineRelated :
    LiveMachineRelated
      { neutralLiveState with env := deadExtendedEnv }
      neutralLiveState := by
  simpa [neutralLiveState, deadExtendedEnv] using
    liveMachineRelated_bindLeft_of_absent
      (used := ({} : UsedLocals).insert live)
      (state := neutralLiveState) (binder := dead) (value := .usize 42)
      (code := neutralAfter) neutralAfterCovered
      (by simp [neutralLiveState, JoinEnvCovered])
      (by native_decide)

/-- The first interpreter step reads only covered variables, so both concrete
environments produce related successor results. -/
theorem deadBindingCoreStepRelated :
    LiveCoreResultRelated
      (coreStep { neutralLiveState with env := deadExtendedEnv })
      (coreStep neutralLiveState) := by
  have agree : EnvsAgreeOn (({} : UsedLocals).insert live)
      deadExtendedEnv liveEnv := by
    simpa [deadExtendedEnv] using
      (EnvsAgreeOn.bindLeft_of_absent (binder := dead) (value := .usize 42)
        (EnvsAgreeOn.refl (({} : UsedLocals).insert live) liveEnv)
        (by native_decide))
  simpa [neutralLiveState] using
    coreStep_codeLive_related
      (used := ({} : UsedLocals).insert live) (joins := [])
      (leftState := { neutralLiveState with env := deadExtendedEnv })
      (rightState := neutralLiveState) rfl rfl (.nil)
      neutralAfterCovered (by simp [JoinEnvCovered]) agree

/-- The one-step regression lifts to every terminating observation, including
external calls reached later through the related continuation stacks. -/
theorem deadBindingExecutionEquivalent (externals : ExternalSpec) :
    EvaluatesState externals
        { neutralLiveState with env := deadExtendedEnv } observation ↔
      EvaluatesState externals neutralLiveState observation :=
  evaluatesState_iff_of_liveRelated deadBindingMachineRelated

/-- A dead erased binding before a live return is the concrete nonterminal
one-step/zero-step deletion shape. -/
theorem deadErasedBeforeReturnCorrect (externals : ExternalSpec) :
    EvaluatesState externals
        { neutralLiveState with
          control := .code (.let deadErasedDecl (.return live)) }
        observation ↔
      EvaluatesState externals
        { neutralLiveState with control := .code (.return live) }
        observation := by
  apply eliminateLet_correct_of_runtimeNeutral_coverage
      (used := ({} : UsedLocals).insert live) (value := .erased)
  · rfl
  · exact .ret (by simp)
  · simp [neutralLiveState, JoinEnvCovered]
  · native_decide

/-- Recursive composition follows the actual neutral fixture: the outer live
let is retained while its recursively transformed continuation deletes the
inner dead erased let. -/
theorem neutralCodeEquivalentAt (externals : ExternalSpec)
    (state : MachineState) :
    CodeEquivalentAt externals { state with joins := [] }
      neutralBefore neutralAfter := by
  unfold neutralBefore neutralAfter
  apply let_codeEquivalentAt_of_runtimeNeutral (value := .erased)
  · rfl
  · apply eliminateLet_codeEquivalentAt_of_runtimeNeutral
      (used := ({} : UsedLocals).insert live) (value := .erased)
    · rfl
    · exact codeEquivalentAt_refl
    · exact .ret (by simp)
    · simp [JoinEnvCovered]
    · native_decide

/- Runtime-neutral elimination satisfies the current raw-observation contract
on a complete declaration-entry execution. -/
#guard (match runMain neutralBeforeProgram, runMain neutralAfterProgram with
  | .done left, .done right => left == right
  | _, _ => false)

/- The allocating fixture minimizes the observation-contract bug: both runs
return erased, but their raw heaps differ by the dead constructor cell. -/
#guard (match runMain allocatingBeforeProgram, runMain allocatingAfterProgram with
  | .done left, .done right =>
      left.outcome == right.outcome && left.heap != right.heap
  | _, _ => false)

theorem erasedKernelRegression (externals : ExternalSpec)
    (state : MachineState) (type : Expr) :
    EvaluatesState externals
        { state with
          control := .code (.let deadErasedDecl (.unreach type)) } observation ↔
      EvaluatesState externals
        { state with control := .code (.unreach type) } observation := by
  exact eliminate_erased_before_unreach state dead dead.name objType type

end Fir.LeanIR.Passes.ElimDeadExamples
