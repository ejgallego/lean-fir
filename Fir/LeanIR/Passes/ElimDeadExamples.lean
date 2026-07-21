import Fir.LeanIR.Passes.ElimDead
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
