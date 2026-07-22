import Fir.LeanIR.Passes.ElimDeadMachineRel
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
def usizeField : FVarId := ⟨`usizeField⟩
def scalarField : FVarId := ⟨`scalarField⟩
def reuseTokenVar : FVarId := ⟨`reuseToken⟩
def reuseArgVar : FVarId := ⟨`reuseArg⟩
def resetObjectVar : FVarId := ⟨`resetObject⟩
def papArgVar : FVarId := ⟨`papArg⟩
def boxInputVar : FVarId := ⟨`boxInput⟩

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

def deletedWritesBefore : LCNF.Code .impure :=
  .oset dead 0 .erased <|
  .uset dead 0 usizeField <|
  .sset dead 8 0 scalarField u8Type <|
  .return live

def deletedWritesAfter : LCNF.Code .impure :=
  .return live

def deadReuseDecl : LCNF.LetDecl .impure :=
  letDecl dead objType
    (.reuse reuseTokenVar oneFieldInfo true #[.fvar reuseArgVar])

def deletedReuseBefore : LCNF.Code .impure :=
  .let deadReuseDecl (.return live)

def deletedReuseAfter : LCNF.Code .impure :=
  .return live

def deadResetDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.reset 1 resetObjectVar)

def deletedResetBefore : LCNF.Code .impure :=
  .let deadResetDecl (.return live)

def deletedResetAfter : LCNF.Code .impure :=
  .return live

def deadLargeNatDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.lit (.nat 9223372036854775808))

def deletedLargeNatBefore : LCNF.Code .impure :=
  .let deadLargeNatDecl (.return live)

def deletedLargeNatAfter : LCNF.Code .impure :=
  .return live

def deadPapDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.pap `first #[.fvar papArgVar])

def deletedPapBefore : LCNF.Code .impure :=
  .let deadPapDecl (.return live)

def deletedPapAfter : LCNF.Code .impure :=
  .return live

def deadBoxDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.box u64Type boxInputVar)

def deletedBoxBefore : LCNF.Code .impure :=
  .let deadBoxDecl (.return live)

def deletedBoxAfter : LCNF.Code .impure :=
  .return live

def deadNullaryFapDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.fap `deadNullaryExternal #[])

def deadNullaryFapBefore : LCNF.Code .impure :=
  .let liveDecl <| .let deadNullaryFapDecl <| .return live

def deadNullaryFapAfter : LCNF.Code .impure :=
  .let liveDecl <| .return live

#guard safeToElim deadErasedDecl.value
#guard safeToElim deadCtorDecl.value
#guard safeToElim deadNullaryFapDecl.value
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
  checkActualElimDead `elimDeadWrites deletedWritesBefore deletedWritesAfter
  checkActualElimDead `elimDeadReuse deletedReuseBefore deletedReuseAfter
  checkActualElimDead `elimDeadReset deletedResetBefore deletedResetAfter
  checkActualElimDead `elimDeadLargeNat
    deletedLargeNatBefore deletedLargeNatAfter
  checkActualElimDead `elimDeadPap deletedPapBefore deletedPapAfter
  checkActualElimDead `elimDeadBox deletedBoxBefore deletedBoxAfter
  checkActualElimDead `elimDeadNullaryFap
    deadNullaryFapBefore deadNullaryFapAfter
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

def deletedWritesBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedWritesBefore] }

def deletedWritesAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedWritesAfter] }

def deletedReuseBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedReuseBefore] }

def deletedReuseAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedReuseAfter] }

def deletedResetBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedResetBefore] }

def deletedResetAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedResetAfter] }

def deletedLargeNatBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedLargeNatBefore] }

def deletedLargeNatAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedLargeNatAfter] }

def deletedPapBeforeProgram : ImpureProgram :=
  { decls := #[firstDecl, fixtureDecl `main deletedPapBefore] }

def deletedPapAfterProgram : ImpureProgram :=
  { decls := #[firstDecl, fixtureDecl `main deletedPapAfter] }

def deletedBoxBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedBoxBefore] }

def deletedBoxAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedBoxAfter] }

def deadNullaryExternalDecl : LCNF.Decl .impure :=
  decl `deadNullaryExternal #[] objType (.extern { entries := [] })

def deadNullaryFapBeforeProgram : ImpureProgram :=
  { decls := #[deadNullaryExternalDecl,
      fixtureDecl `main deadNullaryFapBefore] }

def deadNullaryFapAfterProgram : ImpureProgram :=
  { decls := #[deadNullaryExternalDecl,
      fixtureDecl `main deadNullaryFapAfter] }

def countedNullaryExternal : ExternalImpl where
  call _ runtime := .ok {
    value := .erased
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world + 1 }

theorem deadNullaryFapBeforeWellFormed :
    WellFormedAt .impure deadNullaryFapBeforeProgram := by
  apply WellFormedAt.impure
  · simp [Program.NamesUnique, deadNullaryFapBeforeProgram,
      deadNullaryExternalDecl, fixtureDecl, decl]
  · unfold Program.ImpureHygienic
    native_decide

theorem deadNullaryFapAfterWellFormed :
    WellFormedAt .impure deadNullaryFapAfterProgram := by
  apply WellFormedAt.impure
  · simp [Program.NamesUnique, deadNullaryFapAfterProgram,
      deadNullaryExternalDecl, fixtureDecl, decl]
  · unfold Program.ImpureHygienic
    native_decide

/-- Executable witness that current impure well-formedness does not make the
upstream nullary-constant rule sound for FIR's observable external effects. -/
def deadNullaryFapObservableMismatch : Bool :=
  match runMain deadNullaryFapBeforeProgram countedNullaryExternal,
      runMain deadNullaryFapAfterProgram countedNullaryExternal with
  | .done source, .done target =>
      source.outcome == .returned .erased &&
        target.outcome == .returned .erased &&
        source.world == 1 && source.trace.size == 1 &&
        target.world == 0 && target.trace.isEmpty
  | _, _ => false

#guard deadNullaryFapObservableMismatch

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

theorem allocatingShadowRun :
    shadowCode? 3 {} allocatingBefore =
      some (allocatingAfter, neutralUsed) := by
  change shadowCode? 3 {} allocatingBefore =
    some (allocatingAfter, ({} : UsedLocals).insert live)
  have liveMember : live ∈ ({} : UsedLocals).insert live := by native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by native_decide
  simp [allocatingBefore, allocatingAfter, neutralAfter, liveDecl,
    deadCtorDecl, letDecl, shadowCode?, safeToElim, collectLetValue,
    collectArgs, collectArgList, collectArg, liveMember, deadAbsent]

theorem deletedWritesShadowRun :
    shadowCode? 4 {} deletedWritesBefore =
      some (deletedWritesAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deletedWritesBefore, deletedWritesAfter, neutralUsed, shadowCode?,
    liveMember, deadAbsent]

theorem deletedUSizeScalarShadowRun :
    shadowCode? 3 {}
        (.uset dead 0 usizeField <|
          .sset dead 8 0 scalarField u8Type <| .return live) =
      some (.return live, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [neutralUsed, shadowCode?, liveMember, deadAbsent]

theorem deletedScalarShadowRun :
    shadowCode? 2 {}
        (.sset dead 8 0 scalarField u8Type <| .return live) =
      some (.return live, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [neutralUsed, shadowCode?, liveMember, deadAbsent]

theorem deletedReuseShadowRun :
    shadowCode? 2 {} deletedReuseBefore =
      some (deletedReuseAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deletedReuseBefore, deletedReuseAfter, deadReuseDecl, letDecl,
    neutralUsed, shadowCode?, safeToElim, liveMember, deadAbsent]

theorem deletedResetShadowRun :
    shadowCode? 2 {} deletedResetBefore =
      some (deletedResetAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deletedResetBefore, deletedResetAfter, deadResetDecl, letDecl,
    neutralUsed, shadowCode?, safeToElim, liveMember, deadAbsent]

theorem deletedLargeNatShadowRun :
    shadowCode? 2 {} deletedLargeNatBefore =
      some (deletedLargeNatAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deletedLargeNatBefore, deletedLargeNatAfter, deadLargeNatDecl,
    letDecl, neutralUsed, shadowCode?, safeToElim, liveMember, deadAbsent]

theorem deletedPapShadowRun :
    shadowCode? 2 {} deletedPapBefore =
      some (deletedPapAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deletedPapBefore, deletedPapAfter, deadPapDecl, letDecl,
    neutralUsed, shadowCode?, safeToElim, liveMember, deadAbsent]

theorem deletedBoxShadowRun :
    shadowCode? 2 {} deletedBoxBefore =
      some (deletedBoxAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deletedBoxBefore, deletedBoxAfter, deadBoxDecl, letDecl,
    neutralUsed, shadowCode?, safeToElim, liveMember, deadAbsent]

/-- The transparent declaration/program lifting relates the complete neutral
fixture, rather than only its local code output. -/
theorem neutralProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 3)
      neutralBeforeProgram neutralAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?, neutralBeforeProgram,
    neutralAfterProgram, fixtureDecl, decl, neutralShadowRun]

theorem allocatingProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 3)
      allocatingBeforeProgram allocatingAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?, allocatingBeforeProgram,
    allocatingAfterProgram, fixtureDecl, decl, allocatingShadowRun]

theorem deletedWritesProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 4)
      deletedWritesBeforeProgram deletedWritesAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    deletedWritesBeforeProgram, deletedWritesAfterProgram,
    fixtureDecl, decl, deletedWritesShadowRun]

theorem deletedReuseProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 2)
      deletedReuseBeforeProgram deletedReuseAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    deletedReuseBeforeProgram, deletedReuseAfterProgram,
    fixtureDecl, decl, deletedReuseShadowRun]

theorem deletedResetProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 2)
      deletedResetBeforeProgram deletedResetAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    deletedResetBeforeProgram, deletedResetAfterProgram,
    fixtureDecl, decl, deletedResetShadowRun]

theorem deletedLargeNatProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 2)
      deletedLargeNatBeforeProgram deletedLargeNatAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    deletedLargeNatBeforeProgram, deletedLargeNatAfterProgram,
    fixtureDecl, decl, deletedLargeNatShadowRun]

theorem firstDeclShadowRun :
    shadowDecl? 2 firstDecl = some firstDecl := by
  simp [shadowDecl?, firstDecl, decl, shadowCode?]

theorem deletedPapMainDeclShadowRun :
    shadowDecl? 2 (fixtureDecl `main deletedPapBefore) =
      some (fixtureDecl `main deletedPapAfter) := by
  simp [shadowDecl?, fixtureDecl, decl, deletedPapShadowRun]

theorem deletedPapProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 2)
      deletedPapBeforeProgram deletedPapAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, deletedPapBeforeProgram,
    deletedPapAfterProgram, firstDeclShadowRun, deletedPapMainDeclShadowRun]

theorem deletedBoxProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 2)
      deletedBoxBeforeProgram deletedBoxAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    deletedBoxBeforeProgram, deletedBoxAfterProgram,
    fixtureDecl, decl, deletedBoxShadowRun]

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

def deletedWriteObject : ConstructorObject :=
  { tag := 0
    objectFields := #[.erased]
    usizeFields := #[0]
    scalarFields := [] }

def deletedWriteSourceRuntime : RuntimeState :=
  (alloc ({} : RuntimeState) (.ctor deletedWriteObject)).1

def deletedWriteSourceEnv : Env :=
  bind (bind (bind liveEnv dead (.object (.heap 0)))
    usizeField (.usize 7)) scalarField (.scalar (.uint8 9))

def deletedObjectSetSourceState : MachineState :=
  { program := deletedWritesBeforeProgram
    control := .code deletedWritesBefore
    env := deletedWriteSourceEnv
    runtime := deletedWriteSourceRuntime }

def deletedUSizeSetSourceState : MachineState :=
  { program := deletedWritesBeforeProgram
    control := .code (.uset dead 0 usizeField <|
      .sset dead 8 0 scalarField u8Type <| .return live)
    env := deletedWriteSourceEnv
    runtime := deletedWriteSourceRuntime }

def deletedScalarSetSourceState : MachineState :=
  { program := deletedWritesBeforeProgram
    control := .code (.sset dead 8 0 scalarField u8Type <| .return live)
    env := deletedWriteSourceEnv
    runtime := deletedWriteSourceRuntime }

def deletedWritesTargetState : MachineState :=
  { program := deletedWritesAfterProgram
    control := .code deletedWritesAfter
    env := liveEnv }

def deletedReuseNoneSourceEnv : Env :=
  bind (bind liveEnv reuseTokenVar (.reuseToken none))
    reuseArgVar .erased

def deletedReuseSomeSourceEnv : Env :=
  bind (bind liveEnv reuseTokenVar (.reuseToken (some 0)))
    reuseArgVar .erased

def deletedReuseNoneSourceState : MachineState :=
  { program := deletedReuseBeforeProgram
    control := .code deletedReuseBefore
    env := deletedReuseNoneSourceEnv }

def deletedReuseSomeSourceState : MachineState :=
  { program := deletedReuseBeforeProgram
    control := .code deletedReuseBefore
    env := deletedReuseSomeSourceEnv
    runtime := deletedWriteSourceRuntime }

def deletedReuseTargetState : MachineState :=
  { program := deletedReuseAfterProgram
    control := .code deletedReuseAfter
    env := liveEnv }

def deletedResetObject : ConstructorObject :=
  { tag := 0
    objectFields := #[.object (.tagged 7)]
    usizeFields := #[]
    scalarFields := [] }

def deletedResetClearedObject : ConstructorObject :=
  { deletedResetObject with objectFields := #[.object (.tagged 0)] }

def deletedResetSourceRuntime : RuntimeState :=
  (alloc ({} : RuntimeState) (.ctor deletedResetObject)).1

def deletedResetReplacementCell : HeapCell :=
  { object := .ctor deletedResetClearedObject }

def deletedResetNextRuntime : RuntimeState :=
  { deletedResetSourceRuntime with
    heap := [(0, deletedResetReplacementCell)] }

def deletedResetSourceEnv : Env :=
  bind liveEnv resetObjectVar (.object (.heap 0))

def deletedResetSourceState : MachineState :=
  { program := deletedResetBeforeProgram
    control := .code deletedResetBefore
    env := deletedResetSourceEnv
    runtime := deletedResetSourceRuntime }

def deletedResetTargetState : MachineState :=
  { program := deletedResetAfterProgram
    control := .code deletedResetAfter
    env := liveEnv }

def deletedLargeNatSourceState : MachineState :=
  { program := deletedLargeNatBeforeProgram
    control := .code deletedLargeNatBefore
    env := liveEnv }

def deletedLargeNatTargetState : MachineState :=
  { program := deletedLargeNatAfterProgram
    control := .code deletedLargeNatAfter
    env := liveEnv }

def deletedPapSourceEnv : Env :=
  bind liveEnv papArgVar .erased

def deletedPapSourceState : MachineState :=
  { program := deletedPapBeforeProgram
    control := .code deletedPapBefore
    env := deletedPapSourceEnv }

def deletedPapTargetState : MachineState :=
  { program := deletedPapAfterProgram
    control := .code deletedPapAfter
    env := liveEnv }

def deletedBoxSourceEnv : Env :=
  bind liveEnv boxInputVar (.scalar (.uint64 18446744073709551615))

def deletedBoxSourceState : MachineState :=
  { program := deletedBoxBeforeProgram
    control := .code deletedBoxBefore
    env := deletedBoxSourceEnv }

def deletedBoxTargetState : MachineState :=
  { program := deletedBoxAfterProgram
    control := .code deletedBoxAfter
    env := liveEnv }

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

/-- Kernel regression for the allocating bug-card fixture: evaluating the
well-formed dead constructor may add a source heap cell, but the resulting
runtime is still related to the unchanged empty target runtime because the
constructor result is absent from all live roots. -/
theorem deadCtorEvalPreservesReachableRuntime :
    ∃ nextRuntime value,
      evalLetValue neutralLiveState deadCtorDecl =
          .ok (nextRuntime, .value value) ∧
      ShadowRuntimeRel emptyAddressRenaming nextRuntime
        ({} : RuntimeState) [] [] := by
  have base : ShadowRuntimeRel emptyAddressRenaming
      neutralLiveState.runtime ({} : RuntimeState) [] [] := by
    simpa [neutralLiveState] using emptyRuntime_shadowRelated
  have argumentsResult :
      evalArgs neutralLiveState.env #[.fvar live] = .ok #[.erased] := by
    simp [neutralLiveState, liveEnv, evalArgs, evalArg]
    rfl
  have arity : (#[.erased] : Array Value).size = oneFieldInfo.size := by
    rfl
  simpa [deadCtorDecl, letDecl] using
    (base.evalLetValueCtorLeftGarbage
      (state := neutralLiveState) (fvarId := dead)
      (binderName := dead.name) (type := objType) (info := oneFieldInfo)
      (arguments := #[.fvar live]) (values := #[.erased])
      argumentsResult arity)

def allocatingSourceInnerState : MachineState :=
  { program := allocatingBeforeProgram
    control := .code (.let deadCtorDecl (.return live))
    env := liveEnv }

def allocatingTargetInnerState : MachineState :=
  { program := allocatingAfterProgram
    control := .code (.return live)
    env := liveEnv }

theorem returnLiveShadowGraph :
    ShadowCodeGraph 3 neutralUsed (.return live) (.return live) := by
  refine ⟨0, {}, neutralUsed, by omega, ?_, .refl neutralUsed⟩
  simp [shadowCode?, neutralUsed]

theorem returnLiveShadowGraph4 :
    ShadowCodeGraph 4 neutralUsed (.return live) (.return live) := by
  refine ⟨0, {}, neutralUsed, by omega, ?_, .refl neutralUsed⟩
  simp [shadowCode?, neutralUsed]

theorem returnLiveShadowGraph2 :
    ShadowCodeGraph 2 neutralUsed (.return live) (.return live) := by
  refine ⟨0, {}, neutralUsed, by omega, ?_, .refl neutralUsed⟩
  simp [shadowCode?, neutralUsed]

theorem deletedUSizeScalarShadowGraph :
    ShadowCodeGraph 4 neutralUsed
      (.uset dead 0 usizeField <|
        .sset dead 8 0 scalarField u8Type <| .return live)
      (.return live) := by
  exact ⟨3, {}, neutralUsed, by omega,
    deletedUSizeScalarShadowRun, .refl neutralUsed⟩

theorem deletedScalarShadowGraph :
    ShadowCodeGraph 4 neutralUsed
      (.sset dead 8 0 scalarField u8Type <| .return live)
      (.return live) := by
  exact ⟨2, {}, neutralUsed, by omega,
    deletedScalarShadowRun, .refl neutralUsed⟩

theorem liveEnvReachableRelated :
    EnvRelOn emptyAddressRenaming neutralUsed liveEnv liveEnv := by
  intro fvarId member
  have same : live = fvarId := by
    simpa [neutralUsed] using member
  subst fvarId
  exact .some .erased

theorem deletedWriteEnvReachableRelated :
    EnvRelOn emptyAddressRenaming neutralUsed deletedWriteSourceEnv liveEnv := by
  unfold deletedWriteSourceEnv
  apply EnvRelOn.bindLeft_of_absent
  · apply EnvRelOn.bindLeft_of_absent
    · apply EnvRelOn.bindLeft_of_absent liveEnvReachableRelated
      native_decide
    · native_decide
  · native_decide

theorem deletedReuseNoneEnvReachableRelated :
    EnvRelOn emptyAddressRenaming neutralUsed deletedReuseNoneSourceEnv
      liveEnv := by
  unfold deletedReuseNoneSourceEnv
  apply EnvRelOn.bindLeft_of_absent
  · apply EnvRelOn.bindLeft_of_absent liveEnvReachableRelated
    native_decide
  · native_decide

theorem deletedReuseSomeEnvReachableRelated :
    EnvRelOn emptyAddressRenaming neutralUsed deletedReuseSomeSourceEnv
      liveEnv := by
  unfold deletedReuseSomeSourceEnv
  apply EnvRelOn.bindLeft_of_absent
  · apply EnvRelOn.bindLeft_of_absent liveEnvReachableRelated
    native_decide
  · native_decide

theorem deletedReuseNoneRuntimeRelated :
    ShadowRuntimeRel emptyAddressRenaming
      deletedReuseNoneSourceState.runtime deletedReuseTargetState.runtime
      (envRootsOn neutralUsed deletedReuseNoneSourceState.env)
      (envRootsOn neutralUsed deletedReuseTargetState.env) := by
  simpa [deletedReuseNoneSourceState, deletedReuseTargetState] using
    emptyRuntime_shadowRelated_of_roots
      (envRootsOn_related deletedReuseNoneEnvReachableRelated)

theorem deletedReuseSomeRuntimeRelated :
    ShadowRuntimeRel emptyAddressRenaming
      deletedReuseSomeSourceState.runtime deletedReuseTargetState.runtime
      (envRootsOn neutralUsed deletedReuseSomeSourceState.env)
      (envRootsOn neutralUsed deletedReuseTargetState.env) := by
  have base := emptyRuntime_shadowRelated_of_roots
    (envRootsOn_related deletedReuseSomeEnvReachableRelated)
  simpa [deletedReuseSomeSourceState, deletedReuseTargetState,
    deletedWriteSourceRuntime] using
      base.allocLeftGarbage (.ctor deletedWriteObject) false

theorem deletedReuseSomeDestinationUnreachable :
    ¬Reachable deletedReuseSomeSourceState.runtime.heap
      (runtimeRoots deletedReuseSomeSourceState.runtime
        (envRootsOn neutralUsed deletedReuseSomeSourceState.env)) 0 := by
  apply deletedReuseSomeRuntimeRelated.leftUnreachable_of_forward_unmapped
  simp [emptyAddressRenaming]

theorem deletedResetEnvReachableRelated :
    EnvRelOn emptyAddressRenaming neutralUsed deletedResetSourceEnv
      liveEnv := by
  unfold deletedResetSourceEnv
  apply EnvRelOn.bindLeft_of_absent liveEnvReachableRelated
  native_decide

theorem deletedResetRuntimeRelated :
    ShadowRuntimeRel emptyAddressRenaming
      deletedResetSourceState.runtime deletedResetTargetState.runtime
      (envRootsOn neutralUsed deletedResetSourceState.env)
      (envRootsOn neutralUsed deletedResetTargetState.env) := by
  have base := emptyRuntime_shadowRelated_of_roots
    (envRootsOn_related deletedResetEnvReachableRelated)
  simpa [deletedResetSourceState, deletedResetTargetState,
    deletedResetSourceRuntime] using
      base.allocLeftGarbage (.ctor deletedResetObject) false

theorem deletedResetDestinationUnreachable :
    ¬Reachable deletedResetSourceState.runtime.heap
      (runtimeRoots deletedResetSourceState.runtime
        (envRootsOn neutralUsed deletedResetSourceState.env)) 0 := by
  apply deletedResetRuntimeRelated.leftUnreachable_of_forward_unmapped
  simp [emptyAddressRenaming]

theorem deletedResetSetCellEffect :
    setCell deletedResetSourceRuntime 0 deletedResetReplacementCell =
      .ok deletedResetNextRuntime := by
  rfl

theorem deletedResetEffect :
    reset deletedResetSourceRuntime 1 (.object (.heap 0)) =
      .ok (deletedResetNextRuntime, .reuseToken (some 0)) := by
  rfl

theorem deletedResetRuntimeFrame :
    RuntimeReachableFrame deletedResetSourceState.runtime
      deletedResetNextRuntime
      (runtimeRoots deletedResetSourceState.runtime
        (envRootsOn neutralUsed deletedResetSourceState.env)) := by
  have found : findCell? deletedResetSourceState.runtime.heap 0 =
      some ({ object := .ctor deletedResetObject } : HeapCell) := by
    rfl
  rcases setCell_reachableFrame_of_unreachable found
      deletedResetDestinationUnreachable
      deletedResetRuntimeRelated.leftHeapFresh deletedResetReplacementCell with
    ⟨after, effect, frame⟩
  have known : setCell deletedResetSourceState.runtime 0
      deletedResetReplacementCell = .ok deletedResetNextRuntime := by
    simpa [deletedResetSourceState] using deletedResetSetCellEffect
  rw [known] at effect
  injection effect with same
  subst after
  exact frame

theorem deletedResetReady :
    DeletedResetReadyAt deletedResetSourceState
      (runtimeRoots deletedResetSourceState.runtime
        (envRootsOn neutralUsed deletedResetSourceState.env))
      1 resetObjectVar := by
  apply DeletedResetReadyAt.mk (.object (.heap 0))
    (.reuseToken (some 0)) deletedResetNextRuntime
  · simp [deletedResetSourceState, deletedResetSourceEnv,
      lookupValue, Impure.bind, lookup, resetObjectVar]
  · simpa [deletedResetSourceState] using deletedResetEffect
  · exact deletedResetRuntimeFrame

theorem deletedPapEnvReachableRelated :
    EnvRelOn emptyAddressRenaming neutralUsed deletedPapSourceEnv liveEnv := by
  unfold deletedPapSourceEnv
  apply EnvRelOn.bindLeft_of_absent liveEnvReachableRelated
  native_decide

theorem deletedPapRuntimeRelated :
    ShadowRuntimeRel emptyAddressRenaming
      deletedPapSourceState.runtime deletedPapTargetState.runtime
      (envRootsOn neutralUsed deletedPapSourceState.env)
      (envRootsOn neutralUsed deletedPapTargetState.env) := by
  simpa [deletedPapSourceState, deletedPapTargetState] using
    emptyRuntime_shadowRelated_of_roots
      (envRootsOn_related deletedPapEnvReachableRelated)

theorem deletedPapReady :
    DeletedPapReadyAt deletedPapSourceState `first #[.fvar papArgVar] := by
  apply DeletedPapReadyAt.mk firstDecl #[.erased]
  · simp [deletedPapSourceState, deletedPapSourceEnv, evalArgs, evalArg,
      Impure.bind, lookup, papArgVar]
    rfl
  · rfl
  · simp [firstDecl, decl]

theorem deletedBoxEnvReachableRelated :
    EnvRelOn emptyAddressRenaming neutralUsed deletedBoxSourceEnv liveEnv := by
  unfold deletedBoxSourceEnv
  apply EnvRelOn.bindLeft_of_absent liveEnvReachableRelated
  native_decide

theorem deletedBoxRuntimeRelated :
    ShadowRuntimeRel emptyAddressRenaming
      deletedBoxSourceState.runtime deletedBoxTargetState.runtime
      (envRootsOn neutralUsed deletedBoxSourceState.env)
      (envRootsOn neutralUsed deletedBoxTargetState.env) := by
  simpa [deletedBoxSourceState, deletedBoxTargetState] using
    emptyRuntime_shadowRelated_of_roots
      (envRootsOn_related deletedBoxEnvReachableRelated)

theorem deletedBoxReady :
    DeletedBoxReadyAt deletedBoxSourceState boxInputVar := by
  apply DeletedBoxReadyAt.scalar (.uint64 18446744073709551615)
  simp [deletedBoxSourceState, deletedBoxSourceEnv,
    lookupValue, Impure.bind, lookup, boxInputVar]

theorem deletedBoxUnifiedReady :
    DeletedLetReadyAt deletedBoxSourceState
      (runtimeRoots deletedBoxSourceState.runtime
        (envRootsOn neutralUsed deletedBoxSourceState.env ++ []))
      deadBoxDecl := by
  unfold deadBoxDecl letDecl
  exact .box dead dead.name objType u64Type boxInputVar deletedBoxReady

theorem deletedReuseNoneReady :
    DeletedReuseReadyAt deletedReuseNoneSourceState
      (runtimeRoots deletedReuseNoneSourceState.runtime
        (envRootsOn neutralUsed deletedReuseNoneSourceState.env))
      reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] := by
  apply DeletedReuseReadyAt.none #[.erased]
  · simp [deletedReuseNoneSourceState, deletedReuseNoneSourceEnv,
      lookupValue, Impure.bind, lookup, reuseTokenVar, reuseArgVar]
  · simp [deletedReuseNoneSourceState, deletedReuseNoneSourceEnv,
      evalArgs, evalArg, Impure.bind, lookup, reuseTokenVar, reuseArgVar]
    rfl
  · rfl

theorem deletedReuseSomeReady :
    DeletedReuseReadyAt deletedReuseSomeSourceState
      (runtimeRoots deletedReuseSomeSourceState.runtime
        (envRootsOn neutralUsed deletedReuseSomeSourceState.env))
      reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] := by
  apply DeletedReuseReadyAt.some 0
    ({ object := .ctor deletedWriteObject } : HeapCell)
    deletedWriteObject #[.erased]
  · simp [deletedReuseSomeSourceState, deletedReuseSomeSourceEnv,
      lookupValue, Impure.bind, lookup, reuseTokenVar, reuseArgVar]
  · simp [deletedReuseSomeSourceState, deletedReuseSomeSourceEnv,
      evalArgs, evalArg, Impure.bind, lookup, reuseTokenVar, reuseArgVar]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact deletedReuseSomeDestinationUnreachable

theorem deletedWriteRuntimeRelated :
    ShadowRuntimeRel emptyAddressRenaming deletedWriteSourceRuntime
      ({} : RuntimeState)
      (envRootsOn neutralUsed deletedWriteSourceEnv)
      (envRootsOn neutralUsed liveEnv) := by
  have base := emptyRuntime_shadowRelated_of_roots
    (envRootsOn_related deletedWriteEnvReachableRelated)
  simpa [deletedWriteSourceRuntime] using
    base.allocLeftGarbage (.ctor deletedWriteObject) false

theorem deletedWriteDestinationUnreachable :
    ¬Reachable deletedWriteSourceRuntime.heap
      (runtimeRoots deletedWriteSourceRuntime
        (envRootsOn neutralUsed deletedWriteSourceEnv)) 0 := by
  apply deletedWriteRuntimeRelated.leftUnreachable_of_forward_unmapped
  simp [emptyAddressRenaming]

theorem deletedObjectSetReady :
    DeletedObjectSetReadyAt deletedObjectSetSourceState
      (runtimeRoots deletedObjectSetSourceState.runtime
        (envRootsOn neutralUsed deletedObjectSetSourceState.env))
      dead 0 .erased := by
  refine ⟨0, ({ object := .ctor deletedWriteObject } : HeapCell),
    deletedWriteObject, .erased, ?_, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simp [deletedObjectSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl
  · simp [deletedWriteObject]
  · simpa [deletedObjectSetSourceState] using
      deletedWriteDestinationUnreachable

theorem deletedUSizeSetReady :
    DeletedUSizeSetReadyAt deletedUSizeSetSourceState
      (runtimeRoots deletedUSizeSetSourceState.runtime
        (envRootsOn neutralUsed deletedUSizeSetSourceState.env))
      dead 0 usizeField := by
  refine ⟨0, ({ object := .ctor deletedWriteObject } : HeapCell),
    deletedWriteObject, 7, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp [deletedUSizeSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · simp [deletedUSizeSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl
  · simp [deletedWriteObject]
  · simpa [deletedUSizeSetSourceState] using
      deletedWriteDestinationUnreachable

theorem deletedScalarSetReady :
    DeletedScalarSetReadyAt deletedScalarSetSourceState
      (runtimeRoots deletedScalarSetSourceState.runtime
        (envRootsOn neutralUsed deletedScalarSetSourceState.env))
      dead scalarField := by
  refine ⟨0, ({ object := .ctor deletedWriteObject } : HeapCell),
    deletedWriteObject, .uint8 9, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp [deletedScalarSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · simp [deletedScalarSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl
  · simpa [deletedScalarSetSourceState] using
      deletedWriteDestinationUnreachable

/-- The first mutation in the closed regression takes one source step while
the transformed target stutters at the live return. -/
theorem deletedObjectSetSourceOnlyMachineStep :
    ∃ nextRuntime,
      let sourceAfter := {
        deletedObjectSetSourceState with
        runtime := nextRuntime
        control := .code (.uset dead 0 usizeField <|
          .sset dead 8 0 scalarField u8Type <| .return live) }
      coreStep deletedObjectSetSourceState = .next sourceAfter ∧
        ReachableMachineRelated 4 emptyAddressRenaming sourceAfter
          deletedWritesTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 4)
      deletedObjectSetSourceState.program deletedWritesTargetState.program := by
    simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramShadowRelated
  have frames : ReachableFramesRelated 4 emptyAddressRenaming
      deletedObjectSetSourceState.frames deletedWritesTargetState.frames [] [] := by
    exact .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedObjectSetSourceState.env deletedWritesTargetState.env := by
    simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
      deletedWriteEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedObjectSetSourceState.runtime deletedWritesTargetState.runtime
      (envRootsOn neutralUsed deletedObjectSetSourceState.env ++ [])
      (envRootsOn neutralUsed deletedWritesTargetState.env ++ []) := by
    simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated
  have progress := coreStep_deletedObjectSet_of_ready
    (sourceState := deletedObjectSetSourceState)
    (targetState := deletedWritesTargetState)
    (sourceContinuation := .uset dead 0 usizeField <|
      .sset dead 8 0 scalarField u8Type <| .return live)
    (targetContinuation := .return live)
    programs frames deletedUSizeScalarShadowGraph
    (ShadowJoinEnvRelated.empty 4 neutralUsed) env runtime
    (by simpa using deletedObjectSetReady)
  simpa [deletedObjectSetSourceState, deletedWritesTargetState,
    deletedWritesBefore, deletedWritesAfter, withCodeControl] using progress

theorem deletedUSizeSetSourceOnlyMachineStep :
    ∃ nextRuntime,
      let sourceAfter := {
        deletedUSizeSetSourceState with
        runtime := nextRuntime
        control := .code (.sset dead 8 0 scalarField u8Type <| .return live) }
      coreStep deletedUSizeSetSourceState = .next sourceAfter ∧
        ReachableMachineRelated 4 emptyAddressRenaming sourceAfter
          deletedWritesTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 4)
      deletedUSizeSetSourceState.program deletedWritesTargetState.program := by
    simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramShadowRelated
  have frames : ReachableFramesRelated 4 emptyAddressRenaming
      deletedUSizeSetSourceState.frames deletedWritesTargetState.frames [] [] := by
    exact .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedUSizeSetSourceState.env deletedWritesTargetState.env := by
    simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
      deletedWriteEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedUSizeSetSourceState.runtime deletedWritesTargetState.runtime
      (envRootsOn neutralUsed deletedUSizeSetSourceState.env ++ [])
      (envRootsOn neutralUsed deletedWritesTargetState.env ++ []) := by
    simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated
  have progress := coreStep_deletedUSizeSet_of_ready
    (sourceState := deletedUSizeSetSourceState)
    (targetState := deletedWritesTargetState)
    (sourceContinuation := .sset dead 8 0 scalarField u8Type <| .return live)
    (targetContinuation := .return live)
    programs frames deletedScalarShadowGraph
    (ShadowJoinEnvRelated.empty 4 neutralUsed) env runtime
    (by simpa using deletedUSizeSetReady)
  simpa [deletedUSizeSetSourceState, deletedWritesTargetState,
    deletedWritesAfter, withCodeControl] using progress

theorem deletedScalarSetSourceOnlyMachineStep :
    ∃ nextRuntime,
      let sourceAfter := {
        deletedScalarSetSourceState with
        runtime := nextRuntime
        control := .code (.return live) }
      coreStep deletedScalarSetSourceState = .next sourceAfter ∧
        ReachableMachineRelated 4 emptyAddressRenaming sourceAfter
          deletedWritesTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 4)
      deletedScalarSetSourceState.program deletedWritesTargetState.program := by
    simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramShadowRelated
  have frames : ReachableFramesRelated 4 emptyAddressRenaming
      deletedScalarSetSourceState.frames deletedWritesTargetState.frames [] [] := by
    exact .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedScalarSetSourceState.env deletedWritesTargetState.env := by
    simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
      deletedWriteEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedScalarSetSourceState.runtime deletedWritesTargetState.runtime
      (envRootsOn neutralUsed deletedScalarSetSourceState.env ++ [])
      (envRootsOn neutralUsed deletedWritesTargetState.env ++ []) := by
    simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated
  have progress := coreStep_deletedScalarSet_of_ready
    (sourceState := deletedScalarSetSourceState)
    (targetState := deletedWritesTargetState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    programs frames returnLiveShadowGraph4
    (ShadowJoinEnvRelated.empty 4 neutralUsed) env runtime
    (width := 8) (offset := 0) (type := u8Type)
    (by simpa using deletedScalarSetReady)
  simpa [deletedScalarSetSourceState, deletedWritesTargetState,
    deletedWritesAfter, withCodeControl] using progress

/-- A deleted failed-token reuse performs its constructor allocation only on
the source; the dead result and allocation remain outside all live roots. -/
theorem deletedReuseNoneSourceOnlyMachineStep :
    ∃ nextRuntime value,
      let sourceAfter := {
        deletedReuseNoneSourceState with
        runtime := nextRuntime
        env := bind deletedReuseNoneSourceState.env dead value
        control := .code (.return live) }
      coreStep deletedReuseNoneSourceState = .next sourceAfter ∧
        ReachableMachineRelated 2 emptyAddressRenaming sourceAfter
          deletedReuseTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 2)
      deletedReuseNoneSourceState.program deletedReuseTargetState.program := by
    simpa [deletedReuseNoneSourceState, deletedReuseTargetState] using
      deletedReuseProgramShadowRelated
  have frames : ReachableFramesRelated 2 emptyAddressRenaming
      deletedReuseNoneSourceState.frames deletedReuseTargetState.frames [] [] :=
    .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedReuseNoneSourceState.env deletedReuseTargetState.env := by
    simpa [deletedReuseNoneSourceState, deletedReuseTargetState] using
      deletedReuseNoneEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedReuseNoneSourceState.runtime deletedReuseTargetState.runtime
      (envRootsOn neutralUsed deletedReuseNoneSourceState.env ++ [])
      (envRootsOn neutralUsed deletedReuseTargetState.env ++ []) := by
    simpa using deletedReuseNoneRuntimeRelated
  have progress := coreStep_deletedReuse_of_ready
    (sourceState := deletedReuseNoneSourceState)
    (targetState := deletedReuseTargetState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    (fvarId := dead) (binderName := dead.name) (type := objType)
    (token := reuseTokenVar) (info := oneFieldInfo) (updateHeader := true)
    (arguments := #[.fvar reuseArgVar])
    programs frames returnLiveShadowGraph2
    (ShadowJoinEnvRelated.empty 2 neutralUsed) env (by native_decide)
    runtime (by simpa using deletedReuseNoneReady)
  simpa [deletedReuseNoneSourceState, deletedReuseTargetState,
    deletedReuseBefore, deletedReuseAfter, deadReuseDecl, letDecl] using progress

/-- A deleted concrete-token reuse overwrites only its unreachable owned cell
and likewise advances the source while the target stutters. -/
theorem deletedReuseSomeSourceOnlyMachineStep :
    ∃ nextRuntime value,
      let sourceAfter := {
        deletedReuseSomeSourceState with
        runtime := nextRuntime
        env := bind deletedReuseSomeSourceState.env dead value
        control := .code (.return live) }
      coreStep deletedReuseSomeSourceState = .next sourceAfter ∧
        ReachableMachineRelated 2 emptyAddressRenaming sourceAfter
          deletedReuseTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 2)
      deletedReuseSomeSourceState.program deletedReuseTargetState.program := by
    simpa [deletedReuseSomeSourceState, deletedReuseTargetState] using
      deletedReuseProgramShadowRelated
  have frames : ReachableFramesRelated 2 emptyAddressRenaming
      deletedReuseSomeSourceState.frames deletedReuseTargetState.frames [] [] :=
    .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedReuseSomeSourceState.env deletedReuseTargetState.env := by
    simpa [deletedReuseSomeSourceState, deletedReuseTargetState] using
      deletedReuseSomeEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedReuseSomeSourceState.runtime deletedReuseTargetState.runtime
      (envRootsOn neutralUsed deletedReuseSomeSourceState.env ++ [])
      (envRootsOn neutralUsed deletedReuseTargetState.env ++ []) := by
    simpa using deletedReuseSomeRuntimeRelated
  have progress := coreStep_deletedReuse_of_ready
    (sourceState := deletedReuseSomeSourceState)
    (targetState := deletedReuseTargetState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    (fvarId := dead) (binderName := dead.name) (type := objType)
    (token := reuseTokenVar) (info := oneFieldInfo) (updateHeader := true)
    (arguments := #[.fvar reuseArgVar])
    programs frames returnLiveShadowGraph2
    (ShadowJoinEnvRelated.empty 2 neutralUsed) env (by native_decide)
    runtime (by simpa using deletedReuseSomeReady)
  simpa [deletedReuseSomeSourceState, deletedReuseTargetState,
    deletedReuseBefore, deletedReuseAfter, deadReuseDecl, letDecl] using progress

/-- The concrete reset clears and releases an unreachable constructor field.
Every cell reachable from the live return remains fixed, so the target can
delete the reset and stutter. -/
theorem deletedResetSourceOnlyMachineStep :
    ∃ nextRuntime token,
      let sourceAfter := {
        deletedResetSourceState with
        runtime := nextRuntime
        env := bind deletedResetSourceState.env dead token
        control := .code (.return live) }
      coreStep deletedResetSourceState = .next sourceAfter ∧
        ReachableMachineRelated 2 emptyAddressRenaming sourceAfter
          deletedResetTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 2)
      deletedResetSourceState.program deletedResetTargetState.program := by
    simpa [deletedResetSourceState, deletedResetTargetState] using
      deletedResetProgramShadowRelated
  have frames : ReachableFramesRelated 2 emptyAddressRenaming
      deletedResetSourceState.frames deletedResetTargetState.frames [] [] :=
    .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedResetSourceState.env deletedResetTargetState.env := by
    simpa [deletedResetSourceState, deletedResetTargetState] using
      deletedResetEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedResetSourceState.runtime deletedResetTargetState.runtime
      (envRootsOn neutralUsed deletedResetSourceState.env ++ [])
      (envRootsOn neutralUsed deletedResetTargetState.env ++ []) := by
    simpa using deletedResetRuntimeRelated
  have progress := coreStep_deletedReset_of_ready
    (sourceState := deletedResetSourceState)
    (targetState := deletedResetTargetState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    (fvarId := dead) (binderName := dead.name) (type := objType)
    (count := 1) (object := resetObjectVar)
    programs frames returnLiveShadowGraph2
    (ShadowJoinEnvRelated.empty 2 neutralUsed) env (by native_decide)
    runtime (by simpa using deletedResetReady)
  simpa [deletedResetSourceState, deletedResetTargetState,
    deletedResetBefore, deletedResetAfter, deadResetDecl, letDecl] using progress

/-- The large natural crosses the tagged-immediate boundary and allocates a
heap object, yet deleting its dead binding is still a valid source-only step. -/
theorem deletedLargeNatSourceOnlyMachineStep :
    ∃ nextRuntime value,
      let sourceAfter := {
        deletedLargeNatSourceState with
        runtime := nextRuntime
        env := bind deletedLargeNatSourceState.env dead value
        control := .code (.return live) }
      coreStep deletedLargeNatSourceState = .next sourceAfter ∧
        ReachableMachineRelated 2 emptyAddressRenaming sourceAfter
          deletedLargeNatTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 2)
      deletedLargeNatSourceState.program deletedLargeNatTargetState.program := by
    simpa [deletedLargeNatSourceState, deletedLargeNatTargetState] using
      deletedLargeNatProgramShadowRelated
  have frames : ReachableFramesRelated 2 emptyAddressRenaming
      deletedLargeNatSourceState.frames deletedLargeNatTargetState.frames [] [] :=
    .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedLargeNatSourceState.env deletedLargeNatTargetState.env := by
    simpa [deletedLargeNatSourceState, deletedLargeNatTargetState] using
      liveEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedLargeNatSourceState.runtime deletedLargeNatTargetState.runtime
      (envRootsOn neutralUsed deletedLargeNatSourceState.env ++ [])
      (envRootsOn neutralUsed deletedLargeNatTargetState.env ++ []) := by
    simpa [deletedLargeNatSourceState, deletedLargeNatTargetState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related liveEnvReachableRelated)
  have progress := coreStep_deletedLiteral_reachableRelated
    (sourceState := deletedLargeNatSourceState)
    (targetState := deletedLargeNatTargetState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    (fvarId := dead) (binderName := dead.name) (type := objType)
    (literalValue := .nat 9223372036854775808)
    programs frames returnLiveShadowGraph2
    (ShadowJoinEnvRelated.empty 2 neutralUsed) env (by native_decide) runtime
  simpa [deletedLargeNatSourceState, deletedLargeNatTargetState,
    deletedLargeNatBefore, deletedLargeNatAfter, deadLargeNatDecl, letDecl]
    using progress

/-- The complete two-declaration regression resolves `first`, fixes one of
its two parameters, allocates an unreachable closure, and stutters the target. -/
theorem deletedPapSourceOnlyMachineStep :
    ∃ nextRuntime value,
      let sourceAfter := {
        deletedPapSourceState with
        runtime := nextRuntime
        env := bind deletedPapSourceState.env dead value
        control := .code (.return live) }
      coreStep deletedPapSourceState = .next sourceAfter ∧
        ReachableMachineRelated 2 emptyAddressRenaming sourceAfter
          deletedPapTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 2)
      deletedPapSourceState.program deletedPapTargetState.program := by
    simpa [deletedPapSourceState, deletedPapTargetState] using
      deletedPapProgramShadowRelated
  have frames : ReachableFramesRelated 2 emptyAddressRenaming
      deletedPapSourceState.frames deletedPapTargetState.frames [] [] := .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedPapSourceState.env deletedPapTargetState.env := by
    simpa [deletedPapSourceState, deletedPapTargetState] using
      deletedPapEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedPapSourceState.runtime deletedPapTargetState.runtime
      (envRootsOn neutralUsed deletedPapSourceState.env ++ [])
      (envRootsOn neutralUsed deletedPapTargetState.env ++ []) := by
    simpa using deletedPapRuntimeRelated
  have progress := coreStep_deletedPap_of_ready
    (sourceState := deletedPapSourceState)
    (targetState := deletedPapTargetState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    (fvarId := dead) (binderName := dead.name) (type := objType)
    (name := `first) (arguments := #[.fvar papArgVar])
    programs frames returnLiveShadowGraph2
    (ShadowJoinEnvRelated.empty 2 neutralUsed) env (by native_decide)
    runtime deletedPapReady
  simpa [deletedPapSourceState, deletedPapTargetState,
    deletedPapBefore, deletedPapAfter, deadPapDecl, letDecl] using progress

/-- A large scalar box allocates one source-only heap cell.  Because the
binding is dead and the cell is absent from every live root, the target may
stutter at the retained return. -/
theorem deletedBoxSourceOnlyMachineStep :
    ∃ nextRuntime value,
      let sourceAfter := {
        deletedBoxSourceState with
        runtime := nextRuntime
        env := bind deletedBoxSourceState.env dead value
        control := .code (.return live) }
      coreStep deletedBoxSourceState = .next sourceAfter ∧
        ReachableMachineRelated 2 emptyAddressRenaming sourceAfter
          deletedBoxTargetState := by
  have programs : ProgramRelated (ShadowCodeRelated 2)
      deletedBoxSourceState.program deletedBoxTargetState.program := by
    simpa [deletedBoxSourceState, deletedBoxTargetState] using
      deletedBoxProgramShadowRelated
  have frames : ReachableFramesRelated 2 emptyAddressRenaming
      deletedBoxSourceState.frames deletedBoxTargetState.frames [] [] := .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedBoxSourceState.env deletedBoxTargetState.env := by
    simpa [deletedBoxSourceState, deletedBoxTargetState] using
      deletedBoxEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedBoxSourceState.runtime deletedBoxTargetState.runtime
      (envRootsOn neutralUsed deletedBoxSourceState.env ++ [])
      (envRootsOn neutralUsed deletedBoxTargetState.env ++ []) := by
    simpa using deletedBoxRuntimeRelated
  have progress := coreStep_deletedLet_of_ready
    (sourceState := deletedBoxSourceState)
    (targetState := deletedBoxTargetState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    (declaration := deadBoxDecl)
    programs frames returnLiveShadowGraph2
    (ShadowJoinEnvRelated.empty 2 neutralUsed) env (by native_decide)
    runtime deletedBoxUnifiedReady
  simpa [deletedBoxSourceState, deletedBoxTargetState,
    deletedBoxBefore, deletedBoxAfter, deadBoxDecl, letDecl] using progress

/-- The semantic `Step` interface sees the same deletion as a genuine
non-lockstep match: the source advances and the target takes the reflexive
path while the reachable relation is preserved. -/
theorem deletedBoxStepMatchesTargetStutter (externals : ExternalSpec)
    {sourceAfter : MachineState}
    (step : Step externals deletedBoxSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedBoxTargetState targetAfter ∧
      ReachableMachineRelated 2 emptyAddressRenaming
        sourceAfter targetAfter := by
  have programs : ProgramRelated (ShadowCodeRelated 2)
      deletedBoxSourceState.program deletedBoxTargetState.program := by
    simpa [deletedBoxSourceState, deletedBoxTargetState] using
      deletedBoxProgramShadowRelated
  have frames : ReachableFramesRelated 2 emptyAddressRenaming
      deletedBoxSourceState.frames deletedBoxTargetState.frames [] [] := .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      deletedBoxSourceState.env deletedBoxTargetState.env := by
    simpa [deletedBoxSourceState, deletedBoxTargetState] using
      deletedBoxEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      deletedBoxSourceState.runtime deletedBoxTargetState.runtime
      (envRootsOn neutralUsed deletedBoxSourceState.env ++ [])
      (envRootsOn neutralUsed deletedBoxTargetState.env ++ []) := by
    simpa using deletedBoxRuntimeRelated
  have sourceStep : Step externals
      { deletedBoxSourceState with
        control := .code (.let deadBoxDecl (.return live)) }
      sourceAfter := by
    simpa [deletedBoxSourceState, deletedBoxBefore] using step
  have matched := match_deletedLetStep_of_ready
    (sourceState := deletedBoxSourceState)
    (targetState := deletedBoxTargetState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    (declaration := deadBoxDecl)
    programs frames returnLiveShadowGraph2
    (ShadowJoinEnvRelated.empty 2 neutralUsed) env (by native_decide)
    runtime deletedBoxUnifiedReady sourceStep
  simpa [deletedBoxTargetState, deletedBoxAfter] using matched

/-- The source-only allocation followed by the retained return reaches
related yielded states, and the shared terminal projection ignores precisely
the unreachable boxed cell. -/
theorem deletedBoxReturnObservationRelated :
    ∃ nextRuntime boxValue targetValue,
      let sourceAfterLet := {
        deletedBoxSourceState with
        runtime := nextRuntime
        env := bind deletedBoxSourceState.env dead boxValue
        control := .code (.return live) }
      let sourceYielded := {
        sourceAfterLet with control := .yielded .erased }
      let targetYielded := {
        deletedBoxTargetState with control := .yielded targetValue }
      coreStep deletedBoxSourceState = .next sourceAfterLet ∧
        coreStep sourceAfterLet = .next sourceYielded ∧
        coreStep deletedBoxTargetState = .next targetYielded ∧
        ReachableMachineRelated 2 emptyAddressRenaming
          sourceYielded targetYielded ∧
        ObservationRel
          (observe sourceYielded (.returned .erased))
          (observe targetYielded (.returned targetValue)) := by
  rcases deletedBoxSourceOnlyMachineStep with
    ⟨nextRuntime, boxValue, firstStep, afterRelated⟩
  let sourceAfterLet : MachineState := {
    deletedBoxSourceState with
    runtime := nextRuntime
    env := bind deletedBoxSourceState.env dead boxValue
    control := .code (.return live) }
  have firstStep' : coreStep deletedBoxSourceState = .next sourceAfterLet := by
    simpa [sourceAfterLet] using firstStep
  have afterRelated' : ReachableMachineRelated 2 emptyAddressRenaming
      sourceAfterLet deletedBoxTargetState := by
    simpa [sourceAfterLet] using afterRelated
  have sourceRead : lookup sourceAfterLet.env live = some .erased := by
    simp [sourceAfterLet, deletedBoxSourceState, deletedBoxSourceEnv,
      liveEnv, Impure.bind, lookup, live, dead, boxInputVar]
  rcases afterRelated'.returnStep rfl rfl sourceRead with
    ⟨targetValue, targetRead, values,
      sourceReturn, targetReturn, yieldedRelated⟩
  let sourceYielded : MachineState := {
    sourceAfterLet with control := .yielded .erased }
  let targetYielded : MachineState := {
    deletedBoxTargetState with control := .yielded targetValue }
  have yieldedRelated' : ReachableMachineRelated 2 emptyAddressRenaming
      sourceYielded targetYielded := by
    simpa [sourceYielded, targetYielded] using yieldedRelated
  have observations : ObservationRel
      (observe sourceYielded (.returned .erased))
      (observe targetYielded (.returned targetValue)) := by
    exact yieldedRelated'.yieldedObservation rfl rfl rfl rfl
  refine ⟨nextRuntime, boxValue, targetValue, ?_⟩
  dsimp only
  exact ⟨firstStep', sourceReturn, targetReturn,
    yieldedRelated', observations⟩

/-- End-to-end finite evaluations for the concrete state pair produce
possibly different observations related by reachable semantics. -/
theorem deletedBoxEvaluationsRelated (externals : ExternalSpec) :
    ∃ sourceObservation targetObservation,
      EvaluatesState externals deletedBoxSourceState sourceObservation ∧
        EvaluatesState externals deletedBoxTargetState targetObservation ∧
        ObservationRel sourceObservation targetObservation := by
  rcases deletedBoxReturnObservationRelated with
    ⟨nextRuntime, boxValue, targetValue,
      firstStep, sourceReturn, targetReturn, yieldedRelated, observations⟩
  let sourceAfterLet : MachineState := {
    deletedBoxSourceState with
    runtime := nextRuntime
    env := bind deletedBoxSourceState.env dead boxValue
    control := .code (.return live) }
  let sourceYielded : MachineState := {
    sourceAfterLet with control := .yielded .erased }
  let targetYielded : MachineState := {
    deletedBoxTargetState with control := .yielded targetValue }
  have sourceDone : coreStep sourceYielded =
      .done (observe sourceYielded (.returned .erased)) := by
    simp [sourceYielded, sourceAfterLet, deletedBoxSourceState, coreStep]
  have targetDone : coreStep targetYielded =
      .done (observe targetYielded (.returned targetValue)) := by
    simp [targetYielded, deletedBoxTargetState, coreStep]
  refine ⟨observe sourceYielded (.returned .erased),
    observe targetYielded (.returned targetValue), ?_, ?_, observations⟩
  · exact ⟨2, sourceYielded,
      .step (.internal firstStep) <|
        .step (.internal sourceReturn) (.refl sourceYielded),
      sourceDone⟩
  · exact ⟨1, targetYielded,
      .step (.internal targetReturn) (.refl targetYielded),
      targetDone⟩

/-- The concrete dead-constructor fixture now reaches the generalized
machine relation after one source interpreter step and zero target steps. -/
theorem deadCtorSourceOnlyMachineStep :
    ∃ nextRuntime value,
      let sourceAfter := {
        allocatingSourceInnerState with
        runtime := nextRuntime
        env := bind allocatingSourceInnerState.env dead value
        control := .code (.return live) }
      coreStep allocatingSourceInnerState = .next sourceAfter ∧
        ReachableMachineRelated 3 emptyAddressRenaming sourceAfter
          allocatingTargetInnerState := by
  have roots := envRootsOn_related liveEnvReachableRelated
  have base : ShadowRuntimeRel emptyAddressRenaming
      allocatingSourceInnerState.runtime allocatingTargetInnerState.runtime
      (envRootsOn neutralUsed allocatingSourceInnerState.env)
      (envRootsOn neutralUsed allocatingTargetInnerState.env) := by
    simpa [allocatingSourceInnerState, allocatingTargetInnerState] using
      emptyRuntime_shadowRelated_of_roots roots
  have argumentsResult :
      evalArgs allocatingSourceInnerState.env #[.fvar live] =
        .ok #[.erased] := by
    simp [allocatingSourceInnerState, liveEnv, evalArgs, evalArg]
    rfl
  have arity : (#[.erased] : Array Value).size = oneFieldInfo.size := by
    rfl
  rcases base.evalLetValueCtorLeftGarbage
      (state := allocatingSourceInnerState) (fvarId := dead)
      (binderName := dead.name) (type := objType) (info := oneFieldInfo)
      (arguments := #[.fvar live]) (values := #[.erased])
      argumentsResult arity with
    ⟨nextRuntime, value, evaluated, runtime⟩
  refine ⟨nextRuntime, value, ?_⟩
  have programs : ProgramRelated (ShadowCodeRelated 3)
      allocatingSourceInnerState.program
      allocatingTargetInnerState.program := by
    simpa [allocatingSourceInnerState, allocatingTargetInnerState] using
      allocatingProgramShadowRelated
  have progress := coreStep_deletedLet_reachableRelated
    (sourceState := allocatingSourceInnerState)
    (targetState := allocatingTargetInnerState)
    programs
    (ReachableFramesRelated.nil :
      ReachableFramesRelated 3 emptyAddressRenaming [] [] [] [])
    returnLiveShadowGraph
    (ShadowJoinEnvRelated.empty 3 neutralUsed)
    liveEnvReachableRelated
    (by native_decide)
    evaluated (by simpa using runtime)
  simpa [allocatingSourceInnerState, allocatingTargetInnerState,
    deadCtorDecl, letDecl] using progress

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
