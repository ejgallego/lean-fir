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
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.SimpCaseWellFormed
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
  .uset dead 1 usizeField <|
  .sset dead 8 0 scalarField u8Type <|
  .return live

def deletedWritesAfter : LCNF.Code .impure :=
  .return live

def closedWritesInfo : LCNF.CtorInfo :=
  { name := `Dead.layout, cidx := 0, size := 1, usize := 1, ssize := 8 }

def closedWritesObjectDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.ctor closedWritesInfo #[.erased])

def closedWritesUSizeDecl : LCNF.LetDecl .impure :=
  letDecl usizeField usizeType (.lit (.usize 7))

def closedWritesScalarDecl : LCNF.LetDecl .impure :=
  letDecl scalarField u8Type (.lit (.uint8 9))

/-- Closed compiler-facing counterpart of `deletedWritesBefore`: every
mutation operand is produced in the declaration before the source-only
write chain. -/
def closedWritesBefore : LCNF.Code .impure :=
  .let liveDecl <|
  .let closedWritesObjectDecl <|
  .let closedWritesUSizeDecl <|
  .let closedWritesScalarDecl <|
  deletedWritesBefore

def closedWritesAfter : LCNF.Code .impure :=
  neutralAfter

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

def closedBoxInputDecl : LCNF.LetDecl .impure :=
  letDecl boxInputVar u64Type (.lit (.uint64 18446744073709551615))

def closedBoxBefore : LCNF.Code .impure :=
  .let closedBoxInputDecl deletedBoxBefore

def closedBoxAfter : LCNF.Code .impure :=
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
  checkActualElimDead `elimDeadClosedWrites closedWritesBefore closedWritesAfter
  checkActualElimDead `elimDeadReuse deletedReuseBefore deletedReuseAfter
  checkActualElimDead `elimDeadReset deletedResetBefore deletedResetAfter
  checkActualElimDead `elimDeadLargeNat
    deletedLargeNatBefore deletedLargeNatAfter
  checkActualElimDead `elimDeadPap deletedPapBefore deletedPapAfter
  checkActualElimDead `elimDeadBox deletedBoxBefore deletedBoxAfter
  checkActualElimDead `elimDeadClosedBox closedBoxBefore closedBoxAfter
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

def usedProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main usedBefore] }

def unsafeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main unsafeBefore] }

def allocatingBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main allocatingBefore] }

def allocatingAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main allocatingAfter] }

def deletedWritesBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedWritesBefore] }

def deletedWritesAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main deletedWritesAfter] }

def closedWritesBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main closedWritesBefore] }

def closedWritesAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main closedWritesAfter] }

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

def closedBoxBeforeProgram : ImpureProgram :=
  { decls := #[decl `main #[param live] objType (.code closedBoxBefore)] }

def closedBoxAfterProgram : ImpureProgram :=
  { decls := #[decl `main #[param live] objType (.code closedBoxAfter)] }

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

/-- The closed setup values and all three writes disappear together; only
the live erased result binding remains. -/
theorem closedWritesShadowRun :
    shadowCode? 8 {} closedWritesBefore =
      some (closedWritesAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  have usizeAbsent : usizeField ∉ ({} : UsedLocals).insert live := by
    native_decide
  have scalarAbsent : scalarField ∉ ({} : UsedLocals).insert live := by
    native_decide
  unfold closedWritesBefore
  rw [shadowCode?]
  rw [shadowCode?]
  rw [shadowCode?]
  rw [shadowCode?]
  rw [deletedWritesShadowRun]
  simp [closedWritesAfter, neutralAfter, neutralUsed, deletedWritesAfter, liveDecl,
    closedWritesObjectDecl, closedWritesUSizeDecl, closedWritesScalarDecl,
    letDecl, safeToElim,
    collectLetValue, collectArgs, collectArgList, collectArg,
    liveMember, deadAbsent, usizeAbsent, scalarAbsent]

theorem deletedUSizeScalarShadowRun :
    shadowCode? 3 {}
        (.uset dead 1 usizeField <|
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

theorem closedBoxShadowRun :
    shadowCode? 3 {} closedBoxBefore =
      some (closedBoxAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  have inputAbsent : boxInputVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [closedBoxBefore, closedBoxAfter, closedBoxInputDecl,
    deletedBoxBefore, deadBoxDecl, letDecl, neutralUsed,
    shadowCode?, safeToElim, liveMember, deadAbsent, inputAbsent]

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

theorem closedWritesProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 8)
      closedWritesBeforeProgram closedWritesAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    closedWritesBeforeProgram, closedWritesAfterProgram,
    fixtureDecl, decl, closedWritesShadowRun]

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

theorem closedBoxProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 3)
      closedBoxBeforeProgram closedBoxAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    closedBoxBeforeProgram, closedBoxAfterProgram,
    decl, closedBoxShadowRun]

theorem neutralInitialShadowRelated (entry : Name)
    (arguments : Array Value) :
    ShadowMachineRelated 3
      (initialState neutralBeforeProgram entry arguments)
      (initialState neutralAfterProgram entry arguments) :=
  shadowInitialState_related neutralProgramShadowRelated

/-- The first concrete source-runtime certificate for the strong proof: the
outer live `erased` binding is dynamically safe under either exact compiler
decision.  The actual traversal retains it, but the semantic proof does not
need to recover or replace that proof-relevant witness. -/
theorem neutralBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3 state sourceFrameRoots
      neutralBefore := by
  unfold neutralBefore
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

/-- The same source-only contract at the residual where the pass deletes the
dead `erased` binding. -/
theorem neutralDeadErasedSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3 state sourceFrameRoots
      (.let deadErasedDecl (.return live)) := by
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

/-- Returning itself has no dynamic runtime/ownership premise in an exact
elimDead view. -/
theorem neutralReturnSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3 state sourceFrameRoots
      (.return live) := by
  intro used remaining final targetCode bounded exact subset static
  simp [ExactShadowCodeRuntimeReadyAt]

/-- A finite source execution proof may now discharge machine readiness by
classifying its active control as one of the neutral fixture's three code
positions.  Saved-frame roots remain arbitrary and are handled by the
source-only contract. -/
theorem neutralActiveCodeMachineReadyAt
    (state : MachineState)
    (active :
      state.control = .code neutralBefore ∨
      state.control =
        .code (.let deadErasedDecl (.return live)) ∨
      state.control = .code (.return live)) :
    SourceRuntimeOwnershipMachineReadyAt 3 state := by
  intro sourceFrameRoots sourceCode frames control
  rcases active with outer | inner | ret
  · have codeEq :
        sourceCode = neutralBefore :=
      Control.code.inj (control.symm.trans outer)
    subst sourceCode
    intro used remaining final targetCode bounded exact subset static
    exact neutralBeforeSourceRuntimeReadyAt state sourceFrameRoots
      bounded exact subset static
  · have codeEq :
        sourceCode = .let deadErasedDecl (.return live) :=
      Control.code.inj (control.symm.trans inner)
    subst sourceCode
    intro used remaining final targetCode bounded exact subset static
    exact neutralDeadErasedSourceRuntimeReadyAt state sourceFrameRoots
      bounded exact subset static
  · have codeEq : sourceCode = .return live :=
      Control.code.inj (control.symm.trans ret)
    subst sourceCode
    intro used remaining final targetCode bounded exact subset static
    exact neutralReturnSourceRuntimeReadyAt state sourceFrameRoots
      bounded exact subset static

def neutralEntryFrames (arguments : Array Value) : List Frame :=
  if arguments.isEmpty then [.cache `main] else [.apply arguments]

def neutralSourceOuterState (arguments : Array Value) : MachineState :=
  { program := neutralBeforeProgram
    control := .code neutralBefore
    frames := neutralEntryFrames arguments }

def neutralSourceInnerState (arguments : Array Value) : MachineState :=
  { program := neutralBeforeProgram
    control := .code (.let deadErasedDecl (.return live))
    env := bind [] live .erased
    frames := neutralEntryFrames arguments }

def neutralSourceReturnState (arguments : Array Value) : MachineState :=
  { program := neutralBeforeProgram
    control := .code (.return live)
    env := bind (bind [] live .erased) dead .erased
    frames := neutralEntryFrames arguments }

def neutralSourceYieldedState (arguments : Array Value) : MachineState :=
  { program := neutralBeforeProgram
    control := .yielded .erased
    env := bind (bind [] live .erased) dead .erased
    frames := neutralEntryFrames arguments }

def neutralSourceCachedState : MachineState :=
  { program := neutralBeforeProgram
    control := .yielded .erased
    env := bind (bind [] live .erased) dead .erased
    runtime := ({} : RuntimeState).setGlobal `main .erased }

def neutralSourceInvokingState (arguments : Array Value) : MachineState :=
  { program := neutralBeforeProgram
    control := .invokeValue .erased arguments
    env := bind (bind [] live .erased) dead .erased }

theorem neutralSourceEntryStep (arguments : Array Value) :
    coreStep (initialState neutralBeforeProgram `main arguments) =
      .next (neutralSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, neutralBeforeProgram,
      Program.findDecl?, invokeDecl, neutralSourceOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem neutralSourceOuterStep (arguments : Array Value) :
    coreStep (neutralSourceOuterState arguments) =
      .next (neutralSourceInnerState arguments) := by
  rfl

theorem neutralSourceInnerStep (arguments : Array Value) :
    coreStep (neutralSourceInnerState arguments) =
      .next (neutralSourceReturnState arguments) := by
  rfl

theorem neutralSourceReturnStep (arguments : Array Value) :
    coreStep (neutralSourceReturnState arguments) =
      .next (neutralSourceYieldedState arguments) := by
  simp [coreStep, neutralSourceReturnState, neutralSourceYieldedState,
    lookupValue, Impure.bind, Impure.lookup, live, dead]

theorem neutralSourceYieldedStepEmpty :
    coreStep (neutralSourceYieldedState #[]) =
      .next neutralSourceCachedState := by
  rfl

theorem neutralSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (neutralSourceYieldedState arguments) =
      .next (neutralSourceInvokingState arguments) := by
  simp [coreStep, neutralSourceYieldedState, neutralEntryFrames,
    notEmpty, neutralSourceInvokingState]

/-- Complete finite-state characterization of executions starting at the
neutral source fixture. -/
inductive NeutralSourceReachable (arguments : Array Value) :
    MachineState → Prop where
  | entry :
      NeutralSourceReachable arguments
        (initialState neutralBeforeProgram `main arguments)
  | outer :
      NeutralSourceReachable arguments
        (neutralSourceOuterState arguments)
  | inner :
      NeutralSourceReachable arguments
        (neutralSourceInnerState arguments)
  | ret :
      NeutralSourceReachable arguments
        (neutralSourceReturnState arguments)
  | yielded :
      NeutralSourceReachable arguments
        (neutralSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      NeutralSourceReachable arguments neutralSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      NeutralSourceReachable arguments
        (neutralSourceInvokingState arguments)

theorem predicate_of_step_next
    {predicate : MachineState → Prop}
    (transition : coreStep before = .next expected)
    (expectedReady : predicate expected)
    (step : Step externals before after) :
    predicate after := by
  cases step with
  | internal actual =>
      rw [transition] at actual
      cases actual
      exact expectedReady
  | external actual response =>
      rw [transition] at actual
      contradiction

theorem neutralSourceReachable_step
    (reachable : NeutralSourceReachable arguments before)
    (step : Step externals before after) :
    NeutralSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (neutralSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (neutralSourceOuterStep arguments) .inner step
  | inner =>
      exact predicate_of_step_next
        (neutralSourceInnerStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (neutralSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next neutralSourceYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (neutralSourceYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [neutralSourceCachedState, coreStep] at transition
      | external transition response =>
          simp [neutralSourceCachedState, coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [neutralSourceInvokingState, coreStep, invokeClosure,
            fail] at transition
      | external transition response =>
          simp [neutralSourceInvokingState, coreStep, invokeClosure,
            fail] at transition

theorem neutralSourceReachable_ready
    (state : MachineState)
    (reachable : NeutralSourceReachable arguments state) :
    SourceRuntimeOwnershipMachineReadyAt 3 state := by
  cases reachable with
  | entry =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      exact neutralActiveCodeMachineReadyAt
        (neutralSourceOuterState arguments) (.inl rfl)
  | inner =>
      exact neutralActiveCodeMachineReadyAt
        (neutralSourceInnerState arguments) (.inr (.inl rfl))
  | ret =>
      exact neutralActiveCodeMachineReadyAt
        (neutralSourceReturnState arguments) (.inr (.inr rfl))
  | yielded =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [neutralSourceYieldedState] at control
  | cached empty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [neutralSourceCachedState] at control
  | invoking notEmpty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [neutralSourceInvokingState] at control

/-- The first complete concrete source invariant: every state reachable from
the neutral entry satisfies the dynamic contract consumed by the strong
non-lockstep simulation. -/
theorem neutralSourceRuntimeOwnershipMachineInvariant
    (externals : ExternalSpec) (arguments : Array Value) :
    SourceRuntimeOwnershipMachineInvariant externals 3
      (initialState neutralBeforeProgram `main arguments) :=
  SourceRuntimeOwnershipMachineInvariant.of_inductive
    (NeutralSourceReachable arguments)
    .entry neutralSourceReachable_step neutralSourceReachable_ready

/-- Entry-array form of the complete neutral fixture invariant. -/
theorem neutralSourceRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    SourceRuntimeOwnershipInitialInvariantOn externals 3
      neutralBeforeProgram #[`main] := by
  intro entry member arguments
  have entryEq : entry = `main := by
    simpa using member
  subst entry
  exact neutralSourceRuntimeOwnershipMachineInvariant externals arguments

theorem neutralBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed neutralBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique, neutralBeforeProgram,
          fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [neutralBeforeProgram] at member
      subst declaration
      exact .letE (.letE .ret)
    · intro declaration member
      simp [neutralBeforeProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩
        (.letE ⟨.object, trivial⟩ .ret)
  · intro declaration member
    simp [neutralBeforeProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl, neutralBefore,
      liveDecl, deadErasedDecl, letDecl, codeBinderIds,
      BinderNamesUnique, ImpureHygiene.paramIds, live, dead]

theorem neutralShadowProgramRun :
    shadowProgram? 3 neutralBeforeProgram =
      some neutralAfterProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    neutralBeforeProgram, neutralAfterProgram, fixtureDecl, decl,
    neutralShadowRun]

/-- End-to-end use of the checked strong endpoint on a concrete program.
Only foreign-response compatibility remains parametric; the source
runtime/ownership invariant is fully discharged above. -/
theorem neutralProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 3) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      neutralBeforeProgram neutralAfterProgram #[`main] :=
  shadowProgram_loweringCorrect_sourceMachineInvariant
    neutralBeforeProgramElimDeadWellFormed neutralShadowProgramRun
    compatible (neutralSourceRuntimeOwnershipInitialInvariant externals)

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
    control := .code (.uset dead 1 usizeField <|
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

def closedBoxSourceInitialState : MachineState :=
  initialState closedBoxBeforeProgram `main #[.erased]

def closedBoxTargetInitialState : MachineState :=
  initialState closedBoxAfterProgram `main #[.erased]

def closedBoxSourceBodyState : MachineState :=
  { program := closedBoxBeforeProgram
    control := .code closedBoxBefore
    env := liveEnv }

def closedBoxTargetBodyState : MachineState :=
  { program := closedBoxAfterProgram
    control := .code closedBoxAfter
    env := liveEnv }

def closedBoxSourceAfterLiteralState : MachineState :=
  { closedBoxSourceBodyState with
    control := .code deletedBoxBefore
    env := bind liveEnv boxInputVar
      (.scalar (.uint64 18446744073709551615)) }

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

theorem deletedBoxShadowGraph3 :
    ShadowCodeGraph 3 neutralUsed deletedBoxBefore deletedBoxAfter := by
  exact ⟨2, {}, neutralUsed, by omega,
    deletedBoxShadowRun, .refl neutralUsed⟩

theorem closedBoxShadowGraph :
    ShadowCodeGraph 3 neutralUsed closedBoxBefore closedBoxAfter := by
  exact ⟨3, {}, neutralUsed, by omega,
    closedBoxShadowRun, .refl neutralUsed⟩

theorem deletedUSizeScalarShadowGraph :
    ShadowCodeGraph 4 neutralUsed
      (.uset dead 1 usizeField <|
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

theorem closedBoxInitialSteps :
    coreStep closedBoxSourceInitialState = .next closedBoxSourceBodyState ∧
      coreStep closedBoxTargetInitialState = .next closedBoxTargetBodyState := by
  constructor <;> rfl

theorem closedBoxBodyRelated :
    ReachableMachineRelated 3 emptyAddressRenaming
      closedBoxSourceBodyState closedBoxTargetBodyState := by
  unfold ReachableMachineRelated
  refine ⟨envRootsOn neutralUsed closedBoxSourceBodyState.env,
    envRootsOn neutralUsed closedBoxTargetBodyState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
      closedBoxProgramShadowRelated
  · exact .code closedBoxShadowGraph
      (ShadowJoinEnvRelated.empty 3 neutralUsed)
      (by simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
        liveEnvReachableRelated)
  · simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related liveEnvReachableRelated)

theorem closedBoxLiteralStepRelated :
    coreStep closedBoxSourceBodyState =
        .next closedBoxSourceAfterLiteralState ∧
      ReachableMachineRelated 3 emptyAddressRenaming
        closedBoxSourceAfterLiteralState closedBoxTargetBodyState := by
  have programs : ProgramRelated (ShadowCodeRelated 3)
      closedBoxSourceBodyState.program closedBoxTargetBodyState.program := by
    simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
      closedBoxProgramShadowRelated
  have frames : ReachableFramesRelated 3 emptyAddressRenaming
      closedBoxSourceBodyState.frames closedBoxTargetBodyState.frames [] [] :=
    .nil
  have env : EnvRelOn emptyAddressRenaming neutralUsed
      closedBoxSourceBodyState.env closedBoxTargetBodyState.env := by
    simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
      liveEnvReachableRelated
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      closedBoxSourceBodyState.runtime closedBoxTargetBodyState.runtime
      (envRootsOn neutralUsed closedBoxSourceBodyState.env ++ [])
      (envRootsOn neutralUsed closedBoxTargetBodyState.env ++ []) := by
    simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related liveEnvReachableRelated)
  have evaluated : evalLetValue closedBoxSourceBodyState closedBoxInputDecl =
      .ok (closedBoxSourceBodyState.runtime,
        .value (.scalar (.uint64 18446744073709551615))) := by
    rfl
  have progress := coreStep_deletedLet_reachableRelated
    (sourceState := closedBoxSourceBodyState)
    (targetState := closedBoxTargetBodyState)
    (declaration := closedBoxInputDecl)
    (sourceContinuation := deletedBoxBefore)
    (targetContinuation := deletedBoxAfter)
    programs frames deletedBoxShadowGraph3
    (ShadowJoinEnvRelated.empty 3 neutralUsed) env
    (by native_decide) evaluated runtime
  simpa [closedBoxSourceBodyState, closedBoxTargetBodyState,
    closedBoxSourceAfterLiteralState, closedBoxBefore, closedBoxAfter,
    deletedBoxAfter, closedBoxInputDecl, letDecl] using progress

theorem closedBoxAfterLiteralEnvRelated :
    EnvRelOn emptyAddressRenaming neutralUsed
      closedBoxSourceAfterLiteralState.env closedBoxTargetBodyState.env := by
  simpa [closedBoxSourceAfterLiteralState, closedBoxSourceBodyState,
    closedBoxTargetBodyState] using
      (EnvRelOn.bindLeft_of_absent
        (binder := boxInputVar)
        (value := Value.scalar (.uint64 18446744073709551615))
        liveEnvReachableRelated (by native_decide))

theorem closedBoxAfterLiteralRuntimeRelated :
    ShadowRuntimeRel emptyAddressRenaming
      closedBoxSourceAfterLiteralState.runtime
      closedBoxTargetBodyState.runtime
      (envRootsOn neutralUsed closedBoxSourceAfterLiteralState.env)
      (envRootsOn neutralUsed closedBoxTargetBodyState.env) := by
  simpa [closedBoxSourceAfterLiteralState, closedBoxSourceBodyState,
    closedBoxTargetBodyState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related closedBoxAfterLiteralEnvRelated)

theorem closedBoxAfterLiteralBoxReady :
    DeletedBoxReadyAt closedBoxSourceAfterLiteralState boxInputVar := by
  apply DeletedBoxReadyAt.scalar (.uint64 18446744073709551615)
  simp [closedBoxSourceAfterLiteralState, closedBoxSourceBodyState,
    liveEnv, lookupValue, Impure.bind, lookup,
    boxInputVar, live]

theorem closedBoxAfterLiteralUnifiedReady :
    DeletedLetReadyAt closedBoxSourceAfterLiteralState
      (runtimeRoots closedBoxSourceAfterLiteralState.runtime
        (envRootsOn neutralUsed closedBoxSourceAfterLiteralState.env ++ []))
      deadBoxDecl := by
  unfold deadBoxDecl letDecl
  exact .box dead dead.name objType u64Type boxInputVar
    closedBoxAfterLiteralBoxReady

/-- The first active closed-box state satisfies the exact source contract:
its large scalar literal is locally eliminable regardless of whether it is
represented immediately or in the runtime. -/
theorem closedBoxLiteralSourceRuntimeReadyAt
    (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3 closedBoxSourceBodyState
      sourceFrameRoots closedBoxBefore := by
  unfold closedBoxBefore closedBoxInputDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_literal

/-- The residual closed-box state uses the reusable allocation-family
contract rather than reopening the exact compiler view. -/
theorem closedBoxBoxSourceRuntimeReadyAt
    (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3 closedBoxSourceAfterLiteralState
      sourceFrameRoots deletedBoxBefore := by
  unfold deletedBoxBefore deadBoxDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_box
    closedBoxAfterLiteralBoxReady

theorem closedBoxBoxStepRelated :
    ∃ nextRuntime boxValue,
      let sourceAfterBox := {
        closedBoxSourceAfterLiteralState with
        runtime := nextRuntime
        env := bind closedBoxSourceAfterLiteralState.env dead boxValue
        control := .code (.return live) }
      coreStep closedBoxSourceAfterLiteralState = .next sourceAfterBox ∧
        ReachableMachineRelated 3 emptyAddressRenaming
          sourceAfterBox closedBoxTargetBodyState := by
  have programs : ProgramRelated (ShadowCodeRelated 3)
      closedBoxSourceAfterLiteralState.program
      closedBoxTargetBodyState.program := by
    simpa [closedBoxSourceAfterLiteralState, closedBoxSourceBodyState,
      closedBoxTargetBodyState] using closedBoxProgramShadowRelated
  have frames : ReachableFramesRelated 3 emptyAddressRenaming
      closedBoxSourceAfterLiteralState.frames
      closedBoxTargetBodyState.frames [] [] := .nil
  have runtime : ShadowRuntimeRel emptyAddressRenaming
      closedBoxSourceAfterLiteralState.runtime closedBoxTargetBodyState.runtime
      (envRootsOn neutralUsed closedBoxSourceAfterLiteralState.env ++ [])
      (envRootsOn neutralUsed closedBoxTargetBodyState.env ++ []) := by
    simpa using closedBoxAfterLiteralRuntimeRelated
  have progress := coreStep_deletedLet_of_ready
    (sourceState := closedBoxSourceAfterLiteralState)
    (targetState := closedBoxTargetBodyState)
    (sourceContinuation := .return live)
    (targetContinuation := .return live)
    (declaration := deadBoxDecl)
    programs frames returnLiveShadowGraph
    (ShadowJoinEnvRelated.empty 3 neutralUsed)
    closedBoxAfterLiteralEnvRelated (by native_decide)
    runtime closedBoxAfterLiteralUnifiedReady
  simpa [closedBoxSourceAfterLiteralState, closedBoxSourceBodyState,
    closedBoxTargetBodyState, closedBoxAfter, deletedBoxBefore,
    deadBoxDecl, letDecl] using progress

/-- Complete program-entry witness: Lean's actual output needs two internal
steps, while the source additionally evaluates the now-dead literal and box.
Both executions terminate with observations related up to unreachable heap
garbage. -/
theorem closedBoxProgramEvaluationsRelated (externals : ExternalSpec) :
    ∃ sourceObservation targetObservation,
      Impure.Evaluates externals closedBoxBeforeProgram `main #[.erased]
          sourceObservation ∧
        Impure.Evaluates externals closedBoxAfterProgram `main #[.erased]
          targetObservation ∧
        ObservationRel sourceObservation targetObservation := by
  rcases closedBoxBoxStepRelated with
    ⟨nextRuntime, boxValue, boxStep, afterBoxRelated⟩
  let sourceAfterBox : MachineState := {
    closedBoxSourceAfterLiteralState with
    runtime := nextRuntime
    env := bind closedBoxSourceAfterLiteralState.env dead boxValue
    control := .code (.return live) }
  have boxStep' : coreStep closedBoxSourceAfterLiteralState =
      .next sourceAfterBox := by
    simpa [sourceAfterBox] using boxStep
  have afterBoxRelated' : ReachableMachineRelated 3 emptyAddressRenaming
      sourceAfterBox closedBoxTargetBodyState := by
    simpa [sourceAfterBox] using afterBoxRelated
  have sourceRead : lookup sourceAfterBox.env live = some .erased := by
    simp [sourceAfterBox, closedBoxSourceAfterLiteralState,
      closedBoxSourceBodyState, liveEnv, Impure.bind, lookup,
      live, dead, boxInputVar]
  rcases afterBoxRelated'.returnStep rfl rfl sourceRead with
    ⟨targetValue, targetRead, values,
      sourceReturn, targetReturn, yieldedRelated⟩
  let sourceYielded : MachineState := {
    sourceAfterBox with control := .yielded .erased }
  let targetYielded : MachineState := {
    closedBoxTargetBodyState with control := .yielded targetValue }
  have yieldedRelated' : ReachableMachineRelated 3 emptyAddressRenaming
      sourceYielded targetYielded := by
    simpa [sourceYielded, targetYielded] using yieldedRelated
  have observations : ObservationRel
      (observe sourceYielded (.returned .erased))
      (observe targetYielded (.returned targetValue)) :=
    yieldedRelated'.yieldedObservation rfl rfl rfl rfl
  have sourceDone : coreStep sourceYielded =
      .done (observe sourceYielded (.returned .erased)) := by
    simp [sourceYielded, sourceAfterBox,
      closedBoxSourceAfterLiteralState, closedBoxSourceBodyState, coreStep]
  have targetDone : coreStep targetYielded =
      .done (observe targetYielded (.returned targetValue)) := by
    simp [targetYielded, closedBoxTargetBodyState, coreStep]
  refine ⟨observe sourceYielded (.returned .erased),
    observe targetYielded (.returned targetValue), ?_, ?_, observations⟩
  · exact ⟨4, sourceYielded,
      .step (.internal closedBoxInitialSteps.1) <|
        .step (.internal closedBoxLiteralStepRelated.1) <|
          .step (.internal boxStep') <|
            .step (.internal sourceReturn) (.refl sourceYielded),
      sourceDone⟩
  · exact ⟨2, targetYielded,
      .step (.internal closedBoxInitialSteps.2) <|
        .step (.internal targetReturn) (.refl targetYielded),
      targetDone⟩

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

/-- The concrete reset fixture's actual transparent traversal, before any
fuel or liveness widening. -/
def deletedResetExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      deletedResetBefore deletedResetAfter :=
  ExactShadowCodeGraph.ofResult deletedResetShadowRun

/-- Hereditary binder readiness for that exact reset deletion.  The scoped
index names precisely the two ambient operands supplied by this synthetic
mid-execution fixture. -/
theorem deletedResetExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedResetExactGraph.view := by
  apply deletedResetExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
        resetObjectVar)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [deletedResetBefore, deadResetDecl, letDecl, codeBinderIds,
      BinderNamesUnique, ImpureHygiene.paramIds, live, dead]

/-- The exact-provenance interface accepts the concrete reset ownership
certificate at its actual liveness roots.  The older universal source
contract cannot express this state because widening the roots with the reset
operand itself would make its destination reachable. -/
theorem deletedResetExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 2 neutralUsed deletedResetSourceState
      (runtimeRoots deletedResetSourceState.runtime
        (envRootsOn neutralUsed deletedResetSourceState.env ++ []))
      deletedResetBefore deletedResetAfter := by
  refine ⟨2, neutralUsed, Nat.le_refl 2,
    deletedResetExactGraph, UsedSubset.refl neutralUsed,
    deletedResetExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt deletedResetSourceState
        (runtimeRoots deletedResetSourceState.runtime
          (envRootsOn neutralUsed deletedResetSourceState.env ++ []))
        deadResetDecl := by
    unfold deadResetDecl letDecl
    exact .reset dead dead.name objType 1 resetObjectVar
      (by simpa using deletedResetReady)
  have kept :
      RetainedLetReadyAt deletedResetSourceState
        (runtimeRoots deletedResetSourceState.runtime
          (envRootsOn neutralUsed deletedResetSourceState.env ++ []))
        deadResetDecl.value := by
    trivial
  exact ExactShadowCodeRuntimeReadyAt.let_of_ready removed kept

/-- The synthetic reset programs retain the same hereditary exact graph in
their single declaration bodies. -/
theorem deletedResetProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 2)
      deletedResetBeforeProgram deletedResetAfterProgram := by
  unfold ProgramRelated
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated 2))
    [fixtureDecl `main deletedResetBefore]
    [fixtureDecl `main deletedResetAfter]
  apply ListRel.cons
  · exact {
      name_eq := rfl
      levelParams_eq := rfl
      type_eq := rfl
      params_eq := rfl
      safe_eq := rfl
      value := .code ⟨neutralUsed, 2, neutralUsed, Nat.le_refl 2,
        deletedResetExactGraph, UsedSubset.refl neutralUsed,
        deletedResetExactBinderReady⟩
      recursive_eq := rfl
      inlineAttr_eq := rfl
    }
  · exact .nil

/-- Full strong readiness of the concrete reset pair, including exact
compiler provenance, live environments, empty saved stacks, and the
unreachable-heap relation. -/
theorem deletedResetExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 2
      deletedResetSourceState deletedResetTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedResetSourceState.env,
    envRootsOn neutralUsed deletedResetTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedResetSourceState, deletedResetTargetState] using
      deletedResetProgramBinderReadyRelated
  · exact .code deletedResetExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed)
      (by simpa [deletedResetSourceState, deletedResetTargetState] using
        deletedResetEnvReachableRelated)
  · simpa [deletedResetSourceState, deletedResetTargetState] using
      deletedResetRuntimeRelated

/-- The exact dispatcher consumes the concrete ownership certificate and
preserves hereditary compiler provenance after the reset step, while the
target may take a non-lockstep path (reflexive for this deletion). -/
theorem deletedResetExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedResetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedResetTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 2 sourceAfter targetAfter :=
  deletedResetExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedResetExactMachineReadyAt rfl step

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

/-- The heap-allocating large-Nat literal satisfies the source-side dynamic
contract at its concrete active state. -/
theorem deletedLargeNatSourceRuntimeReadyAt
    (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 2 deletedLargeNatSourceState
      sourceFrameRoots deletedLargeNatBefore := by
  unfold deletedLargeNatBefore deadLargeNatDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_literal

/-- The partial-application allocation certificate is now exposed through
the same source-side exact-view interface as constructors and literals. -/
theorem deletedPapSourceRuntimeReadyAt
    (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 2 deletedPapSourceState
      sourceFrameRoots deletedPapBefore := by
  unfold deletedPapBefore deadPapDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_partialApplication
    deletedPapReady

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

/-- The scalar-box allocation certificate is exposed through the common
source-side exact-view interface. -/
theorem deletedBoxSourceRuntimeReadyAt
    (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 2 deletedBoxSourceState
      sourceFrameRoots deletedBoxBefore := by
  unfold deletedBoxBefore deadBoxDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_box deletedBoxReady

theorem deletedBoxUnifiedReady :
    DeletedLetReadyAt deletedBoxSourceState
      (runtimeRoots deletedBoxSourceState.runtime
        (envRootsOn neutralUsed deletedBoxSourceState.env ++ []))
      deadBoxDecl := by
  unfold deadBoxDecl letDecl
  exact .box dead dead.name objType u64Type boxInputVar deletedBoxReady

/-- The large literal's unified deleted-let certificate records that its
possible heap allocation is fresh source-only garbage. -/
theorem deletedLargeNatUnifiedReady :
    DeletedLetReadyAt deletedLargeNatSourceState
      (runtimeRoots deletedLargeNatSourceState.runtime
        (envRootsOn neutralUsed deletedLargeNatSourceState.env ++ []))
      deadLargeNatDecl := by
  unfold deadLargeNatDecl letDecl
  exact .literal dead dead.name objType (.nat 9223372036854775808)

/-- The partial application's unified deleted-let certificate records the
resolved declaration and evaluated captured arguments. -/
theorem deletedPapUnifiedReady :
    DeletedLetReadyAt deletedPapSourceState
      (runtimeRoots deletedPapSourceState.runtime
        (envRootsOn neutralUsed deletedPapSourceState.env ++ []))
      deadPapDecl := by
  unfold deadPapDecl letDecl
  exact .partialApplication dead dead.name objType `first
    #[.fvar papArgVar] deletedPapReady

/-- Concrete constructor readiness for the inner allocating fixture. -/
theorem deletedCtorReady :
    DeletedCtorReadyAt allocatingSourceInnerState
      oneFieldInfo #[.fvar live] := by
  refine .mk #[.erased] ?_ rfl
  simp [allocatingSourceInnerState, liveEnv, evalArgs, evalArg]
  rfl

/-- The inner constructor's unified deleted-let certificate exposes its
fresh source-only heap allocation. -/
theorem deletedCtorUnifiedReady :
    DeletedLetReadyAt allocatingSourceInnerState
      (runtimeRoots allocatingSourceInnerState.runtime
        (envRootsOn neutralUsed allocatingSourceInnerState.env ++ []))
      deadCtorDecl := by
  unfold deadCtorDecl letDecl
  exact .constructor dead dead.name objType oneFieldInfo
    #[.fvar live] deletedCtorReady

/-- Transparent exact run for the inner deleted constructor. -/
theorem deletedCtorShadowRun :
    shadowCode? 2 {} (.let deadCtorDecl (.return live)) =
      some (.return live, neutralUsed) := by
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deadCtorDecl, letDecl, neutralUsed, shadowCode?, safeToElim,
    deadAbsent]

/-- Transparent exact identity run for the declaration used by the partial
application fixture. -/
theorem firstCodeShadowRun :
    shadowCode? 2 {} (.return x) =
      some (.return x, ({} : UsedLocals).insert x) := by
  simp [shadowCode?]

/-- Exact compiler provenance for the heap-allocating large literal. -/
def deletedLargeNatExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      deletedLargeNatBefore deletedLargeNatAfter :=
  ExactShadowCodeGraph.ofResult deletedLargeNatShadowRun

/-- Exact compiler provenance for the deleted partial application. -/
def deletedPapExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      deletedPapBefore deletedPapAfter :=
  ExactShadowCodeGraph.ofResult deletedPapShadowRun

/-- Exact compiler provenance for the deleted scalar box. -/
def deletedBoxExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      deletedBoxBefore deletedBoxAfter :=
  ExactShadowCodeGraph.ofResult deletedBoxShadowRun

/-- Exact compiler provenance for the inner deleted constructor. -/
def deletedCtorExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      (.let deadCtorDecl (.return live)) (.return live) :=
  ExactShadowCodeGraph.ofResult deletedCtorShadowRun

/-- Exact compiler provenance for the complete retained/deleted constructor
fixture. -/
def allocatingExactGraph :
    ExactShadowCodeGraph 3 neutralUsed
      allocatingBefore allocatingAfter :=
  ExactShadowCodeGraph.ofResult allocatingShadowRun

/-- Exact identity provenance for `first`'s return body. -/
def firstCodeExactGraph :
    ExactShadowCodeGraph 2 (({} : UsedLocals).insert x)
      (.return x) (.return x) :=
  ExactShadowCodeGraph.ofResult firstCodeShadowRun

/-- Hereditary static readiness for the large literal graph. -/
theorem deletedLargeNatExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedLargeNatExactGraph.view := by
  apply deletedLargeNatExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [deletedLargeNatBefore, deadLargeNatDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead]

/-- Hereditary static readiness for the partial-application graph. -/
theorem deletedPapExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedPapExactGraph.view := by
  apply deletedPapExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
        papArgVar)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [deletedPapBefore, deadPapDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead]

/-- Hereditary static readiness for the scalar-box graph. -/
theorem deletedBoxExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedBoxExactGraph.view := by
  apply deletedBoxExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
        boxInputVar)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, .uint64⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [deletedBoxBefore, deadBoxDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead]

/-- Hereditary static readiness for the inner constructor graph. -/
theorem deletedCtorExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedCtorExactGraph.view := by
  apply deletedCtorExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [deadCtorDecl, letDecl, codeBinderIds, BinderNamesUnique,
      live, dead]

/-- Hereditary static readiness for the complete constructor fixture. -/
theorem allocatingExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed allocatingExactGraph.view := by
  apply allocatingExactGraph.binderReady_of_canonical
    (index := Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.letE
      · native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · exact ⟨.object, trivial⟩
      · apply ScopedCodeWellFormedTree.ret
        native_decide
  · simp [allocatingBefore, deadCtorDecl, liveDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead]

/-- Hereditary static readiness for the unchanged `first` declaration. -/
theorem firstCodeExactBinderReady :
    ExactShadowCodeBinderReady (({} : UsedLocals).insert x)
      firstCodeExactGraph.view := by
  apply firstCodeExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty x)
        y)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · simp [codeBinderIds, BinderNamesUnique]

/-- Exact active-code readiness for the heap-allocating large literal. -/
theorem deletedLargeNatExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 2 neutralUsed
      deletedLargeNatSourceState
      (runtimeRoots deletedLargeNatSourceState.runtime
        (envRootsOn neutralUsed deletedLargeNatSourceState.env ++ []))
      deletedLargeNatBefore deletedLargeNatAfter := by
  refine ⟨2, neutralUsed, Nat.le_refl 2,
    deletedLargeNatExactGraph, UsedSubset.refl neutralUsed,
    deletedLargeNatExactBinderReady, ?_⟩
  have decision :
      deletedLargeNatExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedLargeNatExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp [deletedLargeNatAfter])
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision
    deletedLargeNatUnifiedReady

/-- Exact active-code readiness for the deleted partial application. -/
theorem deletedPapExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 2 neutralUsed
      deletedPapSourceState
      (runtimeRoots deletedPapSourceState.runtime
        (envRootsOn neutralUsed deletedPapSourceState.env ++ []))
      deletedPapBefore deletedPapAfter := by
  refine ⟨2, neutralUsed, Nat.le_refl 2,
    deletedPapExactGraph, UsedSubset.refl neutralUsed,
    deletedPapExactBinderReady, ?_⟩
  have decision :
      deletedPapExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedPapExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp [deletedPapAfter])
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision
    deletedPapUnifiedReady

/-- Exact active-code readiness for the deleted scalar box. -/
theorem deletedBoxExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 2 neutralUsed
      deletedBoxSourceState
      (runtimeRoots deletedBoxSourceState.runtime
        (envRootsOn neutralUsed deletedBoxSourceState.env ++ []))
      deletedBoxBefore deletedBoxAfter := by
  refine ⟨2, neutralUsed, Nat.le_refl 2,
    deletedBoxExactGraph, UsedSubset.refl neutralUsed,
    deletedBoxExactBinderReady, ?_⟩
  have decision :
      deletedBoxExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedBoxExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp [deletedBoxAfter])
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision
    deletedBoxUnifiedReady

/-- Exact active-code readiness for the inner deleted constructor. -/
theorem deletedCtorExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 3 neutralUsed
      allocatingSourceInnerState
      (runtimeRoots allocatingSourceInnerState.runtime
        (envRootsOn neutralUsed allocatingSourceInnerState.env ++ []))
      (.let deadCtorDecl (.return live)) (.return live) := by
  refine ⟨2, neutralUsed, by omega,
    deletedCtorExactGraph, UsedSubset.refl neutralUsed,
    deletedCtorExactBinderReady, ?_⟩
  have decision :
      deletedCtorExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedCtorExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp)
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision
    deletedCtorUnifiedReady

/-- Lift one exact code relation through the synthetic one-declaration
fixture wrapper. -/
theorem fixtureProgram_binderReadyRelated
    (related : BinderReadyShadowCodeRelated fuel source target) :
    ProgramRelated (BinderReadyShadowCodeRelated fuel)
      { decls := #[fixtureDecl name source] }
      { decls := #[fixtureDecl name target] } := by
  unfold ProgramRelated
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated fuel))
    [fixtureDecl name source] [fixtureDecl name target]
  apply ListRel.cons
  · exact {
      name_eq := rfl
      levelParams_eq := rfl
      type_eq := rfl
      params_eq := rfl
      safe_eq := rfl
      value := .code related
      recursive_eq := rfl
      inlineAttr_eq := rfl
    }
  · exact .nil

/-- Exact hereditary program relation for the large literal fixture. -/
theorem deletedLargeNatProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 2)
      deletedLargeNatBeforeProgram deletedLargeNatAfterProgram := by
  simpa [deletedLargeNatBeforeProgram, deletedLargeNatAfterProgram] using
    fixtureProgram_binderReadyRelated (name := `main)
      (⟨neutralUsed, 2, neutralUsed, Nat.le_refl 2,
        deletedLargeNatExactGraph, UsedSubset.refl neutralUsed,
        deletedLargeNatExactBinderReady⟩ :
        BinderReadyShadowCodeRelated 2
          deletedLargeNatBefore deletedLargeNatAfter)

/-- Exact hereditary program relation for the scalar-box fixture. -/
theorem deletedBoxProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 2)
      deletedBoxBeforeProgram deletedBoxAfterProgram := by
  simpa [deletedBoxBeforeProgram, deletedBoxAfterProgram] using
    fixtureProgram_binderReadyRelated (name := `main)
      (⟨neutralUsed, 2, neutralUsed, Nat.le_refl 2,
        deletedBoxExactGraph, UsedSubset.refl neutralUsed,
        deletedBoxExactBinderReady⟩ :
        BinderReadyShadowCodeRelated 2 deletedBoxBefore deletedBoxAfter)

/-- Exact hereditary program relation for the retained/deleted constructor
fixture. -/
theorem allocatingProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 3)
      allocatingBeforeProgram allocatingAfterProgram := by
  simpa [allocatingBeforeProgram, allocatingAfterProgram] using
    fixtureProgram_binderReadyRelated (name := `main)
      (⟨neutralUsed, 3, neutralUsed, Nat.le_refl 3,
        allocatingExactGraph, UsedSubset.refl neutralUsed,
        allocatingExactBinderReady⟩ :
        BinderReadyShadowCodeRelated 3 allocatingBefore allocatingAfter)

/-- Exact hereditary program relation for the two-declaration partial
application fixture. -/
theorem deletedPapProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 2)
      deletedPapBeforeProgram deletedPapAfterProgram := by
  unfold ProgramRelated
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated 2))
    [firstDecl, fixtureDecl `main deletedPapBefore]
    [firstDecl, fixtureDecl `main deletedPapAfter]
  apply ListRel.cons
  · exact {
      name_eq := rfl
      levelParams_eq := rfl
      type_eq := rfl
      params_eq := rfl
      safe_eq := rfl
      value := .code ⟨({} : UsedLocals).insert x, 2,
        ({} : UsedLocals).insert x, Nat.le_refl 2,
        firstCodeExactGraph,
        UsedSubset.refl (({} : UsedLocals).insert x),
        firstCodeExactBinderReady⟩
      recursive_eq := rfl
      inlineAttr_eq := rfl
    }
  · apply ListRel.cons
    · exact {
        name_eq := rfl
        levelParams_eq := rfl
        type_eq := rfl
        params_eq := rfl
        safe_eq := rfl
        value := .code ⟨neutralUsed, 2, neutralUsed, Nat.le_refl 2,
          deletedPapExactGraph, UsedSubset.refl neutralUsed,
          deletedPapExactBinderReady⟩
        recursive_eq := rfl
        inlineAttr_eq := rfl
      }
    · exact .nil

/-- Full exact-provenance machine readiness for the large literal. -/
theorem deletedLargeNatExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 2
      deletedLargeNatSourceState deletedLargeNatTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedLargeNatSourceState.env,
    envRootsOn neutralUsed deletedLargeNatTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedLargeNatSourceState, deletedLargeNatTargetState] using
      deletedLargeNatProgramBinderReadyRelated
  · exact .code deletedLargeNatExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed)
      (by
        simpa [deletedLargeNatSourceState, deletedLargeNatTargetState] using
          liveEnvReachableRelated)
  · simpa [deletedLargeNatSourceState, deletedLargeNatTargetState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related liveEnvReachableRelated)

/-- Full exact-provenance machine readiness for the partial application. -/
theorem deletedPapExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 2
      deletedPapSourceState deletedPapTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedPapSourceState.env,
    envRootsOn neutralUsed deletedPapTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedPapSourceState, deletedPapTargetState] using
      deletedPapProgramBinderReadyRelated
  · exact .code deletedPapExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed)
      (by
        simpa [deletedPapSourceState, deletedPapTargetState] using
          deletedPapEnvReachableRelated)
  · simpa [deletedPapSourceState, deletedPapTargetState] using
      deletedPapRuntimeRelated

/-- Full exact-provenance machine readiness for the scalar box. -/
theorem deletedBoxExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 2
      deletedBoxSourceState deletedBoxTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedBoxSourceState.env,
    envRootsOn neutralUsed deletedBoxTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedBoxSourceState, deletedBoxTargetState] using
      deletedBoxProgramBinderReadyRelated
  · exact .code deletedBoxExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed)
      (by
        simpa [deletedBoxSourceState, deletedBoxTargetState] using
          deletedBoxEnvReachableRelated)
  · simpa [deletedBoxSourceState, deletedBoxTargetState] using
      deletedBoxRuntimeRelated

/-- Full exact-provenance machine readiness for the inner constructor. -/
theorem deletedCtorExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 3
      allocatingSourceInnerState allocatingTargetInnerState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed allocatingSourceInnerState.env,
    envRootsOn neutralUsed allocatingTargetInnerState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [allocatingSourceInnerState, allocatingTargetInnerState] using
      allocatingProgramBinderReadyRelated
  · exact .code deletedCtorExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 3 neutralUsed)
      (by
        simpa [allocatingSourceInnerState, allocatingTargetInnerState] using
          liveEnvReachableRelated)
  · simpa [allocatingSourceInnerState, allocatingTargetInnerState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related liveEnvReachableRelated)

/-- The exact dispatcher preserves hereditary provenance across the
source-only large-literal allocation. -/
theorem deletedLargeNatExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedLargeNatSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedLargeNatTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 2 sourceAfter targetAfter :=
  deletedLargeNatExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedLargeNatExactMachineReadyAt rfl step

/-- The exact dispatcher preserves hereditary provenance across the
source-only partial-application allocation. -/
theorem deletedPapExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedPapSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedPapTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 2 sourceAfter targetAfter :=
  deletedPapExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedPapExactMachineReadyAt rfl step

/-- The exact dispatcher preserves hereditary provenance across the
source-only scalar-box allocation. -/
theorem deletedBoxExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedBoxSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedBoxTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 2 sourceAfter targetAfter :=
  deletedBoxExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedBoxExactMachineReadyAt rfl step

/-- The exact dispatcher preserves hereditary provenance across the
source-only constructor allocation. -/
theorem deletedCtorExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals allocatingSourceInnerState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals allocatingTargetInnerState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter :=
  deletedCtorExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedCtorExactMachineReadyAt rfl step

/-- Exact compiler provenance for the two-step closed-box deletion.  The
backwards pass first deletes the box, which also makes its scalar input
literal dead, so both source lets disappear. -/
def closedBoxExactGraph :
    ExactShadowCodeGraph 3 neutralUsed closedBoxBefore closedBoxAfter :=
  ExactShadowCodeGraph.ofResult closedBoxShadowRun

/-- Hereditary static readiness for the complete closed-box graph.  The live
result is an ambient declaration parameter; both local binders are fresh and
carry canonical impure runtime types. -/
theorem closedBoxExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed closedBoxExactGraph.view := by
  apply closedBoxExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.uint64, trivial⟩
    · apply ScopedCodeWellFormedTree.letE
      · native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · exact ⟨.object, .uint64⟩
      · apply ScopedCodeWellFormedTree.ret
        native_decide
  · simp [closedBoxBefore, closedBoxInputDecl, deletedBoxBefore,
      deadBoxDecl, letDecl, codeBinderIds, BinderNamesUnique,
      live, dead, boxInputVar]

/-- Exact active-code readiness for the first source-only scalar literal. -/
theorem closedBoxLiteralExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 3 neutralUsed
      closedBoxSourceBodyState
      (runtimeRoots closedBoxSourceBodyState.runtime
        (envRootsOn neutralUsed closedBoxSourceBodyState.env ++ []))
      closedBoxBefore closedBoxAfter := by
  refine ⟨3, neutralUsed, Nat.le_refl 3,
    closedBoxExactGraph, UsedSubset.refl neutralUsed,
    closedBoxExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt closedBoxSourceBodyState
        (runtimeRoots closedBoxSourceBodyState.runtime
          (envRootsOn neutralUsed closedBoxSourceBodyState.env ++ []))
        closedBoxInputDecl := by
    unfold closedBoxInputDecl letDecl
    exact .literal boxInputVar boxInputVar.name u64Type
      (.uint64 18446744073709551615)
  have decision :
      closedBoxExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      closedBoxExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp [closedBoxAfter])
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision removed

/-- Exact active-code readiness for the second source-only edge, where the
scalar input produced by the first step is boxed into unreachable garbage. -/
theorem closedBoxAllocationExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 3 neutralUsed
      closedBoxSourceAfterLiteralState
      (runtimeRoots closedBoxSourceAfterLiteralState.runtime
        (envRootsOn neutralUsed closedBoxSourceAfterLiteralState.env ++ []))
      deletedBoxBefore closedBoxAfter := by
  refine ⟨2, neutralUsed, by omega,
    deletedBoxExactGraph, UsedSubset.refl neutralUsed,
    deletedBoxExactBinderReady, ?_⟩
  have decision :
      deletedBoxExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedBoxExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp [deletedBoxAfter])
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision
    closedBoxAfterLiteralUnifiedReady

/-- Exact hereditary program relation for the parameterized closed-box
declaration. -/
theorem closedBoxProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 3)
      closedBoxBeforeProgram closedBoxAfterProgram := by
  unfold ProgramRelated
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated 3))
    [decl `main #[param live] objType (.code closedBoxBefore)]
    [decl `main #[param live] objType (.code closedBoxAfter)]
  apply ListRel.cons
  · exact {
      name_eq := rfl
      levelParams_eq := rfl
      type_eq := rfl
      params_eq := rfl
      safe_eq := rfl
      value := .code
        ⟨neutralUsed, 3, neutralUsed, Nat.le_refl 3,
          closedBoxExactGraph, UsedSubset.refl neutralUsed,
          closedBoxExactBinderReady⟩
      recursive_eq := rfl
      inlineAttr_eq := rfl
    }
  · exact .nil

/-- The concrete erased parameter is related to itself at the empty-runtime
entry state. -/
theorem closedBoxArgumentsRelated :
    ArrayRel (ValueRel emptyAddressRenaming)
      (#[.erased] : Array Value) #[.erased] := by
  change ListRel (ValueRel emptyAddressRenaming) [.erased] [.erased]
  exact .cons .erased .nil

/-- Exact hereditary readiness before resolving the parameterized `main`
declaration. -/
theorem closedBoxInitialExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 3
      closedBoxSourceInitialState closedBoxTargetInitialState := by
  simpa [closedBoxSourceInitialState, closedBoxTargetInitialState] using
    initialState_binderReadyReachableMachineReadyAt
      closedBoxProgramBinderReadyRelated closedBoxArgumentsRelated

/-- Full exact-provenance readiness at the first deleted let. -/
theorem closedBoxLiteralExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 3
      closedBoxSourceBodyState closedBoxTargetBodyState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed closedBoxSourceBodyState.env,
    envRootsOn neutralUsed closedBoxTargetBodyState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
      closedBoxProgramBinderReadyRelated
  · exact .code closedBoxLiteralExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 3 neutralUsed)
      (by
        simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
          liveEnvReachableRelated)
  · simpa [closedBoxSourceBodyState, closedBoxTargetBodyState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related liveEnvReachableRelated)

/-- Full exact-provenance readiness after the literal step, while the target
continues to stutter at the final return. -/
theorem closedBoxAllocationExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 3
      closedBoxSourceAfterLiteralState closedBoxTargetBodyState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed closedBoxSourceAfterLiteralState.env,
    envRootsOn neutralUsed closedBoxTargetBodyState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [closedBoxSourceAfterLiteralState, closedBoxSourceBodyState,
      closedBoxTargetBodyState] using closedBoxProgramBinderReadyRelated
  · exact .code closedBoxAllocationExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 3 neutralUsed)
      (by simpa using closedBoxAfterLiteralEnvRelated)
  · simpa using closedBoxAfterLiteralRuntimeRelated

/-- Resolving the declaration entry preserves exact provenance and reaches
the first ready source-only edge. -/
theorem closedBoxInitialExactStepPreserved
    (externals : ExternalSpec) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        closedBoxTargetInitialState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3
        closedBoxSourceBodyState targetAfter :=
  closedBoxInitialExactMachineReadyAt.related.matchNextStep_of_ready
    closedBoxInitialExactMachineReadyAt closedBoxInitialSteps.1

/-- The exact dispatcher preserves hereditary provenance while the source
evaluates the deleted scalar literal and the target stutters. -/
theorem closedBoxLiteralExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals closedBoxSourceBodyState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals closedBoxTargetBodyState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter :=
  closedBoxLiteralExactMachineReadyAt.related.matchCodeStep_of_ready
    closedBoxLiteralExactMachineReadyAt rfl step

/-- The exact dispatcher preserves hereditary provenance across the second
source-only step, which allocates an unreachable scalar box. -/
theorem closedBoxAllocationExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals closedBoxSourceAfterLiteralState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals closedBoxTargetBodyState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter :=
  closedBoxAllocationExactMachineReadyAt.related.matchCodeStep_of_ready
    closedBoxAllocationExactMachineReadyAt rfl step

/-- Composed exact regression: the source takes both deleted let steps while
the target may follow the non-lockstep path selected by the dispatcher, and
hereditary compiler provenance survives at the endpoint. -/
theorem closedBoxTwoSourceOnlyStepsExactPreserved
    (externals : ExternalSpec) :
    ∃ sourceAfter targetAfter,
      NonLockstep.Reaches externals closedBoxSourceBodyState sourceAfter ∧
      NonLockstep.Reaches externals closedBoxTargetBodyState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter := by
  rcases closedBoxBoxStepRelated with
    ⟨nextRuntime, boxValue, boxTransition, _related⟩
  let sourceAfterBox : MachineState := {
    closedBoxSourceAfterLiteralState with
    runtime := nextRuntime
    env := bind closedBoxSourceAfterLiteralState.env dead boxValue
    control := .code (.return live) }
  have boxTransition' :
      coreStep closedBoxSourceAfterLiteralState = .next sourceAfterBox := by
    simpa [sourceAfterBox] using boxTransition
  rcases closedBoxAllocationExactStepPreserved externals
      (.internal boxTransition') with
    ⟨targetAfter, targetPath, endpoint⟩
  refine ⟨sourceAfterBox, targetAfter, ?_, targetPath, endpoint⟩
  exact
    (NonLockstep.reaches_of_step
      (.internal closedBoxLiteralStepRelated.1)).trans
    (NonLockstep.reaches_of_step (.internal boxTransition'))

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

/-- Exact transparent provenance for the concrete-token reuse deletion. -/
def deletedReuseSomeExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      deletedReuseBefore deletedReuseAfter :=
  ExactShadowCodeGraph.ofResult deletedReuseShadowRun

/-- The reuse fixture's exact graph carries the hereditary absence proof for
its deleted result binder. -/
theorem deletedReuseSomeExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedReuseSomeExactGraph.view := by
  apply deletedReuseSomeExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
          (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
            Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
          reuseTokenVar)
        reuseArgVar)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [deletedReuseBefore, deadReuseDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead]

/-- Failed-token reuse allocates only on the source, and the exact deleted
edge consumes that allocation-safety certificate. -/
theorem deletedReuseNoneExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 2 neutralUsed
      deletedReuseNoneSourceState
      (runtimeRoots deletedReuseNoneSourceState.runtime
        (envRootsOn neutralUsed deletedReuseNoneSourceState.env ++ []))
      deletedReuseBefore deletedReuseAfter := by
  refine ⟨2, neutralUsed, Nat.le_refl 2,
    deletedReuseSomeExactGraph, UsedSubset.refl neutralUsed,
    deletedReuseSomeExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt deletedReuseNoneSourceState
        (runtimeRoots deletedReuseNoneSourceState.runtime
          (envRootsOn neutralUsed deletedReuseNoneSourceState.env ++ []))
        deadReuseDecl := by
    unfold deadReuseDecl letDecl
    exact .reuse dead dead.name objType reuseTokenVar oneFieldInfo true
      #[.fvar reuseArgVar] (by simpa using deletedReuseNoneReady)
  have decision :
      deletedReuseSomeExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedReuseSomeExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp [deletedReuseAfter])
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision removed

/-- At the deleted edge's roots, retained concrete-token reuse readiness is
constructively false: the token names exactly the unreachable cell certified
for source-only overwrite. -/
theorem deletedReuseSomeRetainedNotReady :
    ¬RetainedLetReadyAt deletedReuseSomeSourceState
      (runtimeRoots deletedReuseSomeSourceState.runtime
        (envRootsOn neutralUsed deletedReuseSomeSourceState.env ++ []))
      deadReuseDecl.value := by
  intro retained
  apply deletedReuseSomeDestinationUnreachable
  have reachable := retained 0 (by
    simp [deletedReuseSomeSourceState, deletedReuseSomeSourceEnv,
      lookupValue, Impure.bind, lookup, reuseTokenVar, reuseArgVar])
  simpa using reachable

/-- Concrete-token reuse is ready only for the actual deleted edge.  Its
unreachable destination proves deleted ownership safety; asking for retained
reuse readiness at these roots would require the opposite reachability fact. -/
theorem deletedReuseSomeExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 2 neutralUsed
      deletedReuseSomeSourceState
      (runtimeRoots deletedReuseSomeSourceState.runtime
        (envRootsOn neutralUsed deletedReuseSomeSourceState.env ++ []))
      deletedReuseBefore deletedReuseAfter := by
  refine ⟨2, neutralUsed, Nat.le_refl 2,
    deletedReuseSomeExactGraph, UsedSubset.refl neutralUsed,
    deletedReuseSomeExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt deletedReuseSomeSourceState
        (runtimeRoots deletedReuseSomeSourceState.runtime
          (envRootsOn neutralUsed deletedReuseSomeSourceState.env ++ []))
        deadReuseDecl := by
    unfold deadReuseDecl letDecl
    exact .reuse dead dead.name objType reuseTokenVar oneFieldInfo true
      #[.fvar reuseArgVar] (by simpa using deletedReuseSomeReady)
  have decision :
      deletedReuseSomeExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedReuseSomeExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp [deletedReuseAfter])
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision removed

/-- The single-declaration reuse fixtures retain their exact hereditary
compiler graph. -/
theorem deletedReuseSomeProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 2)
      deletedReuseBeforeProgram deletedReuseAfterProgram := by
  unfold ProgramRelated
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated 2))
    [fixtureDecl `main deletedReuseBefore]
    [fixtureDecl `main deletedReuseAfter]
  apply ListRel.cons
  · exact {
      name_eq := rfl
      levelParams_eq := rfl
      type_eq := rfl
      params_eq := rfl
      safe_eq := rfl
      value := .code ⟨neutralUsed, 2, neutralUsed, Nat.le_refl 2,
        deletedReuseSomeExactGraph, UsedSubset.refl neutralUsed,
        deletedReuseSomeExactBinderReady⟩
      recursive_eq := rfl
      inlineAttr_eq := rfl
    }
  · exact .nil

/-- Full exact-provenance machine readiness for failed-token reuse. -/
theorem deletedReuseNoneExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 2
      deletedReuseNoneSourceState deletedReuseTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedReuseNoneSourceState.env,
    envRootsOn neutralUsed deletedReuseTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedReuseNoneSourceState, deletedReuseTargetState] using
      deletedReuseSomeProgramBinderReadyRelated
  · exact .code deletedReuseNoneExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed)
      (by
        simpa [deletedReuseNoneSourceState, deletedReuseTargetState] using
          deletedReuseNoneEnvReachableRelated)
  · simpa [deletedReuseNoneSourceState, deletedReuseTargetState] using
      deletedReuseNoneRuntimeRelated

/-- The exact dispatcher preserves hereditary compiler provenance after
failed-token reuse performs its source-only allocation. -/
theorem deletedReuseNoneExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedReuseNoneSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedReuseTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 2 sourceAfter targetAfter :=
  deletedReuseNoneExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedReuseNoneExactMachineReadyAt rfl step

/-- Full exact-provenance machine readiness for the concrete-token reuse
pair. -/
theorem deletedReuseSomeExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 2
      deletedReuseSomeSourceState deletedReuseTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedReuseSomeSourceState.env,
    envRootsOn neutralUsed deletedReuseTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedReuseSomeSourceState, deletedReuseTargetState] using
      deletedReuseSomeProgramBinderReadyRelated
  · exact .code deletedReuseSomeExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed)
      (by
        simpa [deletedReuseSomeSourceState, deletedReuseTargetState] using
          deletedReuseSomeEnvReachableRelated)
  · simpa [deletedReuseSomeSourceState, deletedReuseTargetState] using
      deletedReuseSomeRuntimeRelated

/-- The exact dispatcher preserves hereditary compiler provenance after the
concrete-token reuse overwrites its unreachable owned cell. -/
theorem deletedReuseSomeExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedReuseSomeSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedReuseTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 2 sourceAfter targetAfter :=
  deletedReuseSomeExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedReuseSomeExactMachineReadyAt rfl step

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
      dead 1 usizeField := by
  refine ⟨0, ({ object := .ctor deletedWriteObject } : HeapCell),
    deletedWriteObject, 7, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [deletedUSizeSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · simp [deletedUSizeSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl
  · simp [deletedWriteObject]
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

/-- The source scope used by the three concrete deleted-write fixtures. -/
def deletedWriteScopeIndex :
    Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex :=
  Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
    (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
      (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        (Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
        dead)
      usizeField)
    scalarField

/-- Exact transparent provenance for the complete deleted-write chain. -/
def deletedWritesExactGraph :
    ExactShadowCodeGraph 4 neutralUsed
      deletedWritesBefore deletedWritesAfter :=
  ExactShadowCodeGraph.ofResult deletedWritesShadowRun

/-- Exact transparent provenance for the closed setup and deleted-write
chain. -/
def closedWritesExactGraph :
    ExactShadowCodeGraph 8 neutralUsed
      closedWritesBefore closedWritesAfter :=
  ExactShadowCodeGraph.ofResult closedWritesShadowRun

/-- Exact transparent provenance for the unboxed/scalar suffix. -/
def deletedUSizeScalarExactGraph :
    ExactShadowCodeGraph 3 neutralUsed
      (.uset dead 1 usizeField <|
        .sset dead 8 0 scalarField u8Type <| .return live)
      deletedWritesAfter :=
  ExactShadowCodeGraph.ofResult deletedUSizeScalarShadowRun

/-- Exact transparent provenance for the scalar suffix. -/
def deletedScalarExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      (.sset dead 8 0 scalarField u8Type <| .return live)
      deletedWritesAfter :=
  ExactShadowCodeGraph.ofResult deletedScalarShadowRun

/-- Hereditary static readiness for the complete exact deleted-write chain. -/
theorem deletedWritesExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedWritesExactGraph.view := by
  apply deletedWritesExactGraph.binderReady_of_canonical
    (index := deletedWriteScopeIndex)
  · apply ScopedCodeWellFormedTree.oset
    · native_decide
    · native_decide
    · apply ScopedCodeWellFormedTree.uset
      · native_decide
      · native_decide
      · apply ScopedCodeWellFormedTree.sset
        · native_decide
        · native_decide
        · apply ScopedCodeWellFormedTree.ret
          native_decide
  · simp [deletedWritesBefore, codeBinderIds, BinderNamesUnique]

/-- Hereditary static readiness for the closed setup and all three writes. -/
theorem closedWritesExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      closedWritesExactGraph.view := by
  apply closedWritesExactGraph.binderReady_of_canonical
    (index := Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.letE
      · native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · exact ⟨.object, trivial⟩
      · apply ScopedCodeWellFormedTree.letE
        · native_decide
        · apply freshForScope_of_not_contains
          native_decide
        · apply freshForScope_of_not_contains
          native_decide
        · exact ⟨.usize, trivial⟩
        · apply ScopedCodeWellFormedTree.letE
          · native_decide
          · apply freshForScope_of_not_contains
            native_decide
          · apply freshForScope_of_not_contains
            native_decide
          · exact ⟨.uint8, trivial⟩
          · apply ScopedCodeWellFormedTree.oset
            · native_decide
            · native_decide
            · apply ScopedCodeWellFormedTree.uset
              · native_decide
              · native_decide
              · apply ScopedCodeWellFormedTree.sset
                · native_decide
                · native_decide
                · apply ScopedCodeWellFormedTree.ret
                  native_decide
  · simp [closedWritesBefore, deletedWritesBefore, liveDecl,
      closedWritesObjectDecl, closedWritesUSizeDecl,
      closedWritesScalarDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead, usizeField, scalarField]

/-- Hereditary static readiness for the exact unboxed/scalar suffix. -/
theorem deletedUSizeScalarExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedUSizeScalarExactGraph.view := by
  apply deletedUSizeScalarExactGraph.binderReady_of_canonical
    (index := deletedWriteScopeIndex)
  · apply ScopedCodeWellFormedTree.uset
    · native_decide
    · native_decide
    · apply ScopedCodeWellFormedTree.sset
      · native_decide
      · native_decide
      · apply ScopedCodeWellFormedTree.ret
        native_decide
  · simp [codeBinderIds, BinderNamesUnique]

/-- Hereditary static readiness for the exact scalar suffix. -/
theorem deletedScalarExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      deletedScalarExactGraph.view := by
  apply deletedScalarExactGraph.binderReady_of_canonical
    (index := deletedWriteScopeIndex)
  · apply ScopedCodeWellFormedTree.sset
    · native_decide
    · native_decide
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [codeBinderIds, BinderNamesUnique]

/-- Exact active-code readiness for the deleted object write. -/
theorem deletedObjectSetExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 4 neutralUsed
      deletedObjectSetSourceState
      (runtimeRoots deletedObjectSetSourceState.runtime
        (envRootsOn neutralUsed deletedObjectSetSourceState.env ++ []))
      deletedWritesBefore deletedWritesAfter := by
  refine ⟨4, neutralUsed, Nat.le_refl 4,
    deletedWritesExactGraph, UsedSubset.refl neutralUsed,
    deletedWritesExactBinderReady, ?_⟩
  have decision :
      deletedWritesExactGraph.view.runtimeDecision =
        .deletedObjectSet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedObjectSet_of_target_not_oset
      deletedWritesExactGraph.view
        (by
          intro targetObject targetIndex targetField targetContinuation
          simp [deletedWritesAfter])
  exact ExactShadowCodeRuntimeReadyAt.objectSetDeleted decision
    (by simpa using deletedObjectSetReady)

/-- Exact active-code readiness for the deleted unboxed write. -/
theorem deletedUSizeSetExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 4 neutralUsed
      deletedUSizeSetSourceState
      (runtimeRoots deletedUSizeSetSourceState.runtime
        (envRootsOn neutralUsed deletedUSizeSetSourceState.env ++ []))
      (.uset dead 1 usizeField <|
        .sset dead 8 0 scalarField u8Type <| .return live)
      deletedWritesAfter := by
  refine ⟨3, neutralUsed, by omega,
    deletedUSizeScalarExactGraph, UsedSubset.refl neutralUsed,
    deletedUSizeScalarExactBinderReady, ?_⟩
  have decision :
      deletedUSizeScalarExactGraph.view.runtimeDecision =
        .deletedUSizeSet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedUSizeSet_of_target_not_uset
      deletedUSizeScalarExactGraph.view
        (by
          intro targetObject targetIndex targetField targetContinuation
          simp [deletedWritesAfter])
  exact ExactShadowCodeRuntimeReadyAt.usizeSetDeleted decision
    (by simpa using deletedUSizeSetReady)

/-- Exact active-code readiness for the deleted scalar write. -/
theorem deletedScalarSetExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 4 neutralUsed
      deletedScalarSetSourceState
      (runtimeRoots deletedScalarSetSourceState.runtime
        (envRootsOn neutralUsed deletedScalarSetSourceState.env ++ []))
      (.sset dead 8 0 scalarField u8Type <| .return live)
      deletedWritesAfter := by
  refine ⟨2, neutralUsed, by omega,
    deletedScalarExactGraph, UsedSubset.refl neutralUsed,
    deletedScalarExactBinderReady, ?_⟩
  have decision :
      deletedScalarExactGraph.view.runtimeDecision =
        .deletedScalarSet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedScalarSet_of_target_not_sset
      deletedScalarExactGraph.view
        (by
          intro targetObject targetWidth targetOffset targetField targetType
            targetContinuation
          simp [deletedWritesAfter])
  exact ExactShadowCodeRuntimeReadyAt.scalarSetDeleted decision
    (by simpa using deletedScalarSetReady)

/-- The deleted-write fixture retains its exact hereditary compiler graph at
the declaration/program boundary. -/
theorem deletedWritesProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 4)
      deletedWritesBeforeProgram deletedWritesAfterProgram := by
  unfold ProgramRelated
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated 4))
    [fixtureDecl `main deletedWritesBefore]
    [fixtureDecl `main deletedWritesAfter]
  apply ListRel.cons
  · exact {
      name_eq := rfl
      levelParams_eq := rfl
      type_eq := rfl
      params_eq := rfl
      safe_eq := rfl
      value := .code ⟨neutralUsed, 4, neutralUsed, Nat.le_refl 4,
        deletedWritesExactGraph, UsedSubset.refl neutralUsed,
        deletedWritesExactBinderReady⟩
      recursive_eq := rfl
      inlineAttr_eq := rfl
    }
  · exact .nil

/-- The closed fixture retains exact hereditary compiler provenance through
its declaration/program wrapper. -/
theorem closedWritesProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 8)
      closedWritesBeforeProgram closedWritesAfterProgram := by
  simpa [closedWritesBeforeProgram, closedWritesAfterProgram] using
    fixtureProgram_binderReadyRelated (name := `main)
      (⟨neutralUsed, 8, neutralUsed, Nat.le_refl 8,
        closedWritesExactGraph, UsedSubset.refl neutralUsed,
        closedWritesExactBinderReady⟩ :
        BinderReadyShadowCodeRelated 8
          closedWritesBefore closedWritesAfter)

/-- Full exact-provenance machine readiness at the deleted object write. -/
theorem deletedObjectSetExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 4
      deletedObjectSetSourceState deletedWritesTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedObjectSetSourceState.env,
    envRootsOn neutralUsed deletedWritesTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramBinderReadyRelated
  · exact .code deletedObjectSetExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 4 neutralUsed)
      (by
        simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
          deletedWriteEnvReachableRelated)
  · simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated

/-- Full exact-provenance machine readiness at the deleted unboxed write. -/
theorem deletedUSizeSetExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 4
      deletedUSizeSetSourceState deletedWritesTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedUSizeSetSourceState.env,
    envRootsOn neutralUsed deletedWritesTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramBinderReadyRelated
  · exact .code deletedUSizeSetExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 4 neutralUsed)
      (by
        simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
          deletedWriteEnvReachableRelated)
  · simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated

/-- Full exact-provenance machine readiness at the deleted scalar write. -/
theorem deletedScalarSetExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 4
      deletedScalarSetSourceState deletedWritesTargetState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed deletedScalarSetSourceState.env,
    envRootsOn neutralUsed deletedWritesTargetState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramBinderReadyRelated
  · exact .code deletedScalarSetExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 4 neutralUsed)
      (by
        simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
          deletedWriteEnvReachableRelated)
  · simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated

/-- The exact dispatcher preserves hereditary provenance across the deleted
object write. -/
theorem deletedObjectSetExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedObjectSetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedWritesTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 4 sourceAfter targetAfter :=
  deletedObjectSetExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedObjectSetExactMachineReadyAt rfl step

/-- The exact dispatcher preserves hereditary provenance across the deleted
unboxed write. -/
theorem deletedUSizeSetExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedUSizeSetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedWritesTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 4 sourceAfter targetAfter :=
  deletedUSizeSetExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedUSizeSetExactMachineReadyAt rfl step

/-- The exact dispatcher preserves hereditary provenance across the deleted
scalar write. -/
theorem deletedScalarSetExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedScalarSetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedWritesTargetState targetAfter ∧
        SomeBinderReadyReachableMachineRelated 4 sourceAfter targetAfter :=
  deletedScalarSetExactMachineReadyAt.related.matchCodeStep_of_ready
    deletedScalarSetExactMachineReadyAt rfl step

/-- The first mutation in the closed regression takes one source step while
the transformed target stutters at the live return. -/
theorem deletedObjectSetSourceOnlyMachineStep :
    ∃ nextRuntime,
      let sourceAfter := {
        deletedObjectSetSourceState with
        runtime := nextRuntime
        control := .code (.uset dead 1 usizeField <|
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
    (sourceContinuation := .uset dead 1 usizeField <|
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

/-- Entry state after resolving the allocating fixture's `main`
declaration. -/
def allocatingSourceOuterState (arguments : Array Value) : MachineState :=
  { program := allocatingBeforeProgram
    control := .code allocatingBefore
    frames := neutralEntryFrames arguments }

/-- Target state after resolving the allocating fixture's `main`
declaration.  The retained outer let is still active on both sides. -/
def allocatingTargetOuterState (arguments : Array Value) : MachineState :=
  { program := allocatingAfterProgram
    control := .code allocatingAfter
    frames := neutralEntryFrames arguments }

/-- Active state after evaluating the fixture's retained live binding. -/
def allocatingSourceInnerStateAt
    (arguments : Array Value) : MachineState :=
  { program := allocatingBeforeProgram
    control := .code (.let deadCtorDecl (.return live))
    env := liveEnv
    frames := neutralEntryFrames arguments }

/-- Target counterpart of `allocatingSourceInnerStateAt`.  The target has
already deleted the inner constructor and therefore waits at its return. -/
def allocatingTargetInnerStateAt
    (arguments : Array Value) : MachineState :=
  { program := allocatingAfterProgram
    control := .code (.return live)
    env := liveEnv
    frames := neutralEntryFrames arguments }

/-- The declaration-entry frame is hereditarily related to itself whenever
its saved application arguments are related. -/
theorem allocatingEntryFramesBinderReadyRelated
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    ∃ roots,
      BinderReadyReachableFramesRelated 3 emptyAddressRenaming
        (neutralEntryFrames arguments) (neutralEntryFrames arguments)
        roots roots := by
  unfold neutralEntryFrames
  split
  · refine ⟨[], ?_⟩
    simpa using
      (BinderReadyReachableFramesRelated.cons
        (BinderReadyReachableFrameRelated.cache (fuel := 3)
          (rho := emptyAddressRenaming) `main)
        (BinderReadyReachableFramesRelated.nil :
          BinderReadyReachableFramesRelated
            3 emptyAddressRenaming [] [] [] []))
  · refine ⟨arguments.toList, ?_⟩
    simpa using
      (BinderReadyReachableFramesRelated.cons
        (BinderReadyReachableFrameRelated.apply
          (fuel := 3) argumentsRelated)
        (BinderReadyReachableFramesRelated.nil :
          BinderReadyReachableFramesRelated
            3 emptyAddressRenaming [] [] [] []))

/-- Exact active-code readiness at the retained outer let.  Its erased value
is dynamically ready under either exact let decision; compiler provenance
selects the retained branch. -/
theorem allocatingOuterExactCodeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    BinderReadyShadowCodeReadyAt 3 neutralUsed
      (allocatingSourceOuterState arguments)
      (runtimeRoots (allocatingSourceOuterState arguments).runtime
        (envRootsOn neutralUsed
          (allocatingSourceOuterState arguments).env ++ sourceFrameRoots))
      allocatingBefore allocatingAfter := by
  refine ⟨3, neutralUsed, Nat.le_refl 3,
    allocatingExactGraph, UsedSubset.refl neutralUsed,
    allocatingExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt (allocatingSourceOuterState arguments)
        (runtimeRoots (allocatingSourceOuterState arguments).runtime
          (envRootsOn neutralUsed
            (allocatingSourceOuterState arguments).env ++ sourceFrameRoots))
        liveDecl := by
    exact .runtimeNeutral liveDecl .erased rfl
  have kept :
      RetainedLetReadyAt (allocatingSourceOuterState arguments)
        (runtimeRoots (allocatingSourceOuterState arguments).runtime
          (envRootsOn neutralUsed
            (allocatingSourceOuterState arguments).env ++ sourceFrameRoots))
        liveDecl.value := by
    trivial
  exact ExactShadowCodeRuntimeReadyAt.let_of_ready removed kept

/-- Exact active-code readiness at the deleted inner constructor, generalized
to the declaration-entry frame roots carried by a full execution. -/
theorem deletedCtorExactCodeReadyAtWithFrames
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    BinderReadyShadowCodeReadyAt 3 neutralUsed
      (allocatingSourceInnerStateAt arguments)
      (runtimeRoots (allocatingSourceInnerStateAt arguments).runtime
        (envRootsOn neutralUsed
          (allocatingSourceInnerStateAt arguments).env ++ sourceFrameRoots))
      (.let deadCtorDecl (.return live)) (.return live) := by
  refine ⟨2, neutralUsed, by omega,
    deletedCtorExactGraph, UsedSubset.refl neutralUsed,
    deletedCtorExactBinderReady, ?_⟩
  have constructorReady :
      DeletedCtorReadyAt (allocatingSourceInnerStateAt arguments)
        oneFieldInfo #[.fvar live] := by
    refine .mk #[.erased] ?_ rfl
    simp [allocatingSourceInnerStateAt, liveEnv, evalArgs, evalArg]
    rfl
  have removed :
      DeletedLetReadyAt (allocatingSourceInnerStateAt arguments)
        (runtimeRoots (allocatingSourceInnerStateAt arguments).runtime
          (envRootsOn neutralUsed
            (allocatingSourceInnerStateAt arguments).env ++ sourceFrameRoots))
        deadCtorDecl := by
    unfold deadCtorDecl letDecl
    exact .constructor dead dead.name objType oneFieldInfo
      #[.fvar live] constructorReady
  have decision :
      deletedCtorExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedCtorExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp)
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision removed

/-- Full exact-provenance readiness for the retained outer state, including
the cache/apply frame introduced by declaration entry. -/
theorem allocatingOuterExactMachineReadyAt
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    BinderReadyReachableMachineReadyAt 3
      (allocatingSourceOuterState arguments)
      (allocatingTargetOuterState arguments) := by
  rcases allocatingEntryFramesBinderReadyRelated argumentsRelated with
    ⟨frameRoots, frames⟩
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed (allocatingSourceOuterState arguments).env,
    envRootsOn neutralUsed (allocatingTargetOuterState arguments).env,
    frameRoots, frameRoots, ?_, ?_, frames, ?_⟩
  · simpa [allocatingSourceOuterState, allocatingTargetOuterState] using
      allocatingProgramBinderReadyRelated
  · exact .code (allocatingOuterExactCodeReadyAt arguments frameRoots)
      (BinderReadyShadowJoinEnvRelated.empty 3 neutralUsed)
      (EnvRelOn.empty emptyAddressRenaming neutralUsed)
  · simpa [allocatingSourceOuterState, allocatingTargetOuterState] using
      emptyRuntime_shadowRelated_of_roots
        (listRel_append
          (envRootsOn_related
          (EnvRelOn.empty emptyAddressRenaming neutralUsed))
          frames.roots)

/-- Exact hereditary readiness starts at the canonical declaration
invocation, before `main` has been resolved on either side. -/
theorem allocatingInitialExactMachineReadyAt
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    BinderReadyReachableMachineReadyAt 3
      (initialState allocatingBeforeProgram `main arguments)
      (initialState allocatingAfterProgram `main arguments) :=
  initialState_binderReadyReachableMachineReadyAt
    allocatingProgramBinderReadyRelated argumentsRelated

/-- Full exact-provenance readiness at the destination inner edge, with the
same saved declaration-entry frame. -/
theorem deletedCtorExactMachineReadyAtWithFrames
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    BinderReadyReachableMachineReadyAt 3
      (allocatingSourceInnerStateAt arguments)
      (allocatingTargetInnerStateAt arguments) := by
  rcases allocatingEntryFramesBinderReadyRelated argumentsRelated with
    ⟨frameRoots, frames⟩
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed (allocatingSourceInnerStateAt arguments).env,
    envRootsOn neutralUsed (allocatingTargetInnerStateAt arguments).env,
    frameRoots, frameRoots, ?_, ?_, frames, ?_⟩
  · simpa [allocatingSourceInnerStateAt, allocatingTargetInnerStateAt] using
      allocatingProgramBinderReadyRelated
  · exact .code
      (deletedCtorExactCodeReadyAtWithFrames arguments frameRoots)
      (BinderReadyShadowJoinEnvRelated.empty 3 neutralUsed)
      (by
        simpa [allocatingSourceInnerStateAt,
          allocatingTargetInnerStateAt] using liveEnvReachableRelated)
  · simpa [allocatingSourceInnerStateAt,
      allocatingTargetInnerStateAt] using
        emptyRuntime_shadowRelated_of_roots
          (listRel_append
            (envRootsOn_related liveEnvReachableRelated) frames.roots)

/-- State after the source allocates the constructor that the target
deletes.  Both the allocation result and its fresh runtime are explicit so
the finite execution invariant does not assume a concrete allocator
implementation. -/
def allocatingSourceReturnState (arguments : Array Value)
    (nextRuntime : RuntimeState) (deadValue : Value) : MachineState :=
  { program := allocatingBeforeProgram
    control := .code (.return live)
    env := bind liveEnv dead deadValue
    runtime := nextRuntime
    frames := neutralEntryFrames arguments }

def allocatingSourceYieldedState (arguments : Array Value)
    (nextRuntime : RuntimeState) (deadValue : Value) : MachineState :=
  { program := allocatingBeforeProgram
    control := .yielded .erased
    env := bind liveEnv dead deadValue
    runtime := nextRuntime
    frames := neutralEntryFrames arguments }

def allocatingSourceCachedState
    (nextRuntime : RuntimeState) (deadValue : Value) : MachineState :=
  { program := allocatingBeforeProgram
    control := .yielded .erased
    env := bind liveEnv dead deadValue
    runtime := nextRuntime.setGlobal `main .erased }

def allocatingSourceInvokingState (arguments : Array Value)
    (nextRuntime : RuntimeState) (deadValue : Value) : MachineState :=
  { program := allocatingBeforeProgram
    control := .invokeValue .erased arguments
    env := bind liveEnv dead deadValue
    runtime := nextRuntime }

theorem allocatingSourceEntryStep (arguments : Array Value) :
    coreStep (initialState allocatingBeforeProgram `main arguments) =
      .next (allocatingSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, allocatingBeforeProgram,
      Program.findDecl?, invokeDecl, allocatingSourceOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

/-- Resolving the entry declaration preserves exact hereditary provenance
and reaches a pair whose active retained-let edge is ready. -/
theorem allocatingInitialExactStepPreserved
    (externals : ExternalSpec)
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        (initialState allocatingAfterProgram `main arguments) targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3
        (allocatingSourceOuterState arguments) targetAfter :=
  (allocatingInitialExactMachineReadyAt argumentsRelated).related
    |>.matchNextStep_of_ready
      (allocatingInitialExactMachineReadyAt argumentsRelated)
      (allocatingSourceEntryStep arguments)

theorem allocatingSourceOuterStep (arguments : Array Value) :
    coreStep (allocatingSourceOuterState arguments) =
      .next (allocatingSourceInnerStateAt arguments) := by
  rfl

theorem allocatingTargetOuterStep (arguments : Array Value) :
    coreStep (allocatingTargetOuterState arguments) =
      .next (allocatingTargetInnerStateAt arguments) := by
  rfl

/-- The exact dispatcher preserves hereditary provenance across the retained
outer let edge and reaches the already-ready deleted constructor edge. -/
theorem allocatingOuterExactStepPreserved
    (externals : ExternalSpec)
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments)
    {sourceAfter : MachineState}
    (step : Step externals
      (allocatingSourceOuterState arguments) sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        (allocatingTargetOuterState arguments) targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter :=
  (allocatingOuterExactMachineReadyAt argumentsRelated).related
    |>.matchCodeStep_of_ready
      (allocatingOuterExactMachineReadyAt argumentsRelated) rfl step

/-- Target state after resolving the neutral fixture's `main` declaration. -/
def neutralTargetOuterState (arguments : Array Value) : MachineState :=
  { program := neutralAfterProgram
    control := .code neutralAfter
    frames := neutralEntryFrames arguments }

/-- Target state after both machines evaluate the retained outer erased
binding.  The source still has its dead erased let; the target is at return. -/
def neutralTargetInnerState (arguments : Array Value) : MachineState :=
  { program := neutralAfterProgram
    control := .code (.return live)
    env := liveEnv
    frames := neutralEntryFrames arguments }

/-- Transparent exact run for the deleted inner erased binding. -/
theorem neutralInnerShadowRun :
    shadowCode? 2 {} (.let deadErasedDecl (.return live)) =
      some (.return live, neutralUsed) := by
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deadErasedDecl, letDecl, neutralUsed, shadowCode?, safeToElim,
    deadAbsent]

/-- Exact compiler provenance for the complete retained/deleted neutral
fixture. -/
def neutralExactGraph :
    ExactShadowCodeGraph 3 neutralUsed neutralBefore neutralAfter :=
  ExactShadowCodeGraph.ofResult neutralShadowRun

/-- Exact compiler provenance for the inner source-only erased let. -/
def neutralInnerExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      (.let deadErasedDecl (.return live)) (.return live) :=
  ExactShadowCodeGraph.ofResult neutralInnerShadowRun

/-- Hereditary static readiness for the complete neutral graph. -/
theorem neutralExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed neutralExactGraph.view := by
  apply neutralExactGraph.binderReady_of_canonical
    (index := Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.letE
      · native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · exact ⟨.object, trivial⟩
      · apply ScopedCodeWellFormedTree.ret
        native_decide
  · simp [neutralBefore, liveDecl, deadErasedDecl, letDecl,
      codeBinderIds, BinderNamesUnique, live, dead]

/-- Hereditary static readiness for the deleted inner erased let. -/
theorem neutralInnerExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      neutralInnerExactGraph.view := by
  apply neutralInnerExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [deadErasedDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead]

/-- Exact hereditary relation for the neutral fixture's single declaration. -/
theorem neutralProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 3)
      neutralBeforeProgram neutralAfterProgram := by
  simpa [neutralBeforeProgram, neutralAfterProgram] using
    fixtureProgram_binderReadyRelated (name := `main)
      (⟨neutralUsed, 3, neutralUsed, Nat.le_refl 3,
        neutralExactGraph, UsedSubset.refl neutralUsed,
        neutralExactBinderReady⟩ :
        BinderReadyShadowCodeRelated 3 neutralBefore neutralAfter)

/-- Exact active-code readiness at the retained outer erased let. -/
theorem neutralOuterExactCodeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    BinderReadyShadowCodeReadyAt 3 neutralUsed
      (neutralSourceOuterState arguments)
      (runtimeRoots (neutralSourceOuterState arguments).runtime
        (envRootsOn neutralUsed
          (neutralSourceOuterState arguments).env ++ sourceFrameRoots))
      neutralBefore neutralAfter := by
  refine ⟨3, neutralUsed, Nat.le_refl 3,
    neutralExactGraph, UsedSubset.refl neutralUsed,
    neutralExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt (neutralSourceOuterState arguments)
        (runtimeRoots (neutralSourceOuterState arguments).runtime
          (envRootsOn neutralUsed
            (neutralSourceOuterState arguments).env ++ sourceFrameRoots))
        liveDecl := by
    exact .runtimeNeutral liveDecl .erased rfl
  have kept :
      RetainedLetReadyAt (neutralSourceOuterState arguments)
        (runtimeRoots (neutralSourceOuterState arguments).runtime
          (envRootsOn neutralUsed
            (neutralSourceOuterState arguments).env ++ sourceFrameRoots))
        liveDecl.value := by
    trivial
  exact ExactShadowCodeRuntimeReadyAt.let_of_ready removed kept

/-- Exact active-code readiness at the deleted inner erased let. -/
theorem neutralInnerExactCodeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    BinderReadyShadowCodeReadyAt 3 neutralUsed
      (neutralSourceInnerState arguments)
      (runtimeRoots (neutralSourceInnerState arguments).runtime
        (envRootsOn neutralUsed
          (neutralSourceInnerState arguments).env ++ sourceFrameRoots))
      (.let deadErasedDecl (.return live)) (.return live) := by
  refine ⟨2, neutralUsed, by omega,
    neutralInnerExactGraph, UsedSubset.refl neutralUsed,
    neutralInnerExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt (neutralSourceInnerState arguments)
        (runtimeRoots (neutralSourceInnerState arguments).runtime
          (envRootsOn neutralUsed
            (neutralSourceInnerState arguments).env ++ sourceFrameRoots))
        deadErasedDecl := by
    exact .runtimeNeutral deadErasedDecl .erased rfl
  have decision :
      neutralInnerExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      neutralInnerExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp)
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision removed

/-- Exact readiness at the canonical invocation control. -/
theorem neutralInitialExactMachineReadyAt
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    BinderReadyReachableMachineReadyAt 3
      (initialState neutralBeforeProgram `main arguments)
      (initialState neutralAfterProgram `main arguments) :=
  initialState_binderReadyReachableMachineReadyAt
    neutralProgramBinderReadyRelated argumentsRelated

/-- Full exact-provenance readiness at the retained outer let. -/
theorem neutralOuterExactMachineReadyAt
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    BinderReadyReachableMachineReadyAt 3
      (neutralSourceOuterState arguments)
      (neutralTargetOuterState arguments) := by
  rcases allocatingEntryFramesBinderReadyRelated argumentsRelated with
    ⟨frameRoots, frames⟩
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed (neutralSourceOuterState arguments).env,
    envRootsOn neutralUsed (neutralTargetOuterState arguments).env,
    frameRoots, frameRoots, ?_, ?_, frames, ?_⟩
  · simpa [neutralSourceOuterState, neutralTargetOuterState] using
      neutralProgramBinderReadyRelated
  · exact .code (neutralOuterExactCodeReadyAt arguments frameRoots)
      (BinderReadyShadowJoinEnvRelated.empty 3 neutralUsed)
      (EnvRelOn.empty emptyAddressRenaming neutralUsed)
  · simpa [neutralSourceOuterState, neutralTargetOuterState] using
      emptyRuntime_shadowRelated_of_roots
        (listRel_append
          (envRootsOn_related
            (EnvRelOn.empty emptyAddressRenaming neutralUsed))
          frames.roots)

/-- Full exact-provenance readiness at the deleted inner erased let. -/
theorem neutralInnerExactMachineReadyAt
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    BinderReadyReachableMachineReadyAt 3
      (neutralSourceInnerState arguments)
      (neutralTargetInnerState arguments) := by
  rcases allocatingEntryFramesBinderReadyRelated argumentsRelated with
    ⟨frameRoots, frames⟩
  refine ⟨emptyAddressRenaming,
    envRootsOn neutralUsed (neutralSourceInnerState arguments).env,
    envRootsOn neutralUsed (neutralTargetInnerState arguments).env,
    frameRoots, frameRoots, ?_, ?_, frames, ?_⟩
  · simpa [neutralSourceInnerState, neutralTargetInnerState] using
      neutralProgramBinderReadyRelated
  · exact .code (neutralInnerExactCodeReadyAt arguments frameRoots)
      (BinderReadyShadowJoinEnvRelated.empty 3 neutralUsed)
      (by
        simpa [neutralSourceInnerState, neutralTargetInnerState,
          liveEnv] using liveEnvReachableRelated)
  · simpa [neutralSourceInnerState, neutralTargetInnerState,
      liveEnv] using
        emptyRuntime_shadowRelated_of_roots
          (listRel_append
            (envRootsOn_related liveEnvReachableRelated) frames.roots)

/-- Resolving `main` preserves exact provenance and reaches the ready retained
outer let pair. -/
theorem neutralInitialExactStepPreserved
    (externals : ExternalSpec)
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        (initialState neutralAfterProgram `main arguments) targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3
        (neutralSourceOuterState arguments) targetAfter :=
  (neutralInitialExactMachineReadyAt argumentsRelated).related
    |>.matchNextStep_of_ready
      (neutralInitialExactMachineReadyAt argumentsRelated)
      (neutralSourceEntryStep arguments)

/-- Concrete target step across the retained outer erased let. -/
theorem neutralTargetOuterStep (arguments : Array Value) :
    coreStep (neutralTargetOuterState arguments) =
      .next (neutralTargetInnerState arguments) := by
  rfl

/-- The dispatcher preserves exact provenance across the retained outer let. -/
theorem neutralOuterExactStepPreserved
    (externals : ExternalSpec)
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments)
    {sourceAfter : MachineState}
    (step : Step externals
      (neutralSourceOuterState arguments) sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        (neutralTargetOuterState arguments) targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter :=
  (neutralOuterExactMachineReadyAt argumentsRelated).related
    |>.matchCodeStep_of_ready
      (neutralOuterExactMachineReadyAt argumentsRelated) rfl step

/-- The dispatcher preserves exact provenance across the source-only inner
erased let while the target stutters at return. -/
theorem neutralInnerExactStepPreserved
    (externals : ExternalSpec)
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments)
    {sourceAfter : MachineState}
    (step : Step externals
      (neutralSourceInnerState arguments) sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        (neutralTargetInnerState arguments) targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter :=
  (neutralInnerExactMachineReadyAt argumentsRelated).related
    |>.matchCodeStep_of_ready
      (neutralInnerExactMachineReadyAt argumentsRelated) rfl step

/-- Composed exact neutral regression: one retained lockstep edge followed by
one source-only deleted edge reaches related endpoints. -/
theorem neutralTwoActiveStepsExactPreserved
    (externals : ExternalSpec)
    (argumentsRelated :
      ArrayRel (ValueRel emptyAddressRenaming) arguments arguments) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        (neutralSourceOuterState arguments)
        (neutralSourceReturnState arguments) ∧
      NonLockstep.Reaches externals
        (neutralTargetOuterState arguments) targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3
        (neutralSourceReturnState arguments) targetAfter := by
  rcases neutralInnerExactStepPreserved externals argumentsRelated
      (.internal (neutralSourceInnerStep arguments)) with
    ⟨targetAfter, targetTail, endpoint⟩
  refine ⟨targetAfter, ?_, ?_, endpoint⟩
  · exact
      (NonLockstep.reaches_of_step
        (.internal (neutralSourceOuterStep arguments))).trans
      (NonLockstep.reaches_of_step
        (.internal (neutralSourceInnerStep arguments)))
  · exact
      (NonLockstep.reaches_of_step
        (.internal (neutralTargetOuterStep arguments))).trans targetTail

/-- Final liveness set of the fixture whose result directly uses its only
let binder. -/
def usedResultUsed : UsedLocals :=
  ({} : UsedLocals).insert dead

/-- Exact implementation-level liveness result for the unsafe local copy.
`HashSet.insert` preserves the existing element internally, but the proof
records the compiler's two syntactic insertions without assuming a
proof-irrelevant extensional representation for hash sets. -/
def unsafeResultUsed : UsedLocals :=
  (({} : UsedLocals).insert live).insert live

/-- The transparent traversal retains a binder that is live in the return. -/
theorem usedShadowRun :
    shadowCode? 2 {} usedBefore =
      some (usedBefore, usedResultUsed) := by
  change shadowCode? 2 {} usedBefore =
    some (usedBefore, ({} : UsedLocals).insert dead)
  have deadMember : dead ∈ ({} : UsedLocals).insert dead := by
    native_decide
  simp [usedBefore, deadErasedDecl, letDecl, shadowCode?, safeToElim,
    collectLetValue, deadMember]

/-- The transparent traversal also retains an otherwise-dead local copy,
because local-function application is not safe to erase. -/
theorem unsafeShadowRun :
    shadowCode? 3 {} unsafeBefore =
      some (unsafeBefore, unsafeResultUsed) := by
  change shadowCode? 3 {} unsafeBefore =
    some (unsafeBefore, (({} : UsedLocals).insert live).insert live)
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  simp [unsafeBefore, liveDecl, deadCopyDecl, letDecl, shadowCode?,
    safeToElim, collectLetValue, collectArgs, collectArgList, liveMember]

/-- Exact residual run at the unsafe fixture's inner retained local copy. -/
theorem unsafeInnerShadowRun :
    shadowCode? 2 {} (.let deadCopyDecl (.return live)) =
      some (.let deadCopyDecl (.return live), unsafeResultUsed) := by
  simp [deadCopyDecl, letDecl, unsafeResultUsed, shadowCode?, safeToElim,
    collectLetValue, collectArgs, collectArgList]

/-- Active identical machines for the live-binder retention fixture. -/
def usedActiveState : MachineState :=
  { program := usedProgram
    control := .code usedBefore }

def usedReturnState : MachineState :=
  { program := usedProgram
    control := .code (.return dead)
    env := bind [] dead .erased }

/-- First and second active states of the unsafe-retention fixture. -/
def unsafeOuterState : MachineState :=
  { program := unsafeProgram
    control := .code unsafeBefore }

def unsafeInnerState : MachineState :=
  { program := unsafeProgram
    control := .code (.let deadCopyDecl (.return live))
    env := liveEnv }

def unsafeReturnState : MachineState :=
  { program := unsafeProgram
    control := .code (.return live)
    env := bind liveEnv dead .erased }

def usedExactGraph :
    ExactShadowCodeGraph 2 usedResultUsed usedBefore usedBefore :=
  ExactShadowCodeGraph.ofResult usedShadowRun

def unsafeExactGraph :
    ExactShadowCodeGraph 3 unsafeResultUsed unsafeBefore unsafeBefore :=
  ExactShadowCodeGraph.ofResult unsafeShadowRun

def unsafeInnerExactGraph :
    ExactShadowCodeGraph 2 unsafeResultUsed
      (.let deadCopyDecl (.return live))
      (.let deadCopyDecl (.return live)) :=
  ExactShadowCodeGraph.ofResult unsafeInnerShadowRun

/-- Hereditary static readiness for the live-binder retention graph. -/
theorem usedExactBinderReady :
    ExactShadowCodeBinderReady usedResultUsed usedExactGraph.view := by
  apply usedExactGraph.binderReady_of_canonical
    (index := Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [usedBefore, deadErasedDecl, letDecl, codeBinderIds,
      BinderNamesUnique, dead]

/-- Hereditary static readiness for both retained lets in the unsafe graph. -/
theorem unsafeExactBinderReady :
    ExactShadowCodeBinderReady unsafeResultUsed unsafeExactGraph.view := by
  apply unsafeExactGraph.binderReady_of_canonical
    (index := Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.letE
      · native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · apply freshForScope_of_not_contains
        native_decide
      · exact ⟨.object, trivial⟩
      · apply ScopedCodeWellFormedTree.ret
        native_decide
  · simp [unsafeBefore, liveDecl, deadCopyDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead]

/-- Hereditary static readiness for the retained unsafe residual. -/
theorem unsafeInnerExactBinderReady :
    ExactShadowCodeBinderReady unsafeResultUsed
      unsafeInnerExactGraph.view := by
  apply unsafeInnerExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [deadCopyDecl, letDecl, codeBinderIds,
      BinderNamesUnique, live, dead]

theorem usedProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 2)
      usedProgram usedProgram := by
  simpa [usedProgram] using
    fixtureProgram_binderReadyRelated (name := `main)
      (⟨usedResultUsed, 2, usedResultUsed, Nat.le_refl 2,
        usedExactGraph, UsedSubset.refl usedResultUsed,
        usedExactBinderReady⟩ :
        BinderReadyShadowCodeRelated 2 usedBefore usedBefore)

theorem unsafeProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 3)
      unsafeProgram unsafeProgram := by
  simpa [unsafeProgram] using
    fixtureProgram_binderReadyRelated (name := `main)
      (⟨unsafeResultUsed, 3, unsafeResultUsed, Nat.le_refl 3,
        unsafeExactGraph, UsedSubset.refl unsafeResultUsed,
        unsafeExactBinderReady⟩ :
        BinderReadyShadowCodeRelated 3 unsafeBefore unsafeBefore)

/-- The inner binder is retained despite being dead because its local copy
operation is unsafe to erase. -/
theorem unsafeInnerExactDecision :
    unsafeInnerExactGraph.view.runtimeDecision = .retainedLet := by
  apply
    ExactShadowCodeView.runtimeDecision_eq_retainedLet_of_unsafe
  simp [deadCopyDecl, letDecl, safeToElim]

theorem usedExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 2 usedResultUsed usedActiveState
      (runtimeRoots usedActiveState.runtime
        (envRootsOn usedResultUsed usedActiveState.env ++ []))
      usedBefore usedBefore := by
  refine ⟨2, usedResultUsed, Nat.le_refl 2,
    usedExactGraph, UsedSubset.refl usedResultUsed,
    usedExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt usedActiveState
        (runtimeRoots usedActiveState.runtime
          (envRootsOn usedResultUsed usedActiveState.env ++ []))
        deadErasedDecl := by
    exact .runtimeNeutral deadErasedDecl .erased rfl
  have kept :
      RetainedLetReadyAt usedActiveState
        (runtimeRoots usedActiveState.runtime
          (envRootsOn usedResultUsed usedActiveState.env ++ []))
        deadErasedDecl.value := by
    trivial
  exact ExactShadowCodeRuntimeReadyAt.let_of_ready removed kept

theorem unsafeOuterExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 3 unsafeResultUsed unsafeOuterState
      (runtimeRoots unsafeOuterState.runtime
        (envRootsOn unsafeResultUsed unsafeOuterState.env ++ []))
      unsafeBefore unsafeBefore := by
  refine ⟨3, unsafeResultUsed, Nat.le_refl 3,
    unsafeExactGraph, UsedSubset.refl unsafeResultUsed,
    unsafeExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt unsafeOuterState
        (runtimeRoots unsafeOuterState.runtime
          (envRootsOn unsafeResultUsed unsafeOuterState.env ++ []))
        liveDecl := by
    exact .runtimeNeutral liveDecl .erased rfl
  have kept :
      RetainedLetReadyAt unsafeOuterState
        (runtimeRoots unsafeOuterState.runtime
          (envRootsOn unsafeResultUsed unsafeOuterState.env ++ []))
        liveDecl.value := by
    trivial
  exact ExactShadowCodeRuntimeReadyAt.let_of_ready removed kept

theorem unsafeInnerExactCodeReadyAt :
    BinderReadyShadowCodeReadyAt 3 unsafeResultUsed unsafeInnerState
      (runtimeRoots unsafeInnerState.runtime
        (envRootsOn unsafeResultUsed unsafeInnerState.env ++ []))
      (.let deadCopyDecl (.return live))
      (.let deadCopyDecl (.return live)) := by
  refine ⟨2, unsafeResultUsed, by omega,
    unsafeInnerExactGraph, UsedSubset.refl unsafeResultUsed,
    unsafeInnerExactBinderReady, ?_⟩
  exact ExactShadowCodeRuntimeReadyAt.letRetained
    unsafeInnerExactDecision (by trivial)

theorem usedExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 2
      usedActiveState usedActiveState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn usedResultUsed usedActiveState.env,
    envRootsOn usedResultUsed usedActiveState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [usedActiveState] using usedProgramBinderReadyRelated
  · exact .code usedExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 2 usedResultUsed)
      (by simpa [usedActiveState] using
        (EnvRelOn.empty emptyAddressRenaming usedResultUsed))
  · simpa [usedActiveState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related
          (EnvRelOn.empty emptyAddressRenaming usedResultUsed))

theorem unsafeOuterExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 3
      unsafeOuterState unsafeOuterState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn unsafeResultUsed unsafeOuterState.env,
    envRootsOn unsafeResultUsed unsafeOuterState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [unsafeOuterState] using unsafeProgramBinderReadyRelated
  · exact .code unsafeOuterExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 3 unsafeResultUsed)
      (by simpa [unsafeOuterState] using
        (EnvRelOn.empty emptyAddressRenaming unsafeResultUsed))
  · simpa [unsafeOuterState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related
          (EnvRelOn.empty emptyAddressRenaming unsafeResultUsed))

theorem unsafeLiveEnvReachableRelated :
    EnvRelOn emptyAddressRenaming unsafeResultUsed liveEnv liveEnv := by
  intro fvarId member
  have same : live = fvarId := by
    simpa [unsafeResultUsed] using member
  subst fvarId
  exact .some .erased

theorem unsafeInnerExactMachineReadyAt :
    BinderReadyReachableMachineReadyAt 3
      unsafeInnerState unsafeInnerState := by
  refine ⟨emptyAddressRenaming,
    envRootsOn unsafeResultUsed unsafeInnerState.env,
    envRootsOn unsafeResultUsed unsafeInnerState.env,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [unsafeInnerState] using unsafeProgramBinderReadyRelated
  · exact .code unsafeInnerExactCodeReadyAt
      (BinderReadyShadowJoinEnvRelated.empty 3 unsafeResultUsed)
      (by simpa [unsafeInnerState] using unsafeLiveEnvReachableRelated)
  · simpa [unsafeInnerState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related unsafeLiveEnvReachableRelated)

theorem usedActiveStep :
    coreStep usedActiveState = .next usedReturnState := by
  rfl

theorem unsafeOuterStep :
    coreStep unsafeOuterState = .next unsafeInnerState := by
  rfl

theorem unsafeInnerStep :
    coreStep unsafeInnerState = .next unsafeReturnState := by
  have evaluatedAt :
      evalLetValue unsafeInnerState deadCopyDecl =
        .ok (unsafeInnerState.runtime, .value .erased) := by
    simp [unsafeInnerState, deadCopyDecl, letDecl, liveEnv,
      evalLetValue, lookupValue, evalArgs, Impure.bind, lookup]
    rfl
  change coreStep {
      unsafeInnerState with
      control := .code (.let deadCopyDecl (.return live)) } =
    .next unsafeReturnState
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluatedAt]
  rfl

/-- Exact dispatcher preservation for a let retained because its binder is
live. -/
theorem usedExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals usedActiveState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals usedActiveState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 2 sourceAfter targetAfter :=
  usedExactMachineReadyAt.related.matchCodeStep_of_ready
    usedExactMachineReadyAt rfl step

/-- Exact dispatcher preservation at the unsafe fixture's outer live let. -/
theorem unsafeOuterExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals unsafeOuterState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals unsafeOuterState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter :=
  unsafeOuterExactMachineReadyAt.related.matchCodeStep_of_ready
    unsafeOuterExactMachineReadyAt rfl step

/-- Exact dispatcher preservation for the dead binder retained solely because
its local copy is unsafe to erase. -/
theorem unsafeInnerExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals unsafeInnerState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals unsafeInnerState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter :=
  unsafeInnerExactMachineReadyAt.related.matchCodeStep_of_ready
    unsafeInnerExactMachineReadyAt rfl step

/-- Composed unsafe-retention regression: both source and target execute the
live outer binding and the otherwise-dead but unsafe inner copy, preserving
exact provenance through the endpoint. -/
theorem unsafeTwoRetainedStepsExactPreserved
    (externals : ExternalSpec) :
    ∃ targetAfter,
      NonLockstep.Reaches externals unsafeOuterState unsafeReturnState ∧
      NonLockstep.Reaches externals unsafeOuterState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3
        unsafeReturnState targetAfter := by
  rcases unsafeInnerExactStepPreserved externals
      (.internal unsafeInnerStep) with
    ⟨targetAfter, targetTail, endpoint⟩
  refine ⟨targetAfter, ?_, ?_, endpoint⟩
  · exact
      (NonLockstep.reaches_of_step (.internal unsafeOuterStep)).trans
      (NonLockstep.reaches_of_step (.internal unsafeInnerStep))
  · exact
      (NonLockstep.reaches_of_step (.internal unsafeOuterStep)).trans
      targetTail

/-- The retained erased binding supplies both possible exact-view runtime
certificates, independently of the compiler's liveness decision. -/
theorem usedBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 2 state sourceFrameRoots usedBefore := by
  unfold usedBefore
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

theorem usedReturnSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 2 state sourceFrameRoots
      (.return dead) := by
  intro used remaining final targetCode bounded exact subset static
  simp [ExactShadowCodeRuntimeReadyAt]

def usedSourceOuterState (arguments : Array Value) : MachineState :=
  { program := usedProgram
    control := .code usedBefore
    frames := neutralEntryFrames arguments }

def usedSourceReturnState (arguments : Array Value) : MachineState :=
  { program := usedProgram
    control := .code (.return dead)
    env := bind [] dead .erased
    frames := neutralEntryFrames arguments }

def usedSourceYieldedState (arguments : Array Value) : MachineState :=
  { program := usedProgram
    control := .yielded .erased
    env := bind [] dead .erased
    frames := neutralEntryFrames arguments }

def usedSourceCachedState : MachineState :=
  { program := usedProgram
    control := .yielded .erased
    env := bind [] dead .erased
    runtime := ({} : RuntimeState).setGlobal `main .erased }

def usedSourceInvokingState (arguments : Array Value) : MachineState :=
  { program := usedProgram
    control := .invokeValue .erased arguments
    env := bind [] dead .erased }

theorem usedSourceEntryStep (arguments : Array Value) :
    coreStep (initialState usedProgram `main arguments) =
      .next (usedSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, usedProgram, Program.findDecl?,
      invokeDecl, usedSourceOuterState, neutralEntryFrames, fixtureDecl, decl,
      bindParams, findGlobal?]

theorem usedSourceOuterStep (arguments : Array Value) :
    coreStep (usedSourceOuterState arguments) =
      .next (usedSourceReturnState arguments) := by
  rfl

theorem usedSourceReturnStep (arguments : Array Value) :
    coreStep (usedSourceReturnState arguments) =
      .next (usedSourceYieldedState arguments) := by
  simp [coreStep, usedSourceReturnState, usedSourceYieldedState,
    lookupValue, Impure.bind, Impure.lookup, dead]

theorem usedSourceYieldedStepEmpty :
    coreStep (usedSourceYieldedState #[]) =
      .next usedSourceCachedState := by
  rfl

theorem usedSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (usedSourceYieldedState arguments) =
      .next (usedSourceInvokingState arguments) := by
  simp [coreStep, usedSourceYieldedState, neutralEntryFrames, notEmpty,
    usedSourceInvokingState]

/-- Complete finite-state characterization of source executions for the
live-binder retention fixture. -/
inductive UsedSourceReachable (arguments : Array Value) :
    MachineState → Prop where
  | entry :
      UsedSourceReachable arguments
        (initialState usedProgram `main arguments)
  | outer :
      UsedSourceReachable arguments (usedSourceOuterState arguments)
  | ret :
      UsedSourceReachable arguments (usedSourceReturnState arguments)
  | yielded :
      UsedSourceReachable arguments (usedSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      UsedSourceReachable arguments usedSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      UsedSourceReachable arguments (usedSourceInvokingState arguments)

theorem usedSourceReachable_step
    (reachable : UsedSourceReachable arguments before)
    (step : Step externals before after) :
    UsedSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (usedSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (usedSourceOuterStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (usedSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next usedSourceYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (usedSourceYieldedStepNonempty empty) (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [usedSourceCachedState, coreStep] at transition
      | external transition response =>
          simp [usedSourceCachedState, coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [usedSourceInvokingState, coreStep, invokeClosure,
            fail] at transition
      | external transition response =>
          simp [usedSourceInvokingState, coreStep, invokeClosure,
            fail] at transition

theorem usedSourceReachable_ready
    (state : MachineState)
    (reachable : UsedSourceReachable arguments state) :
    SourceRuntimeOwnershipMachineReadyAt 2 state := by
  cases reachable with
  | entry =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = usedBefore :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact usedBeforeSourceRuntimeReadyAt
        (usedSourceOuterState arguments) sourceFrameRoots
        bounded exact subset static
  | ret =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = .return dead :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact usedReturnSourceRuntimeReadyAt
        (usedSourceReturnState arguments) sourceFrameRoots
        bounded exact subset static
  | yielded =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [usedSourceYieldedState] at control
  | cached empty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [usedSourceCachedState] at control
  | invoking notEmpty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [usedSourceInvokingState] at control

theorem usedSourceRuntimeOwnershipMachineInvariant
    (externals : ExternalSpec) (arguments : Array Value) :
    SourceRuntimeOwnershipMachineInvariant externals 2
      (initialState usedProgram `main arguments) :=
  SourceRuntimeOwnershipMachineInvariant.of_inductive
    (UsedSourceReachable arguments)
    .entry usedSourceReachable_step usedSourceReachable_ready

theorem usedSourceRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    SourceRuntimeOwnershipInitialInvariantOn externals 2
      usedProgram #[`main] := by
  intro entry member arguments
  have entryEq : entry = `main := by
    simpa using member
  subst entry
  exact usedSourceRuntimeOwnershipMachineInvariant externals arguments

theorem usedProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed usedProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique, usedProgram, fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [usedProgram] at member
      subst declaration
      exact .letE .ret
    · intro declaration member
      simp [usedProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩ .ret
  · intro declaration member
    simp [usedProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl, usedBefore,
      deadErasedDecl, letDecl, codeBinderIds, BinderNamesUnique,
      ImpureHygiene.paramIds, dead]

theorem usedShadowProgramRun :
    shadowProgram? 2 usedProgram = some usedProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?, usedProgram,
    fixtureDecl, decl, usedShadowRun]

/-- Whole-program correctness when the pass retains an erased let because
its binder is live in the return. -/
theorem usedProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 2) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      usedProgram usedProgram #[`main] :=
  shadowProgram_loweringCorrect_sourceMachineInvariant
    usedProgramElimDeadWellFormed usedShadowProgramRun compatible
    (usedSourceRuntimeOwnershipInitialInvariant externals)

/-- The live outer binding of the unsafe-copy fixture is runtime-neutral
under either exact compiler decision. -/
theorem unsafeBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3 state sourceFrameRoots unsafeBefore := by
  unfold unsafeBefore
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

def unsafeSourceOuterState (arguments : Array Value) : MachineState :=
  { program := unsafeProgram
    control := .code unsafeBefore
    frames := neutralEntryFrames arguments }

def unsafeSourceInnerStateAt (arguments : Array Value) : MachineState :=
  { program := unsafeProgram
    control := .code (.let deadCopyDecl (.return live))
    env := liveEnv
    frames := neutralEntryFrames arguments }

def unsafeSourceReturnState (arguments : Array Value) : MachineState :=
  { program := unsafeProgram
    control := .code (.return live)
    env := bind liveEnv dead .erased
    frames := neutralEntryFrames arguments }

def unsafeSourceYieldedState (arguments : Array Value) : MachineState :=
  { program := unsafeProgram
    control := .yielded .erased
    env := bind liveEnv dead .erased
    frames := neutralEntryFrames arguments }

def unsafeSourceCachedState : MachineState :=
  { program := unsafeProgram
    control := .yielded .erased
    env := bind liveEnv dead .erased
    runtime := ({} : RuntimeState).setGlobal `main .erased }

def unsafeSourceInvokingState (arguments : Array Value) : MachineState :=
  { program := unsafeProgram
    control := .invokeValue .erased arguments
    env := bind liveEnv dead .erased }

/-- In the only reachable inner state, the dead local copy evaluates to the
already-published erased value without changing runtime.  This supplies the
deleted-side certificate even though the exact pass must retain the copy. -/
theorem unsafeInnerSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3
      (unsafeSourceInnerStateAt arguments) sourceFrameRoots
      (.let deadCopyDecl (.return live)) := by
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · refine ⟨.erased, ?_⟩
    simp [unsafeSourceInnerStateAt, deadCopyDecl, letDecl, liveEnv,
      evalLetValue, lookupValue, evalArgs, Impure.bind, lookup]
    rfl
  · intro roots
    trivial

theorem unsafeSourceEntryStep (arguments : Array Value) :
    coreStep (initialState unsafeProgram `main arguments) =
      .next (unsafeSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, unsafeProgram, Program.findDecl?,
      invokeDecl, unsafeSourceOuterState, neutralEntryFrames, fixtureDecl,
      decl, bindParams, findGlobal?]

theorem unsafeSourceOuterStep (arguments : Array Value) :
    coreStep (unsafeSourceOuterState arguments) =
      .next (unsafeSourceInnerStateAt arguments) := by
  rfl

theorem unsafeSourceInnerStep (arguments : Array Value) :
    coreStep (unsafeSourceInnerStateAt arguments) =
      .next (unsafeSourceReturnState arguments) := by
  have evaluatedAt :
      evalLetValue (unsafeSourceInnerStateAt arguments) deadCopyDecl =
        .ok ((unsafeSourceInnerStateAt arguments).runtime,
          .value .erased) := by
    simp [unsafeSourceInnerStateAt, deadCopyDecl, letDecl, liveEnv,
      evalLetValue, lookupValue, evalArgs, Impure.bind, lookup]
    rfl
  change coreStep {
      unsafeSourceInnerStateAt arguments with
      control := .code (.let deadCopyDecl (.return live)) } =
    .next (unsafeSourceReturnState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluatedAt]
  rfl

theorem unsafeSourceReturnStep (arguments : Array Value) :
    coreStep (unsafeSourceReturnState arguments) =
      .next (unsafeSourceYieldedState arguments) := by
  simp [coreStep, unsafeSourceReturnState, unsafeSourceYieldedState,
    liveEnv, lookupValue, Impure.bind, Impure.lookup, live, dead]

theorem unsafeSourceYieldedStepEmpty :
    coreStep (unsafeSourceYieldedState #[]) =
      .next unsafeSourceCachedState := by
  rfl

theorem unsafeSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (unsafeSourceYieldedState arguments) =
      .next (unsafeSourceInvokingState arguments) := by
  simp [coreStep, unsafeSourceYieldedState, neutralEntryFrames, notEmpty,
    unsafeSourceInvokingState]

/-- Complete finite-state characterization of source executions for the
dead-but-unsafe retained local copy. -/
inductive UnsafeSourceReachable (arguments : Array Value) :
    MachineState → Prop where
  | entry :
      UnsafeSourceReachable arguments
        (initialState unsafeProgram `main arguments)
  | outer :
      UnsafeSourceReachable arguments
        (unsafeSourceOuterState arguments)
  | inner :
      UnsafeSourceReachable arguments
        (unsafeSourceInnerStateAt arguments)
  | ret :
      UnsafeSourceReachable arguments
        (unsafeSourceReturnState arguments)
  | yielded :
      UnsafeSourceReachable arguments
        (unsafeSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      UnsafeSourceReachable arguments unsafeSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      UnsafeSourceReachable arguments
        (unsafeSourceInvokingState arguments)

theorem unsafeSourceReachable_step
    (reachable : UnsafeSourceReachable arguments before)
    (step : Step externals before after) :
    UnsafeSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (unsafeSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (unsafeSourceOuterStep arguments) .inner step
  | inner =>
      exact predicate_of_step_next
        (unsafeSourceInnerStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (unsafeSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next unsafeSourceYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (unsafeSourceYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [unsafeSourceCachedState, coreStep] at transition
      | external transition response =>
          simp [unsafeSourceCachedState, coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [unsafeSourceInvokingState, coreStep, invokeClosure,
            fail] at transition
      | external transition response =>
          simp [unsafeSourceInvokingState, coreStep, invokeClosure,
            fail] at transition

theorem unsafeSourceReachable_ready
    (state : MachineState)
    (reachable : UnsafeSourceReachable arguments state) :
    SourceRuntimeOwnershipMachineReadyAt 3 state := by
  cases reachable with
  | entry =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = unsafeBefore :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact unsafeBeforeSourceRuntimeReadyAt
        (unsafeSourceOuterState arguments) sourceFrameRoots
        bounded exact subset static
  | inner =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq :
          sourceCode = .let deadCopyDecl (.return live) :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact unsafeInnerSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | ret =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = .return live :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact neutralReturnSourceRuntimeReadyAt
        (unsafeSourceReturnState arguments) sourceFrameRoots
        bounded exact subset static
  | yielded =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [unsafeSourceYieldedState] at control
  | cached empty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [unsafeSourceCachedState] at control
  | invoking notEmpty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [unsafeSourceInvokingState] at control

theorem unsafeSourceRuntimeOwnershipMachineInvariant
    (externals : ExternalSpec) (arguments : Array Value) :
    SourceRuntimeOwnershipMachineInvariant externals 3
      (initialState unsafeProgram `main arguments) :=
  SourceRuntimeOwnershipMachineInvariant.of_inductive
    (UnsafeSourceReachable arguments)
    .entry unsafeSourceReachable_step unsafeSourceReachable_ready

theorem unsafeSourceRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    SourceRuntimeOwnershipInitialInvariantOn externals 3
      unsafeProgram #[`main] := by
  intro entry member arguments
  have entryEq : entry = `main := by
    simpa using member
  subst entry
  exact unsafeSourceRuntimeOwnershipMachineInvariant externals arguments

theorem unsafeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed unsafeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique, unsafeProgram, fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [unsafeProgram] at member
      subst declaration
      exact .letE (.letE .ret)
    · intro declaration member
      simp [unsafeProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩
        (.letE ⟨.object, trivial⟩ .ret)
  · intro declaration member
    simp [unsafeProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl, unsafeBefore,
      liveDecl, deadCopyDecl, letDecl, codeBinderIds, BinderNamesUnique,
      ImpureHygiene.paramIds, live, dead]

theorem unsafeShadowProgramRun :
    shadowProgram? 3 unsafeProgram = some unsafeProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?, unsafeProgram,
    fixtureDecl, decl, unsafeShadowRun]

/-- Whole-program correctness when the pass retains a dead local copy because
local-function application is not safe to erase. -/
theorem unsafeProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 3) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      unsafeProgram unsafeProgram #[`main] :=
  shadowProgram_loweringCorrect_sourceMachineInvariant
    unsafeProgramElimDeadWellFormed unsafeShadowProgramRun compatible
    (unsafeSourceRuntimeOwnershipInitialInvariant externals)

theorem allocatingSourceInnerStep (arguments : Array Value) :
    ∃ nextRuntime deadValue,
      coreStep (allocatingSourceInnerStateAt arguments) =
        .next
          (allocatingSourceReturnState arguments nextRuntime deadValue) := by
  rcases deadCtorEvalPreservesReachableRuntime with
    ⟨nextRuntime, deadValue, evaluated, runtime⟩
  have evaluatedAt :
      evalLetValue (allocatingSourceInnerStateAt arguments) deadCtorDecl =
        .ok (nextRuntime, .value deadValue) := by
    simpa [evalLetValue, deadCtorDecl, letDecl,
      allocatingSourceInnerStateAt, neutralLiveState] using evaluated
  refine ⟨nextRuntime, deadValue, ?_⟩
  change coreStep {
      allocatingSourceInnerStateAt arguments with
      control := .code (.let deadCtorDecl (.return live)) } =
    .next (allocatingSourceReturnState arguments nextRuntime deadValue)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluatedAt]
  rfl

theorem allocatingSourceReturnStep (arguments : Array Value)
    (nextRuntime : RuntimeState) (deadValue : Value) :
    coreStep
        (allocatingSourceReturnState arguments nextRuntime deadValue) =
      .next
        (allocatingSourceYieldedState arguments nextRuntime deadValue) := by
  simp [coreStep, allocatingSourceReturnState,
    allocatingSourceYieldedState, liveEnv, lookupValue, Impure.bind,
    Impure.lookup, live, dead]

theorem allocatingSourceYieldedStepEmpty
    (nextRuntime : RuntimeState) (deadValue : Value) :
    coreStep
        (allocatingSourceYieldedState #[] nextRuntime deadValue) =
      .next (allocatingSourceCachedState nextRuntime deadValue) := by
  rfl

theorem allocatingSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep
        (allocatingSourceYieldedState arguments nextRuntime deadValue) =
      .next
        (allocatingSourceInvokingState arguments nextRuntime deadValue) := by
  simp [coreStep, allocatingSourceYieldedState, neutralEntryFrames,
    notEmpty, allocatingSourceInvokingState]

/-- Complete finite-state characterization of source executions of the first
allocating fixture.  The dead constructor value remains in the environment,
but is absent from every exact live-variable root set used by the simulation.
-/
inductive AllocatingSourceReachable (arguments : Array Value) :
    MachineState → Prop where
  | entry :
      AllocatingSourceReachable arguments
        (initialState allocatingBeforeProgram `main arguments)
  | outer :
      AllocatingSourceReachable arguments
        (allocatingSourceOuterState arguments)
  | inner :
      AllocatingSourceReachable arguments
        (allocatingSourceInnerStateAt arguments)
  | ret (nextRuntime : RuntimeState) (deadValue : Value) :
      AllocatingSourceReachable arguments
        (allocatingSourceReturnState arguments nextRuntime deadValue)
  | yielded (nextRuntime : RuntimeState) (deadValue : Value) :
      AllocatingSourceReachable arguments
        (allocatingSourceYieldedState arguments nextRuntime deadValue)
  | cached (nextRuntime : RuntimeState) (deadValue : Value)
      (empty : arguments = #[]) :
      AllocatingSourceReachable arguments
        (allocatingSourceCachedState nextRuntime deadValue)
  | invoking (nextRuntime : RuntimeState) (deadValue : Value)
      (notEmpty : arguments ≠ #[]) :
      AllocatingSourceReachable arguments
        (allocatingSourceInvokingState arguments nextRuntime deadValue)

theorem allocatingSourceReachable_step
    (reachable : AllocatingSourceReachable arguments before)
    (step : Step externals before after) :
    AllocatingSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (allocatingSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (allocatingSourceOuterStep arguments) .inner step
  | inner =>
      rcases allocatingSourceInnerStep arguments with
        ⟨nextRuntime, deadValue, transition⟩
      exact predicate_of_step_next transition
        (.ret nextRuntime deadValue) step
  | ret nextRuntime deadValue =>
      exact predicate_of_step_next
        (allocatingSourceReturnStep arguments nextRuntime deadValue)
        (.yielded nextRuntime deadValue) step
  | yielded nextRuntime deadValue =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next
          (allocatingSourceYieldedStepEmpty nextRuntime deadValue)
          (.cached nextRuntime deadValue rfl) step
      · exact predicate_of_step_next
          (allocatingSourceYieldedStepNonempty
            (nextRuntime := nextRuntime) (deadValue := deadValue) empty)
          (.invoking nextRuntime deadValue empty) step
  | cached nextRuntime deadValue empty =>
      cases step with
      | internal transition =>
          simp [allocatingSourceCachedState, coreStep] at transition
      | external transition response =>
          simp [allocatingSourceCachedState, coreStep] at transition
  | invoking nextRuntime deadValue notEmpty =>
      cases step with
      | internal transition =>
          simp [allocatingSourceInvokingState, coreStep, invokeClosure,
            fail] at transition
      | external transition response =>
          simp [allocatingSourceInvokingState, coreStep, invokeClosure,
            fail] at transition

/-- The live outer binding is runtime-neutral even though its continuation
contains an allocation. -/
theorem allocatingBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3 state sourceFrameRoots
      allocatingBefore := by
  unfold allocatingBefore
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

/-- The deleted constructor's argument evaluation and arity are sufficient
for the source-only allocation certificate; retaining a constructor has no
additional ownership premise. -/
theorem allocatingDeadCtorSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 3
      (allocatingSourceInnerStateAt arguments) sourceFrameRoots
      (.let deadCtorDecl (.return live)) := by
  unfold deadCtorDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_constructor
  refine .mk #[.erased] ?_ rfl
  simp [allocatingSourceInnerStateAt, liveEnv, evalArgs, evalArg]
  rfl

theorem allocatingSourceReachable_ready
    (state : MachineState)
    (reachable : AllocatingSourceReachable arguments state) :
    SourceRuntimeOwnershipMachineReadyAt 3 state := by
  cases reachable with
  | entry =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = allocatingBefore :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact allocatingBeforeSourceRuntimeReadyAt
        (allocatingSourceOuterState arguments) sourceFrameRoots
        bounded exact subset static
  | inner =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq :
          sourceCode = .let deadCtorDecl (.return live) :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact allocatingDeadCtorSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | ret nextRuntime deadValue =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = .return live :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact neutralReturnSourceRuntimeReadyAt
        (allocatingSourceReturnState arguments nextRuntime deadValue)
        sourceFrameRoots bounded exact subset static
  | yielded nextRuntime deadValue =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [allocatingSourceYieldedState] at control
  | cached nextRuntime deadValue empty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [allocatingSourceCachedState] at control
  | invoking nextRuntime deadValue notEmpty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [allocatingSourceInvokingState] at control

/-- Every state reachable from the allocating source fixture satisfies the
dynamic source contract used by the strong non-lockstep simulation. -/
theorem allocatingSourceRuntimeOwnershipMachineInvariant
    (externals : ExternalSpec) (arguments : Array Value) :
    SourceRuntimeOwnershipMachineInvariant externals 3
      (initialState allocatingBeforeProgram `main arguments) :=
  SourceRuntimeOwnershipMachineInvariant.of_inductive
    (AllocatingSourceReachable arguments)
    .entry allocatingSourceReachable_step allocatingSourceReachable_ready

theorem allocatingSourceRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    SourceRuntimeOwnershipInitialInvariantOn externals 3
      allocatingBeforeProgram #[`main] := by
  intro entry member arguments
  have entryEq : entry = `main := by
    simpa using member
  subst entry
  exact
    allocatingSourceRuntimeOwnershipMachineInvariant externals arguments

theorem allocatingBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed allocatingBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique, allocatingBeforeProgram,
          fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [allocatingBeforeProgram] at member
      subst declaration
      exact .letE (.letE .ret)
    · intro declaration member
      simp [allocatingBeforeProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩
        (.letE ⟨.object, trivial⟩ .ret)
  · intro declaration member
    simp [allocatingBeforeProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl, allocatingBefore,
      liveDecl, deadCtorDecl, letDecl, codeBinderIds,
      BinderNamesUnique, ImpureHygiene.paramIds, live, dead]

theorem allocatingShadowProgramRun :
    shadowProgram? 3 allocatingBeforeProgram =
      some allocatingAfterProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    allocatingBeforeProgram, allocatingAfterProgram, fixtureDecl, decl,
    allocatingShadowRun]

/-- Checked whole-program lowering correctness for the allocating
dead-constructor fixture.  The source may allocate an unreachable cell that
the target omits; `ObservationRel` identifies the resulting executions. -/
theorem allocatingProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 3) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      allocatingBeforeProgram allocatingAfterProgram #[`main] :=
  shadowProgram_loweringCorrect_sourceMachineInvariant
    allocatingBeforeProgramElimDeadWellFormed allocatingShadowProgramRun
    compatible
    (allocatingSourceRuntimeOwnershipInitialInvariant externals)

theorem closedWritesBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed closedWritesBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique, closedWritesBeforeProgram,
          fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [closedWritesBeforeProgram] at member
      subst declaration
      exact .letE (.letE (.letE (.letE (.oset (.uset (.sset .ret))))))
    · intro declaration member
      simp [closedWritesBeforeProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩
        (.letE ⟨.object, trivial⟩
          (.letE ⟨.usize, trivial⟩
            (.letE ⟨.uint8, trivial⟩
              (.oset (.uset (.sset .ret))))))
  · intro declaration member
    simp [closedWritesBeforeProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl,
      closedWritesBefore, deletedWritesBefore, liveDecl,
      closedWritesObjectDecl, closedWritesUSizeDecl,
      closedWritesScalarDecl, letDecl, codeBinderIds,
      BinderNamesUnique, ImpureHygiene.paramIds,
      live, dead, usizeField, scalarField]

theorem closedWritesShadowProgramRun :
    shadowProgram? 8 closedWritesBeforeProgram =
      some closedWritesAfterProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    closedWritesBeforeProgram, closedWritesAfterProgram,
    fixtureDecl, decl, closedWritesShadowRun]

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

/-- Concrete states for the closed mutation fixture.  Entry arguments remain
only in the declaration-entry frame; the declaration itself has no
parameters, so all mutation operands and runtimes below are closed. -/
def closedWritesDeadEnv : Env :=
  bind liveEnv dead (.object (.heap 0))

def closedWritesUSizeEnv : Env :=
  bind closedWritesDeadEnv usizeField (.usize 7)

def closedWritesAfterUSizeRuntime : RuntimeState :=
  match setUSizeSlot deletedWriteSourceRuntime (.object (.heap 0))
      1 (.usize 7) with
  | .ok runtime => runtime
  | .error _ => {}

def closedWritesAfterScalarRuntime : RuntimeState :=
  match setScalarField closedWritesAfterUSizeRuntime (.object (.heap 0))
      8 0 (.scalar (.uint8 9)) with
  | .ok runtime => runtime
  | .error _ => {}

def closedWritesSourceOuterState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .code closedWritesBefore
    frames := neutralEntryFrames arguments }

def closedWritesSourceObjectState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .code <|
      .let closedWritesObjectDecl <|
      .let closedWritesUSizeDecl <|
      .let closedWritesScalarDecl deletedWritesBefore
    env := liveEnv
    frames := neutralEntryFrames arguments }

def closedWritesSourceUSizeState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .code <|
      .let closedWritesUSizeDecl <|
      .let closedWritesScalarDecl deletedWritesBefore
    env := closedWritesDeadEnv
    runtime := deletedWriteSourceRuntime
    frames := neutralEntryFrames arguments }

def closedWritesSourceScalarState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .code <| .let closedWritesScalarDecl deletedWritesBefore
    env := closedWritesUSizeEnv
    runtime := deletedWriteSourceRuntime
    frames := neutralEntryFrames arguments }

def closedWritesSourceObjectSetState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .code deletedWritesBefore
    env := deletedWriteSourceEnv
    runtime := deletedWriteSourceRuntime
    frames := neutralEntryFrames arguments }

def closedWritesSourceUSizeSetState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .code <|
      .uset dead 1 usizeField <|
      .sset dead 8 0 scalarField u8Type <| .return live
    env := deletedWriteSourceEnv
    runtime := deletedWriteSourceRuntime
    frames := neutralEntryFrames arguments }

def closedWritesSourceScalarSetState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .code <|
      .sset dead 8 0 scalarField u8Type <| .return live
    env := deletedWriteSourceEnv
    runtime := closedWritesAfterUSizeRuntime
    frames := neutralEntryFrames arguments }

def closedWritesSourceReturnState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .code (.return live)
    env := deletedWriteSourceEnv
    runtime := closedWritesAfterScalarRuntime
    frames := neutralEntryFrames arguments }

def closedWritesSourceYieldedState (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .yielded .erased
    env := deletedWriteSourceEnv
    runtime := closedWritesAfterScalarRuntime
    frames := neutralEntryFrames arguments }

def closedWritesSourceCachedState : MachineState :=
  { program := closedWritesBeforeProgram
    control := .yielded .erased
    env := deletedWriteSourceEnv
    runtime := closedWritesAfterScalarRuntime.setGlobal `main .erased }

def closedWritesSourceInvokingState
    (arguments : Array Value) : MachineState :=
  { program := closedWritesBeforeProgram
    control := .invokeValue .erased arguments
    env := deletedWriteSourceEnv
    runtime := closedWritesAfterScalarRuntime }

theorem closedWritesSourceEntryStep (arguments : Array Value) :
    coreStep (initialState closedWritesBeforeProgram `main arguments) =
      .next (closedWritesSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, closedWritesBeforeProgram,
      Program.findDecl?, invokeDecl, closedWritesSourceOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem closedWritesSourceOuterStep (arguments : Array Value) :
    coreStep (closedWritesSourceOuterState arguments) =
      .next (closedWritesSourceObjectState arguments) := by
  rfl

theorem closedWritesSourceObjectStep (arguments : Array Value) :
    coreStep (closedWritesSourceObjectState arguments) =
      .next (closedWritesSourceUSizeState arguments) := by
  simp [closedWritesSourceObjectState, closedWritesSourceUSizeState,
    coreStep, evalLetValue, closedWritesObjectDecl, letDecl,
    evalArgs, evalArg, closedWritesDeadEnv, deletedWriteSourceRuntime,
    deletedWriteObject, closedWritesInfo, allocCtor, alloc,
    Functor.map, Except.map, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

theorem closedWritesSourceUSizeStep (arguments : Array Value) :
    coreStep (closedWritesSourceUSizeState arguments) =
      .next (closedWritesSourceScalarState arguments) := by
  rfl

theorem closedWritesSourceScalarStep (arguments : Array Value) :
    coreStep (closedWritesSourceScalarState arguments) =
      .next (closedWritesSourceObjectSetState arguments) := by
  rfl

theorem closedWritesSourceObjectSetStep (arguments : Array Value) :
    coreStep (closedWritesSourceObjectSetState arguments) =
      .next (closedWritesSourceUSizeSetState arguments) := by
  rfl

theorem closedWritesSourceUSizeSetStep (arguments : Array Value) :
    coreStep (closedWritesSourceUSizeSetState arguments) =
      .next (closedWritesSourceScalarSetState arguments) := by
  rfl

theorem closedWritesSourceScalarSetStep (arguments : Array Value) :
    coreStep (closedWritesSourceScalarSetState arguments) =
      .next (closedWritesSourceReturnState arguments) := by
  rfl

theorem closedWritesSourceReturnStep (arguments : Array Value) :
    coreStep (closedWritesSourceReturnState arguments) =
      .next (closedWritesSourceYieldedState arguments) := by
  rfl

theorem closedWritesSourceYieldedStepEmpty :
    coreStep (closedWritesSourceYieldedState #[]) =
      .next closedWritesSourceCachedState := by
  rfl

theorem closedWritesSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (closedWritesSourceYieldedState arguments) =
      .next (closedWritesSourceInvokingState arguments) := by
  simp [coreStep, closedWritesSourceYieldedState, neutralEntryFrames,
    notEmpty, closedWritesSourceInvokingState]

/-- Complete source execution graph for the closed mutation fixture. -/
inductive ClosedWritesSourceReachable (arguments : Array Value) :
    MachineState → Prop where
  | entry :
      ClosedWritesSourceReachable arguments
        (initialState closedWritesBeforeProgram `main arguments)
  | outer :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceOuterState arguments)
  | object :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceObjectState arguments)
  | usize :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceUSizeState arguments)
  | scalar :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceScalarState arguments)
  | objectSet :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceObjectSetState arguments)
  | usizeSet :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceUSizeSetState arguments)
  | scalarSet :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceScalarSetState arguments)
  | ret :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceReturnState arguments)
  | yielded :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      ClosedWritesSourceReachable arguments closedWritesSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      ClosedWritesSourceReachable arguments
        (closedWritesSourceInvokingState arguments)

theorem closedWritesSourceReachable_step
    (reachable : ClosedWritesSourceReachable arguments before)
    (step : Step externals before after) :
    ClosedWritesSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (closedWritesSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (closedWritesSourceOuterStep arguments) .object step
  | object =>
      exact predicate_of_step_next
        (closedWritesSourceObjectStep arguments) .usize step
  | usize =>
      exact predicate_of_step_next
        (closedWritesSourceUSizeStep arguments) .scalar step
  | scalar =>
      exact predicate_of_step_next
        (closedWritesSourceScalarStep arguments) .objectSet step
  | objectSet =>
      exact predicate_of_step_next
        (closedWritesSourceObjectSetStep arguments) .usizeSet step
  | usizeSet =>
      exact predicate_of_step_next
        (closedWritesSourceUSizeSetStep arguments) .scalarSet step
  | scalarSet =>
      exact predicate_of_step_next
        (closedWritesSourceScalarSetStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (closedWritesSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next closedWritesSourceYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (closedWritesSourceYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [closedWritesSourceCachedState, coreStep] at transition
      | external transition response =>
          simp [closedWritesSourceCachedState, coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [closedWritesSourceInvokingState, coreStep,
            invokeClosure, fail] at transition
      | external transition response =>
          simp [closedWritesSourceInvokingState, coreStep,
            invokeClosure, fail] at transition

def closedWritesTargetOuterState (arguments : Array Value) : MachineState :=
  { program := closedWritesAfterProgram
    control := .code closedWritesAfter
    frames := neutralEntryFrames arguments }

def closedWritesTargetReturnState (arguments : Array Value) : MachineState :=
  { program := closedWritesAfterProgram
    control := .code (.return live)
    env := liveEnv
    frames := neutralEntryFrames arguments }

def closedWritesTargetYieldedState (arguments : Array Value) : MachineState :=
  { program := closedWritesAfterProgram
    control := .yielded .erased
    env := liveEnv
    frames := neutralEntryFrames arguments }

def closedWritesTargetCachedState : MachineState :=
  { program := closedWritesAfterProgram
    control := .yielded .erased
    env := liveEnv
    runtime := ({} : RuntimeState).setGlobal `main .erased }

def closedWritesTargetInvokingState
    (arguments : Array Value) : MachineState :=
  { program := closedWritesAfterProgram
    control := .invokeValue .erased arguments
    env := liveEnv }

theorem closedWritesTargetEntryStep (arguments : Array Value) :
    coreStep (initialState closedWritesAfterProgram `main arguments) =
      .next (closedWritesTargetOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, closedWritesAfterProgram,
      Program.findDecl?, invokeDecl, closedWritesTargetOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem closedWritesTargetOuterStep (arguments : Array Value) :
    coreStep (closedWritesTargetOuterState arguments) =
      .next (closedWritesTargetReturnState arguments) := by
  rfl

theorem closedWritesTargetReturnStep (arguments : Array Value) :
    coreStep (closedWritesTargetReturnState arguments) =
      .next (closedWritesTargetYieldedState arguments) := by
  rfl

theorem closedWritesTargetYieldedStepEmpty :
    coreStep (closedWritesTargetYieldedState #[]) =
      .next closedWritesTargetCachedState := by
  rfl

theorem closedWritesTargetYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (closedWritesTargetYieldedState arguments) =
      .next (closedWritesTargetInvokingState arguments) := by
  simp [coreStep, closedWritesTargetYieldedState, neutralEntryFrames,
    notEmpty, closedWritesTargetInvokingState]

inductive ClosedWritesTargetReachable (arguments : Array Value) :
    MachineState → Prop where
  | entry :
      ClosedWritesTargetReachable arguments
        (initialState closedWritesAfterProgram `main arguments)
  | outer :
      ClosedWritesTargetReachable arguments
        (closedWritesTargetOuterState arguments)
  | ret :
      ClosedWritesTargetReachable arguments
        (closedWritesTargetReturnState arguments)
  | yielded :
      ClosedWritesTargetReachable arguments
        (closedWritesTargetYieldedState arguments)
  | cached (empty : arguments = #[]) :
      ClosedWritesTargetReachable arguments closedWritesTargetCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      ClosedWritesTargetReachable arguments
        (closedWritesTargetInvokingState arguments)

theorem closedWritesTargetReachable_step
    (reachable : ClosedWritesTargetReachable arguments before)
    (step : Step externals before after) :
    ClosedWritesTargetReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (closedWritesTargetEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (closedWritesTargetOuterStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (closedWritesTargetReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next closedWritesTargetYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (closedWritesTargetYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [closedWritesTargetCachedState, coreStep] at transition
      | external transition response =>
          simp [closedWritesTargetCachedState, coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [closedWritesTargetInvokingState, coreStep,
            invokeClosure, fail] at transition
      | external transition response =>
          simp [closedWritesTargetInvokingState, coreStep,
            invokeClosure, fail] at transition

/-- The erased target has no allocation path and no active write head. -/
def ClosedWritesTargetRuntimeShape (state : MachineState) : Prop :=
  state.runtime.nextLocation = 0 ∧
    ∀ code, state.control = .code code →
      (∀ object index field continuation,
        code ≠ .oset object index field continuation) ∧
      (∀ object index field continuation,
        code ≠ .uset object index field continuation) ∧
      (∀ object width offset field type continuation,
        code ≠ .sset object width offset field type continuation)

theorem closedWritesTargetReachable_runtimeShape
    (reachable : ClosedWritesTargetReachable arguments state) :
    ClosedWritesTargetRuntimeShape state := by
  cases reachable <;>
    simp [ClosedWritesTargetRuntimeShape, initialState,
      closedWritesTargetOuterState, closedWritesTargetReturnState,
      closedWritesTargetYieldedState, closedWritesTargetCachedState,
      closedWritesTargetInvokingState, closedWritesAfter, neutralAfter,
      RuntimeState.setGlobal, RuntimeState.markPersistent]

/-- Pair-indexed ownership certificates for the three source-only writes.
The target's zero allocation frontier, together with the runtime relation,
excludes the source object from every actual control/frame root
decomposition. -/
theorem closedWritesObjectSetReady_of_shadowRuntime
    (target : MachineState) (runtime :
      ShadowRuntimeRel rho
        (closedWritesSourceObjectSetState arguments).runtime
        target.runtime sourceRoots targetRoots)
    (targetEmpty : target.runtime.nextLocation = 0) :
    DeletedObjectSetReadyAt
      (closedWritesSourceObjectSetState arguments)
      (runtimeRoots
        (closedWritesSourceObjectSetState arguments).runtime sourceRoots)
      dead 0 .erased := by
  refine ⟨0, ({ object := .ctor deletedWriteObject } : HeapCell),
    deletedWriteObject, .erased, ?_, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simp [closedWritesSourceObjectSetState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl
  · simp [deletedWriteObject]
  · exact runtime.leftUnreachable_of_rightNextLocation_zero targetEmpty 0

theorem closedWritesUSizeSetReady_of_shadowRuntime
    (target : MachineState) (runtime :
      ShadowRuntimeRel rho
        (closedWritesSourceUSizeSetState arguments).runtime
        target.runtime sourceRoots targetRoots)
    (targetEmpty : target.runtime.nextLocation = 0) :
    DeletedUSizeSetReadyAt
      (closedWritesSourceUSizeSetState arguments)
      (runtimeRoots
        (closedWritesSourceUSizeSetState arguments).runtime sourceRoots)
      dead 1 usizeField := by
  refine ⟨0, ({ object := .ctor deletedWriteObject } : HeapCell),
    deletedWriteObject, 7, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [closedWritesSourceUSizeSetState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · simp [closedWritesSourceUSizeSetState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl
  · simp [deletedWriteObject]
  · simp [deletedWriteObject]
  · exact runtime.leftUnreachable_of_rightNextLocation_zero targetEmpty 0

def deletedWriteObjectAfterUSize : ConstructorObject :=
  { deletedWriteObject with usizeFields := #[7] }

theorem closedWritesScalarSetReady_of_shadowRuntime
    (target : MachineState) (runtime :
      ShadowRuntimeRel rho
        (closedWritesSourceScalarSetState arguments).runtime
        target.runtime sourceRoots targetRoots)
    (targetEmpty : target.runtime.nextLocation = 0) :
    DeletedScalarSetReadyAt
      (closedWritesSourceScalarSetState arguments)
      (runtimeRoots
        (closedWritesSourceScalarSetState arguments).runtime sourceRoots)
      dead scalarField := by
  refine ⟨0, ({ object := .ctor deletedWriteObjectAfterUSize } : HeapCell),
    deletedWriteObjectAfterUSize, .uint8 9, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp [closedWritesSourceScalarSetState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · simp [closedWritesSourceScalarSetState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · change findCell? closedWritesAfterUSizeRuntime.heap 0 =
      some ({ object := .ctor deletedWriteObjectAfterUSize } : HeapCell)
    rfl
  · exact runtime.leftUnreachable_of_rightNextLocation_zero targetEmpty 0

/-- The exact structural pair determines the deleted object-write edge; the
target runtime shape supplies its dynamic unreachability certificate. -/
theorem closedWritesObjectSetPairReady
    (targetShape : ClosedWritesTargetRuntimeShape target)
    (related : SomeBinderReadyReachableMachineRelated 8
      (closedWritesSourceObjectSetState arguments) target) :
    BinderReadyReachableMachineReadyAt 8
      (closedWritesSourceObjectSetState arguments) target := by
  rcases related with
    ⟨rho, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  have sourceControl :
      (closedWritesSourceObjectSetState arguments).control =
        .code deletedWritesBefore := rfl
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rcases graph with
        ⟨remaining, final, bounded, exact, subset, static⟩
      have targetHead := targetShape.2 targetCode targetControl
      have decision :
          exact.view.runtimeDecision = .deletedObjectSet :=
        exact.view.runtimeDecision_eq_deletedObjectSet_of_target_not_oset
          targetHead.1
      have writeReady :=
        closedWritesObjectSetReady_of_shadowRuntime target runtime
          targetShape.1
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetControl] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            .objectSetDeleted decision writeReady⟩
          joins env)
  | yielded targetValue =>
      rw [targetControl] at control
      cases control
  | invokeName targetName targetArguments =>
      rw [targetControl] at control
      cases control
  | invokeValue targetFunction targetArguments =>
      rw [targetControl] at control
      cases control

theorem closedWritesUSizeSetPairReady
    (targetShape : ClosedWritesTargetRuntimeShape target)
    (related : SomeBinderReadyReachableMachineRelated 8
      (closedWritesSourceUSizeSetState arguments) target) :
    BinderReadyReachableMachineReadyAt 8
      (closedWritesSourceUSizeSetState arguments) target := by
  rcases related with
    ⟨rho, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  have sourceControl :
      (closedWritesSourceUSizeSetState arguments).control =
        .code
          (.uset dead 1 usizeField <|
            .sset dead 8 0 scalarField u8Type <| .return live) := rfl
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rcases graph with
        ⟨remaining, final, bounded, exact, subset, static⟩
      have targetHead := targetShape.2 targetCode targetControl
      have decision :
          exact.view.runtimeDecision = .deletedUSizeSet :=
        exact.view.runtimeDecision_eq_deletedUSizeSet_of_target_not_uset
          targetHead.2.1
      have writeReady :=
        closedWritesUSizeSetReady_of_shadowRuntime target runtime
          targetShape.1
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetControl] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            .usizeSetDeleted decision writeReady⟩
          joins env)
  | yielded targetValue =>
      rw [targetControl] at control
      cases control
  | invokeName targetName targetArguments =>
      rw [targetControl] at control
      cases control
  | invokeValue targetFunction targetArguments =>
      rw [targetControl] at control
      cases control

theorem closedWritesScalarSetPairReady
    (targetShape : ClosedWritesTargetRuntimeShape target)
    (related : SomeBinderReadyReachableMachineRelated 8
      (closedWritesSourceScalarSetState arguments) target) :
    BinderReadyReachableMachineReadyAt 8
      (closedWritesSourceScalarSetState arguments) target := by
  rcases related with
    ⟨rho, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  have sourceControl :
      (closedWritesSourceScalarSetState arguments).control =
        .code
          (.sset dead 8 0 scalarField u8Type <| .return live) := rfl
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rcases graph with
        ⟨remaining, final, bounded, exact, subset, static⟩
      have targetHead := targetShape.2 targetCode targetControl
      have decision :
          exact.view.runtimeDecision = .deletedScalarSet :=
        exact.view.runtimeDecision_eq_deletedScalarSet_of_target_not_sset
          targetHead.2.2
      have writeReady :=
        closedWritesScalarSetReady_of_shadowRuntime target runtime
          targetShape.1
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetControl] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            .scalarSetDeleted decision writeReady⟩
          joins env)
  | yielded targetValue =>
      rw [targetControl] at control
      cases control
  | invokeName targetName targetArguments =>
      rw [targetControl] at control
      cases control
  | invokeValue targetFunction targetArguments =>
      rw [targetControl] at control
      cases control

theorem closedWritesOuterSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 8
      (closedWritesSourceOuterState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = closedWritesBefore :=
    Control.code.inj control.symm
  subst sourceCode
  unfold closedWritesBefore
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

theorem closedWritesObjectSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 8
      (closedWritesSourceObjectState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq :
      sourceCode =
        (.let closedWritesObjectDecl <|
          .let closedWritesUSizeDecl <|
          .let closedWritesScalarDecl deletedWritesBefore) :=
    Control.code.inj control.symm
  subst sourceCode
  unfold closedWritesObjectDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_constructor
  refine .mk #[.erased] ?_ rfl
  simp [closedWritesSourceObjectState, evalArgs, evalArg]
  rfl

theorem closedWritesUSizeSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 8
      (closedWritesSourceUSizeState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq :
      sourceCode =
        (.let closedWritesUSizeDecl <|
          .let closedWritesScalarDecl deletedWritesBefore) :=
    Control.code.inj control.symm
  subst sourceCode
  unfold closedWritesUSizeDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_literal

theorem closedWritesScalarSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 8
      (closedWritesSourceScalarState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq :
      sourceCode = .let closedWritesScalarDecl deletedWritesBefore :=
    Control.code.inj control.symm
  subst sourceCode
  unfold closedWritesScalarDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_literal

theorem closedWritesReturnSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 8
      (closedWritesSourceReturnState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = .return live :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  simp [ExactShadowCodeRuntimeReadyAt]

/-- Every reachable source state is ready against any structurally related
reachable target state.  The three ownership-sensitive write cases use the
pair-indexed certificates above; all remaining states use ordinary
source-machine readiness. -/
theorem closedWritesSourceReachable_pairReady
    (sourceReachable : ClosedWritesSourceReachable arguments source)
    (targetShape : ClosedWritesTargetRuntimeShape target)
    (related :
      SomeBinderReadyReachableMachineRelated 8 source target) :
    BinderReadyReachableMachineReadyAt 8 source target := by
  cases sourceReachable with
  | entry =>
      apply related.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      exact
        related.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesOuterSourceMachineReadyAt arguments)
  | object =>
      exact
        related.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesObjectSourceMachineReadyAt arguments)
  | usize =>
      exact
        related.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesUSizeSourceMachineReadyAt arguments)
  | scalar =>
      exact
        related.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesScalarSourceMachineReadyAt arguments)
  | objectSet =>
      exact closedWritesObjectSetPairReady targetShape related
  | usizeSet =>
      exact closedWritesUSizeSetPairReady targetShape related
  | scalarSet =>
      exact closedWritesScalarSetPairReady targetShape related
  | ret =>
      exact
        related.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesReturnSourceMachineReadyAt arguments)
  | yielded =>
      apply related.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedWritesSourceYieldedState] at control
  | cached empty =>
      apply related.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedWritesSourceCachedState] at control
  | invoking notEmpty =>
      apply related.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedWritesSourceInvokingState] at control

theorem closedWritesSourceReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState closedWritesBeforeProgram `main arguments) state) :
    ClosedWritesSourceReachable arguments state := by
  rcases path with ⟨count, steps⟩
  have preserves : ∀ {count before after},
      Steps externals count before after →
        ClosedWritesSourceReachable arguments before →
          ClosedWritesSourceReachable arguments after := by
    intro count before after execution
    induction execution with
    | refl state =>
        exact fun ready => ready
    | step head tail ih =>
        intro ready
        exact ih (closedWritesSourceReachable_step ready head)
  exact preserves steps .entry

theorem closedWritesTargetReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState closedWritesAfterProgram `main arguments) state) :
    ClosedWritesTargetReachable arguments state := by
  rcases path with ⟨count, steps⟩
  have preserves : ∀ {count before after},
      Steps externals count before after →
        ClosedWritesTargetReachable arguments before →
          ClosedWritesTargetReachable arguments after := by
    intro count before after execution
    induction execution with
    | refl state =>
        exact fun ready => ready
    | step head tail ih =>
        intro ready
        exact ih (closedWritesTargetReachable_step ready head)
  exact preserves steps .entry

/-- Pair-indexed hereditary ownership for the complete closed fixture.
Related entry arguments may differ, but the empty initial address renaming
and the target's zero allocation frontier rule out aliases to the
source-only object at every write edge. -/
theorem closedWritesExactRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    ReachableInitialInvariantOn
      (BinderReadyExactRuntimeOwnershipInvariant externals 8)
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] := by
  intro entry member sourceArguments targetArguments argumentsRelated
  have entryEq : entry = `main := by
    simpa using member
  subst entry
  intro sourceAfter targetAfter sourcePath targetPath related
  have sourceReachable :=
    closedWritesSourceReachable_of_reaches sourcePath
  have targetReachable :=
    closedWritesTargetReachable_of_reaches targetPath
  exact closedWritesSourceReachable_pairReady sourceReachable
    (closedWritesTargetReachable_runtimeShape targetReachable) related

/-- Whole-program semantic correctness for allocation plus all three
source-only mutation forms. -/
theorem closedWritesProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 8) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] :=
  shadowProgram_loweringCorrect_exactRuntimeOwnership
    closedWritesBeforeProgramElimDeadWellFormed
    closedWritesShadowProgramRun compatible
    (closedWritesExactRuntimeOwnershipInitialInvariant externals)

end Fir.LeanIR.Passes.ElimDeadExamples
