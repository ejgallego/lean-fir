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

/-- Active state after evaluating the fixture's retained live binding. -/
def allocatingSourceInnerStateAt
    (arguments : Array Value) : MachineState :=
  { program := allocatingBeforeProgram
    control := .code (.let deadCtorDecl (.return live))
    env := liveEnv
    frames := neutralEntryFrames arguments }

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

theorem allocatingSourceOuterStep (arguments : Array Value) :
    coreStep (allocatingSourceOuterState arguments) =
      .next (allocatingSourceInnerStateAt arguments) := by
  rfl

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
