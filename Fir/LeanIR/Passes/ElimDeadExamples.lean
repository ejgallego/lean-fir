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
def resetChildVar : FVarId := ⟨`resetChild⟩
def papArgVar : FVarId := ⟨`papArg⟩
def boxInputVar : FVarId := ⟨`boxInput⟩
def papGarbageVar : FVarId := ⟨`papGarbage⟩
def boxGarbageVar : FVarId := ⟨`boxGarbage⟩

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

def closedReuseLiveDecl : LCNF.LetDecl .impure :=
  letDecl live objType (.lit (.nat 0))

def closedReuseTokenDecl : LCNF.LetDecl .impure :=
  letDecl reuseTokenVar objType (.reset 1 live)

def closedReuseArgDecl : LCNF.LetDecl .impure :=
  letDecl reuseArgVar objType .erased

/-- Closed failed-token reuse fixture.  Resetting the erased live value
produces `reuseToken none`; the deleted reuse then allocates only on the
source, while the target retains just the live return. -/
def closedReuseBefore : LCNF.Code .impure :=
  .let closedReuseLiveDecl <|
  .let closedReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedReuseAfter : LCNF.Code .impure :=
  .let closedReuseLiveDecl <| .return live

def closedConcreteReuseObjectDecl : LCNF.LetDecl .impure :=
  letDecl resetObjectVar objType (.ctor oneFieldInfo #[.erased])

def closedConcreteReuseTokenDecl : LCNF.LetDecl .impure :=
  letDecl reuseTokenVar objType (.reset 1 resetObjectVar)

/-- Closed concrete-token reuse fixture.  The constructor is reset to a
compiler-owned token and then reused, but the resulting object is dead. -/
def closedConcreteReuseBefore : LCNF.Code .impure :=
  .let closedReuseLiveDecl <|
  .let closedConcreteReuseObjectDecl <|
  .let closedConcreteReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedConcreteReuseAfter : LCNF.Code .impure :=
  closedReuseAfter

def closedOwnedReuseChildDecl : LCNF.LetDecl .impure :=
  letDecl resetChildVar objType (.ctor oneFieldInfo #[.erased])

def closedOwnedReuseObjectDecl : LCNF.LetDecl .impure :=
  letDecl resetObjectVar objType
    (.ctor oneFieldInfo #[.fvar resetChildVar])

def closedOwnedReuseTokenDecl : LCNF.LetDecl .impure :=
  letDecl reuseTokenVar objType (.reset 1 resetObjectVar)

/-- Closed owned-child reset/reuse fixture.  Reset releases the constructor
owned by its cleared field before the returned token is reused in place. -/
def closedOwnedReuseBefore : LCNF.Code .impure :=
  .let closedReuseLiveDecl <|
  .let closedOwnedReuseChildDecl <|
  .let closedOwnedReuseObjectDecl <|
  .let closedOwnedReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedOwnedReuseAfter : LCNF.Code .impure :=
  closedReuseAfter

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

def closedPapBoxPapArgDecl : LCNF.LetDecl .impure :=
  letDecl papArgVar objType .erased

def closedPapBoxPapDecl : LCNF.LetDecl .impure :=
  letDecl papGarbageVar objType
    (.pap `first #[.fvar papArgVar])

def closedPapBoxInputDecl : LCNF.LetDecl .impure :=
  letDecl boxInputVar u64Type
    (.lit (.uint64 18446744073709551615))

def closedPapBoxBoxDecl : LCNF.LetDecl .impure :=
  letDecl boxGarbageVar objType (.box u64Type boxInputVar)

/-- Closed allocation-family fixture.  The deleted partial application
allocates a closure and the deleted scalar box allocates another source-only
heap cell before the live tagged result is returned. -/
def closedPapBoxBefore : LCNF.Code .impure :=
  .let closedReuseLiveDecl <|
  .let closedPapBoxPapArgDecl <|
  .let closedPapBoxPapDecl <|
  .let closedPapBoxInputDecl <|
  .let closedPapBoxBoxDecl <|
  .return live

def closedPapBoxAfter : LCNF.Code .impure :=
  closedReuseAfter

def deadNullaryFapDecl : LCNF.LetDecl .impure :=
  letDecl dead objType (.fap `deadNullaryExternal #[])

def deadNullaryFapBefore : LCNF.Code .impure :=
  .let liveDecl <| .let deadNullaryFapDecl <| .return live

def deadNullaryFapAfter : LCNF.Code .impure :=
  .let liveDecl <| .return live

def retainedNullaryFapDecl : LCNF.LetDecl .impure :=
  letDecl live objType (.fap `deadNullaryExternal #[])

/-- Control fixture for the conservative policy: the same nullary full
application remains in the program because its result binder is live. -/
def retainedNullaryFap : LCNF.Code .impure :=
  .let retainedNullaryFapDecl <| .return live

#guard safeToElim deadErasedDecl.value
#guard safeToElim deadCtorDecl.value
#guard safeToElim deadNullaryFapDecl.value
#guard isNullaryFap deadNullaryFapDecl.value
#guard isNullaryFap retainedNullaryFapDecl.value
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

/-- Expected result of the fail-closed policy after the ordinary pinned pass
has been checked against the transparent traversal. -/
inductive NullaryPolicyExpectation where
  | accepted
  | rejected

structure ElimDeadPolicyFixture where
  name : Name
  before : LCNF.Code .impure
  expected : LCNF.Code .impure
  policy : NullaryPolicyExpectation

/-- Boundary matrix spanning retained unsafe values, ordinary deleted values,
allocations, writes, reset/reuse, and the unique nullary-application
rejection. Every row is also compared with Lean 4.32's actual pass. -/
def elimDeadPolicyFixtures : Array ElimDeadPolicyFixture := #[
  ⟨`policyNeutral, neutralBefore, neutralAfter, .accepted⟩,
  ⟨`policyUsed, usedBefore, usedBefore, .accepted⟩,
  ⟨`policyUnsafe, unsafeBefore, unsafeBefore, .accepted⟩,
  ⟨`policyAllocation, allocatingBefore, allocatingAfter, .accepted⟩,
  ⟨`policyWrites, deletedWritesBefore, deletedWritesAfter, .accepted⟩,
  ⟨`policyReuse, deletedReuseBefore, deletedReuseAfter, .accepted⟩,
  ⟨`policyReset, deletedResetBefore, deletedResetAfter, .accepted⟩,
  ⟨`policyPap, deletedPapBefore, deletedPapAfter, .accepted⟩,
  ⟨`policyBox, deletedBoxBefore, deletedBoxAfter, .accepted⟩,
  ⟨`policyDeletedNullaryFap,
    deadNullaryFapBefore, deadNullaryFapAfter, .rejected⟩,
  ⟨`policyRetainedNullaryFap,
    retainedNullaryFap, retainedNullaryFap, .accepted⟩
]

def checkActualPolicyFixture (fixture : ElimDeadPolicyFixture) :
    CoreM Unit := do
  checkActualElimDead fixture.name fixture.before fixture.expected
  match fixture.policy, nullarySafeShadowCode? 64 {} fixture.before with
  | .accepted, some (checked, _) =>
      unless checked == fixture.expected do
        throwError
          "nullary policy fixture {fixture.name} changed the pinned pass result"
  | .accepted, none =>
      throwError
        "nullary policy fixture {fixture.name} rejected an expected pass branch"
  | .rejected, none =>
      pure ()
  | .rejected, some _ =>
      throwError
        "nullary policy fixture {fixture.name} accepted a forbidden pass branch"

def checkActualPolicyMatrix : CoreM Unit := do
  for fixture in elimDeadPolicyFixtures do
    checkActualPolicyFixture fixture

def checkFixtures : CoreM Unit := do
  checkActualElimDead `elimDeadNeutral neutralBefore neutralAfter
  checkActualElimDead `elimDeadUsed usedBefore usedBefore
  checkActualElimDead `elimDeadUnsafe unsafeBefore unsafeBefore
  checkActualElimDead `elimDeadAllocating allocatingBefore allocatingAfter
  checkActualElimDead `elimDeadWrites deletedWritesBefore deletedWritesAfter
  checkActualElimDead `elimDeadClosedWrites closedWritesBefore closedWritesAfter
  checkActualElimDead `elimDeadClosedReuse closedReuseBefore closedReuseAfter
  checkActualElimDead `elimDeadClosedConcreteReuse
    closedConcreteReuseBefore closedConcreteReuseAfter
  checkActualElimDead `elimDeadClosedOwnedReuse
    closedOwnedReuseBefore closedOwnedReuseAfter
  checkActualElimDead `elimDeadReuse deletedReuseBefore deletedReuseAfter
  checkActualElimDead `elimDeadReset deletedResetBefore deletedResetAfter
  checkActualElimDead `elimDeadLargeNat
    deletedLargeNatBefore deletedLargeNatAfter
  checkActualElimDead `elimDeadPap deletedPapBefore deletedPapAfter
  checkActualElimDead `elimDeadBox deletedBoxBefore deletedBoxAfter
  checkActualElimDead `elimDeadClosedBox closedBoxBefore closedBoxAfter
  checkActualElimDead `elimDeadClosedPapBox
    closedPapBoxBefore closedPapBoxAfter
  checkActualElimDead `elimDeadNullaryFap
    deadNullaryFapBefore deadNullaryFapAfter
  checkActualElimDead `elimDeadRetainedNullaryFap
    retainedNullaryFap retainedNullaryFap
  checkActualPolicyMatrix
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

def closedReuseBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main closedReuseBefore] }

def closedReuseAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main closedReuseAfter] }

def closedConcreteReuseBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main closedConcreteReuseBefore] }

def closedConcreteReuseAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main closedConcreteReuseAfter] }

def closedOwnedReuseBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main closedOwnedReuseBefore] }

def closedOwnedReuseAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main closedOwnedReuseAfter] }

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

def closedPapBoxBeforeProgram : ImpureProgram :=
  { decls := #[firstDecl, fixtureDecl `main closedPapBoxBefore] }

def closedPapBoxAfterProgram : ImpureProgram :=
  { decls := #[firstDecl, fixtureDecl `main closedPapBoxAfter] }

def deadNullaryExternalDecl : LCNF.Decl .impure :=
  decl `deadNullaryExternal #[] objType (.extern { entries := [] })

def deadNullaryFapBeforeProgram : ImpureProgram :=
  { decls := #[deadNullaryExternalDecl,
      fixtureDecl `main deadNullaryFapBefore] }

def deadNullaryFapAfterProgram : ImpureProgram :=
  { decls := #[deadNullaryExternalDecl,
      fixtureDecl `main deadNullaryFapAfter] }

def retainedNullaryFapProgram : ImpureProgram :=
  { decls := #[deadNullaryExternalDecl,
      fixtureDecl `main retainedNullaryFap] }

def countedNullaryExternal : ExternalImpl where
  call _ runtime := .ok {
    value := .erased
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world + 1 }

def countedNullaryExternalSpec : ExternalSpec :=
  fun request runtime response =>
    countedNullaryExternal.call request runtime = .ok response

theorem countedNullaryExternalImplements :
    countedNullaryExternal.Implements countedNullaryExternalSpec :=
  fun _ _ _ response => response

/-- A deterministic foreign fixture that explicitly requires an owned input
heap, returns that heap unchanged, and advances only the observable world.
The premise makes its source ownership law total even on arbitrary runtime
inputs, rather than silently assuming every caller is well formed. -/
def ownershipEchoExternalSpec : ExternalSpec :=
  fun _ runtime response =>
    HeapOwnershipBelowFrontier runtime ∧
      response = {
        value := .erased
        heap := runtime.heap
        nextLocation := runtime.nextLocation
        world := runtime.world + 1 }

theorem ownershipEchoExternalSpec_sourceCompatible :
    SourceExternalSpecOwnershipCompatible ownershipEchoExternalSpec := by
  intro request waiting response external
  rcases external with ⟨owned, rfl⟩
  refine ⟨Nat.le_refl _, ?_⟩
  constructor
  · intro location cell found
    apply owned.cell_lt
    simpa [resumeExternal, MachineState.withValue] using found
  · intro parent cell child found member
    apply owned.owned_lt
    · simpa [resumeExternal, MachineState.withValue] using found
    · exact member

def ownershipNamedExternalRequest : ExternalRequest := {
  name := `deadNullaryExternal
  paramTypes := #[]
  resultType := objType
  args := #[]
}

def ownershipNamedExternalState : MachineState :=
  initialState retainedNullaryFapProgram `deadNullaryExternal #[]

def ownershipNamedExternalWaiting : MachineState := {
  ownershipNamedExternalState with
  frames := [.cache `deadNullaryExternal]
}

def ownershipNamedExternalResponse : ExternalResponse := {
  value := .erased
  heap := ownershipNamedExternalState.runtime.heap
  nextLocation := ownershipNamedExternalState.runtime.nextLocation
  world := ownershipNamedExternalState.runtime.world + 1
}

theorem ownershipNamedExternalTransition :
    coreStep ownershipNamedExternalState =
      .external ownershipNamedExternalRequest
        ownershipNamedExternalWaiting := by
  simp [ownershipNamedExternalState, initialState, coreStep,
    retainedNullaryFapProgram, deadNullaryExternalDecl, fixtureDecl, decl,
    Program.findDecl?, findGlobal?, invokeDecl, bindParams,
    ownershipNamedExternalRequest, ownershipNamedExternalWaiting]

theorem ownershipNamedExternalState_owned :
    SourceMachineOwnershipBelowFrontier ownershipNamedExternalState := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ownershipNamedExternalState, initialState] using
      HeapOwnershipBelowFrontier.empty
  · intro fvarId value found
    simp [ownershipNamedExternalState, initialState, lookup] at found
  · simp [ownershipNamedExternalState, initialState,
      BindFrameEnvironmentsBelowFrontier]

/-- Concrete named-control regression: suspension and the echoed response
both retain the complete source ownership carrier. -/
theorem ownershipNamedExternalFixture :
    SourceMachineOwnershipBelowFrontier ownershipNamedExternalWaiting ∧
    SourceMachineOwnershipBelowFrontier
      (resumeExternal ownershipNamedExternalRequest
        ownershipNamedExternalWaiting ownershipNamedExternalResponse) := by
  have argumentsBelow :
      HeapLocationsBelowFrontier
        ownershipNamedExternalState.runtime (#[] : Array Value).toList := by
    simp [HeapLocationsBelowFrontier]
  have waiting :=
    ownershipNamedExternalState_owned.invokeNameExternalWaiting
      (name := `deadNullaryExternal) (arguments := #[])
      argumentsBelow ownershipNamedExternalTransition
  have waitingRuntime :
      ownershipNamedExternalWaiting.runtime =
        ownershipNamedExternalState.runtime :=
    coreStep_invokeName_external_runtime_eq
      (step := ownershipNamedExternalTransition)
  have external :
      ownershipEchoExternalSpec ownershipNamedExternalRequest
        ownershipNamedExternalWaiting.runtime
        ownershipNamedExternalResponse := by
    rw [waitingRuntime]
    exact ⟨ownershipNamedExternalState_owned.heap, rfl⟩
  exact ⟨waiting,
    waiting.resumeExternal
      ownershipEchoExternalSpec_sourceCompatible external⟩

def ownershipExternalArgument : FVarId := ⟨`ownershipExternalArgument⟩

def ownershipUnaryExternalDecl : LCNF.Decl .impure :=
  decl `ownershipUnaryExternal #[param ownershipExternalArgument]
    objType (.extern { entries := [] })

def ownershipUnaryExternalProgram : ImpureProgram :=
  { decls := #[ownershipUnaryExternalDecl] }

def ownershipExternalClosureRuntime : RuntimeState :=
  (alloc ({} : RuntimeState)
    (.closure `ownershipUnaryExternal 1 #[.erased])).1

def ownershipValueExternalState : MachineState := {
  program := ownershipUnaryExternalProgram
  control := .invokeValue (.object (.heap 0)) #[]
  runtime := ownershipExternalClosureRuntime
}

def ownershipValueExternalRequest : ExternalRequest := {
  name := `ownershipUnaryExternal
  paramTypes := #[objType]
  resultType := objType
  args := #[.erased]
}

def ownershipValueExternalWaiting : MachineState := {
  ownershipValueExternalState with
  env := bind [] ownershipExternalArgument .erased
}

def ownershipValueExternalResponse : ExternalResponse := {
  value := .erased
  heap := ownershipValueExternalState.runtime.heap
  nextLocation := ownershipValueExternalState.runtime.nextLocation
  world := ownershipValueExternalState.runtime.world + 1
}

theorem ownershipValueExternalTransition :
    coreStep ownershipValueExternalState =
      .external ownershipValueExternalRequest
        ownershipValueExternalWaiting := by
  simp [ownershipValueExternalState, ownershipExternalClosureRuntime,
    coreStep, invokeClosure, getLiveCell, findCell?,
    ownershipUnaryExternalProgram, ownershipUnaryExternalDecl,
    Program.findDecl?, invokeDecl, bindParams, decl, param,
    ownershipExternalArgument, ownershipValueExternalRequest,
    ownershipValueExternalWaiting, Fir.LeanIR.Impure.alloc]

theorem ownershipValueExternalState_owned :
    SourceMachineOwnershipBelowFrontier ownershipValueExternalState := by
  let base : MachineState := {
    program := ownershipUnaryExternalProgram
    control := .yielded .erased
  }
  have baseOwned : SourceMachineOwnershipBelowFrontier base := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [base] using HeapOwnershipBelowFrontier.empty
    · intro fvarId value found
      simp [base, lookup] at found
    · simp [base, BindFrameEnvironmentsBelowFrontier]
  have fixedBelow :
      HeapLocationsBelowFrontier
        base.runtime (#[.erased] : Array Value).toList := by
    simp [HeapLocationsBelowFrontier]
  have allocated :=
    baseOwned.allocClosureRuntime
      (arguments := #[.erased]) fixedBelow
      `ownershipUnaryExternal 1
  have controlled :=
    allocated.withControlAndJoins
      (.invokeValue (.object (.heap 0)) #[]) []
  simpa [base, ownershipValueExternalState,
    ownershipExternalClosureRuntime] using controlled

/-- Concrete closure-control regression: the fixed erased argument is owned
by the closure cell, and both suspension and response preserve ownership. -/
theorem ownershipValueExternalFixture :
    SourceMachineOwnershipBelowFrontier ownershipValueExternalWaiting ∧
    SourceMachineOwnershipBelowFrontier
      (resumeExternal ownershipValueExternalRequest
        ownershipValueExternalWaiting ownershipValueExternalResponse) := by
  have argumentsBelow :
      HeapLocationsBelowFrontier
        ownershipValueExternalState.runtime (#[] : Array Value).toList := by
    simp [HeapLocationsBelowFrontier]
  have waiting :=
    ownershipValueExternalState_owned.invokeValueExternalWaiting
      (function := .object (.heap 0)) (arguments := #[])
      argumentsBelow ownershipValueExternalTransition
  have waitingRuntime :
      ownershipValueExternalWaiting.runtime =
        ownershipValueExternalState.runtime :=
    coreStep_invokeValue_external_runtime_eq
      (step := ownershipValueExternalTransition)
  have external :
      ownershipEchoExternalSpec ownershipValueExternalRequest
        ownershipValueExternalWaiting.runtime
        ownershipValueExternalResponse := by
    rw [waitingRuntime]
    exact ⟨ownershipValueExternalState_owned.heap, rfl⟩
  exact ⟨waiting,
    waiting.resumeExternal
      ownershipEchoExternalSpec_sourceCompatible external⟩

def deadNullaryFapSourceObservation : Observation :=
  match runMain deadNullaryFapBeforeProgram countedNullaryExternal with
  | .done observation => observation
  | .outOfFuel _ => default

def deadNullaryFapSourceRunIsDone : Bool :=
  match runMain deadNullaryFapBeforeProgram countedNullaryExternal with
  | .done _ => true
  | .outOfFuel _ => false

theorem deadNullaryFapSourceRunIsDone_true :
    deadNullaryFapSourceRunIsDone = true := by
  native_decide

theorem deadNullaryFapSourceRun :
    runMain deadNullaryFapBeforeProgram countedNullaryExternal =
      .done deadNullaryFapSourceObservation := by
  unfold deadNullaryFapSourceObservation
  cases execution :
      runMain deadNullaryFapBeforeProgram countedNullaryExternal with
  | done observation =>
      simp
  | outOfFuel _ =>
      have impossible := deadNullaryFapSourceRunIsDone_true
      simp [deadNullaryFapSourceRunIsDone, execution] at impossible

theorem countedNullaryExternal_executeStep_done
    (execution :
      executeStep countedNullaryExternal state = .done observation) :
    coreStep state = .done observation := by
  unfold executeStep at execution
  split at execution
  next transition => contradiction
  next transition =>
    cases execution
    exact transition
  next request waiting transition =>
    simp [countedNullaryExternal] at execution

theorem deadNullaryFapSourceEvaluates :
    Evaluates countedNullaryExternalSpec
      deadNullaryFapBeforeProgram `main #[]
      deadNullaryFapSourceObservation := by
  have executed :=
    run_done_sound countedNullaryExternal
      deadNullaryFapSourceObservation 100
      (initialState deadNullaryFapBeforeProgram `main #[])
      (by
        simpa [runMain, runProgram] using
          deadNullaryFapSourceRun)
  rcases executed with ⟨count, final, steps, done⟩
  exact ⟨count, final,
    execSteps_sound countedNullaryExternalImplements steps,
    countedNullaryExternal_executeStep_done done⟩

def deadNullaryFapLiveEnv : Env :=
  bind [] live .erased

def deadNullaryFapTargetOuterState : MachineState := {
  program := deadNullaryFapAfterProgram
  control := .code deadNullaryFapAfter
  frames := [.cache `main]
}

def deadNullaryFapTargetReturnState : MachineState := {
  program := deadNullaryFapAfterProgram
  control := .code (.return live)
  env := deadNullaryFapLiveEnv
  frames := [.cache `main]
}

def deadNullaryFapTargetYieldedState : MachineState := {
  program := deadNullaryFapAfterProgram
  control := .yielded .erased
  env := deadNullaryFapLiveEnv
  frames := [.cache `main]
}

def deadNullaryFapTargetCachedState : MachineState := {
  program := deadNullaryFapAfterProgram
  control := .yielded .erased
  env := deadNullaryFapLiveEnv
  runtime := ({} : RuntimeState).setGlobal `main .erased
}

def deadNullaryFapTargetObservation : Observation :=
  observe deadNullaryFapTargetCachedState (.returned .erased)

theorem deadNullaryFapTargetEntryStep :
    coreStep
      (initialState deadNullaryFapAfterProgram `main #[]) =
      .next deadNullaryFapTargetOuterState := by
  simp [initialState, coreStep, deadNullaryFapAfterProgram,
    deadNullaryExternalDecl, fixtureDecl, decl,
    Program.findDecl?, invokeDecl, bindParams, findGlobal?,
    deadNullaryFapTargetOuterState]

theorem deadNullaryFapTargetOuterStep :
    coreStep deadNullaryFapTargetOuterState =
      .next deadNullaryFapTargetReturnState := by
  unfold deadNullaryFapTargetOuterState
    deadNullaryFapTargetReturnState deadNullaryFapAfter
    liveDecl letDecl deadNullaryFapLiveEnv
  rfl

theorem deadNullaryFapTargetReturnStep :
    coreStep deadNullaryFapTargetReturnState =
      .next deadNullaryFapTargetYieldedState := by
  simp [coreStep, deadNullaryFapTargetReturnState,
    deadNullaryFapTargetYieldedState, deadNullaryFapLiveEnv,
    lookupValue, Impure.bind, Impure.lookup, live]

theorem deadNullaryFapTargetYieldedStep :
    coreStep deadNullaryFapTargetYieldedState =
      .next deadNullaryFapTargetCachedState := by
  rfl

theorem deadNullaryFapTargetCachedDone :
    coreStep deadNullaryFapTargetCachedState =
      .done deadNullaryFapTargetObservation := by
  rfl

theorem deadNullaryFapTargetEvaluates_iff :
    Evaluates countedNullaryExternalSpec
      deadNullaryFapAfterProgram `main #[] observation ↔
      deadNullaryFapTargetObservation = observation := by
  change EvaluatesState countedNullaryExternalSpec
    (initialState deadNullaryFapAfterProgram `main #[])
    observation ↔ _
  rw [evaluatesState_internal_iff deadNullaryFapTargetEntryStep]
  rw [evaluatesState_internal_iff deadNullaryFapTargetOuterStep]
  rw [evaluatesState_internal_iff deadNullaryFapTargetReturnStep]
  rw [evaluatesState_internal_iff deadNullaryFapTargetYieldedStep]
  exact ElimDead.evaluatesState_done_iff
    deadNullaryFapTargetCachedDone

theorem deadNullaryFapSourceObservation_world :
    deadNullaryFapSourceObservation.world = 1 := by
  native_decide

theorem deadNullaryFapTargetObservation_world :
    deadNullaryFapTargetObservation.world = 0 := by
  rfl

theorem deadNullaryFapObservationsNotRelated :
    ¬ObservationRel deadNullaryFapSourceObservation
      deadNullaryFapTargetObservation := by
  rintro ⟨_, _, world, _, _⟩
  rw [deadNullaryFapSourceObservation_world,
    deadNullaryFapTargetObservation_world] at world
  contradiction

/-- The actual pass result is not a correct lowering under FIR's unrestricted
external semantics: the deleted source call advances the observable world,
while every target execution leaves it at zero. -/
theorem deadNullaryFapNotLoweringCorrect :
    ¬LoweringCorrect
      (Impure.semantics countedNullaryExternalSpec)
      (Impure.semantics countedNullaryExternalSpec)
      (reachablePhaseSimulation countedNullaryExternalSpec)
      deadNullaryFapBeforeProgram
      deadNullaryFapAfterProgram #[`main] := by
  intro correct
  obtain ⟨targetObservation, targetEvaluation, related⟩ :=
    correct `main (by simp) #[] #[] .nil
      deadNullaryFapSourceObservation
      deadNullaryFapSourceEvaluates
  have observationEq :=
    deadNullaryFapTargetEvaluates_iff.mp targetEvaluation
  subst targetObservation
  exact deadNullaryFapObservationsNotRelated related

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

theorem deadNullaryFapShadowRun :
    shadowCode? 3 {} deadNullaryFapBefore =
      some (deadNullaryFapAfter, neutralUsed) := by
  change shadowCode? 3 {} deadNullaryFapBefore =
    some (deadNullaryFapAfter, ({} : UsedLocals).insert live)
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deadNullaryFapBefore, deadNullaryFapAfter,
    liveDecl, deadNullaryFapDecl, letDecl,
    shadowCode?, safeToElim, collectLetValue,
    collectArgs, collectArgList,
    liveMember, deadAbsent]

/-- The executable policy rejects the same successful transparent branch
whose semantic counterexample is recorded above. -/
theorem deadNullaryFapCheckedRejected :
    nullarySafeShadowCode? 3 {} deadNullaryFapBefore = none := by
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deadNullaryFapBefore, liveDecl, deadNullaryFapDecl,
    letDecl, nullarySafeShadowCode?, safeToElim,
    isNullaryFap, collectLetValue, collectArgs, collectArgList,
    deadAbsent]

/-- A nullary full application is accepted when its result is live. The
checked traversal and the ordinary pass both retain the node exactly. -/
theorem retainedNullaryFapCheckedRun :
    nullarySafeShadowCode? 2 {} retainedNullaryFap =
      some (retainedNullaryFap, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  simp [retainedNullaryFap, retainedNullaryFapDecl, letDecl,
    neutralUsed, nullarySafeShadowCode?, safeToElim,
    collectLetValue, collectArgs, collectArgList, liveMember]

/-- A dead but operationally unsafe copy is retained by both the checked
traversal and the pinned pass. -/
theorem unsafeCheckedRun :
    nullarySafeShadowCode? 3 {} unsafeBefore =
      some (unsafeBefore,
        (({} : UsedLocals).insert live).insert live) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  simp [unsafeBefore, liveDecl, deadCopyDecl, letDecl,
    nullarySafeShadowCode?, safeToElim,
    collectLetValue, collectArgs, collectArgList, liveMember]

/-- Ordinary source-only allocation deletion remains accepted by the
conservative policy. -/
theorem allocatingCheckedRun :
    nullarySafeShadowCode? 3 {} allocatingBefore =
      some (allocatingAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [allocatingBefore, allocatingAfter, neutralAfter, liveDecl,
    deadCtorDecl, letDecl, neutralUsed, nullarySafeShadowCode?,
    safeToElim, isNullaryFap, collectLetValue,
    collectArgs, collectArgList, collectArg,
    liveMember, deadAbsent]

/-- Deleted unreachable writes are unaffected by the nullary-call policy. -/
theorem deletedWritesCheckedRun :
    nullarySafeShadowCode? 4 {} deletedWritesBefore =
      some (deletedWritesAfter, neutralUsed) := by
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [deletedWritesBefore, deletedWritesAfter, neutralUsed,
    nullarySafeShadowCode?, deadAbsent]

theorem deadNullaryFapBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed deadNullaryFapBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · exact deadNullaryFapBeforeWellFormed
    · native_decide
    · intro declaration member
      simp [deadNullaryFapBeforeProgram] at member
      rcases member with rfl | rfl
      · trivial
      · exact .letE (.letE .ret)
    · intro declaration member
      simp [deadNullaryFapBeforeProgram] at member
      rcases member with rfl | rfl
      · trivial
      · exact .letE ⟨.object, trivial⟩
          (.letE ⟨.object, trivial⟩ .ret)
  · intro declaration member
    simp [deadNullaryFapBeforeProgram] at member
    rcases member with rfl | rfl
    · simp [DeclCodeBinderNamesUnique,
        deadNullaryExternalDecl, decl,
        BinderNamesUnique, ImpureHygiene.paramIds]
    · simp [DeclCodeBinderNamesUnique, fixtureDecl, decl,
        deadNullaryFapBefore, liveDecl, deadNullaryFapDecl,
        letDecl, codeBinderIds, BinderNamesUnique,
        ImpureHygiene.paramIds, live, dead]

theorem deadNullaryFapShadowProgramRun :
    shadowProgram? 3 deadNullaryFapBeforeProgram =
      some deadNullaryFapAfterProgram := by
  have externalRun :
      shadowDecl? 3 deadNullaryExternalDecl =
        some deadNullaryExternalDecl := by
    simp [shadowDecl?, deadNullaryExternalDecl, decl]
  have mainRun :
      shadowDecl? 3 (fixtureDecl `main deadNullaryFapBefore) =
        some (fixtureDecl `main deadNullaryFapAfter) := by
    simp [shadowDecl?, fixtureDecl, decl,
      deadNullaryFapShadowRun]
  simp [shadowProgram?, shadowDecls?,
    deadNullaryFapBeforeProgram, deadNullaryFapAfterProgram,
    externalRun, mainRun]

/-- The program-level checker rejects the pinned pass result rather than
manufacturing a semantic certificate for the effectful deletion. -/
theorem deadNullaryFapCheckedProgramRejected :
    nullarySafeShadowProgram? 3 deadNullaryFapBeforeProgram = none := by
  simp [nullarySafeShadowProgram?, nullarySafeShadowDecls?,
    nullarySafeShadowDecl?, deadNullaryFapBeforeProgram,
    deadNullaryExternalDecl, fixtureDecl, decl,
    deadNullaryFapCheckedRejected]

/-- Program-level retained-nullary control. This accepted certificate still
allows the ordinary actual pass result because no nullary call is deleted. -/
theorem retainedNullaryFapCheckedProgramRun :
    nullarySafeShadowProgram? 2 retainedNullaryFapProgram =
      some retainedNullaryFapProgram := by
  simp [nullarySafeShadowProgram?, nullarySafeShadowDecls?,
    nullarySafeShadowDecl?, retainedNullaryFapProgram,
    deadNullaryExternalDecl, fixtureDecl, decl,
    retainedNullaryFapCheckedRun]

theorem retainedNullaryFapPolicyProgramRun :
    NoDeletedNullaryFapProgramRun 2
      retainedNullaryFapProgram retainedNullaryFapProgram :=
  (nullarySafeShadowProgram_certifies
    retainedNullaryFapCheckedProgramRun).2

/-- Static compiler well-formedness and a successful pinned transparent run
do not suffice for semantic correctness of the nullary-application rule. -/
theorem deadNullaryFapStaticPremisesButNotCorrect :
    ProgramElimDeadWellFormed deadNullaryFapBeforeProgram ∧
    shadowProgram? 3 deadNullaryFapBeforeProgram =
      some deadNullaryFapAfterProgram ∧
    ¬LoweringCorrect
      (Impure.semantics countedNullaryExternalSpec)
      (Impure.semantics countedNullaryExternalSpec)
      (reachablePhaseSimulation countedNullaryExternalSpec)
      deadNullaryFapBeforeProgram
      deadNullaryFapAfterProgram #[`main] :=
  ⟨deadNullaryFapBeforeProgramElimDeadWellFormed,
    deadNullaryFapShadowProgramRun,
    deadNullaryFapNotLoweringCorrect⟩

/-- The conservative policy rejects exactly the audited deletion responsible
for the observable nullary-application counterexample. -/
theorem deadNullaryFapNotNullarySafeCode :
    ¬NullarySafeExactShadowCodeRelated 3
      deadNullaryFapBefore deadNullaryFapAfter := by
  rintro ⟨final, graph⟩
  change NullarySafeShadowCodeRun 3 {} final
    (.let liveDecl (.let deadNullaryFapDecl (.return live)))
    (.let liveDecl (.return live)) at graph
  cases graph with
  | letRetained continuation _keep =>
      cases continuation with
      | letDeleted _return _absent _safe notNullary =>
          apply notNullary
          exact ⟨`deadNullaryExternal, #[], rfl, rfl⟩
  | letDeleted continuation _absent _safe _notNullary =>
      have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
        native_decide
      have innerRun :
          shadowCode? 2 {}
              (.let deadNullaryFapDecl (.return live)) =
            some (.return live, neutralUsed) := by
        simp [shadowCode?, deadNullaryFapDecl, letDecl,
          neutralUsed, safeToElim, collectLetValue,
          collectArgs, collectArgList,
          deadAbsent]
      have continuationResult := continuation.result
      rw [innerRun] at continuationResult
      cases continuationResult

/-- The same rejection lifts through the external declaration and the
program-level exact pass relation. -/
theorem deadNullaryFapNotNullarySafeProgram :
    ¬NoDeletedNullaryFapProgramRun 3
      deadNullaryFapBeforeProgram deadNullaryFapAfterProgram := by
  intro policy
  have declarations :
      ListRel
        (DeclRelated (NullarySafeExactShadowCodeRelated 3))
        [deadNullaryExternalDecl,
          fixtureDecl `main deadNullaryFapBefore]
        [deadNullaryExternalDecl,
          fixtureDecl `main deadNullaryFapAfter] := by
    simpa [NoDeletedNullaryFapProgramRun, ProgramRelated,
      deadNullaryFapBeforeProgram,
      deadNullaryFapAfterProgram] using policy
  cases declarations with
  | cons _external rest =>
      cases rest with
      | cons main _nil =>
          have bodies :
              DeclValueRelated
                (NullarySafeExactShadowCodeRelated 3)
                (.code deadNullaryFapBefore)
                (.code deadNullaryFapAfter) := by
            simpa [fixtureDecl, decl] using main.value
          cases bodies with
          | code related =>
              exact deadNullaryFapNotNullarySafeCode related

/-- Consequently the observable counterexample cannot be smuggled into the
new compiler-facing contract through an opaque runtime certificate. -/
theorem deadNullaryFapNotCompilerAdmissible
    (externals : ExternalSpec) :
    ¬ElimDeadCompilerAdmissibleRun externals 3
      deadNullaryFapBeforeProgram
      deadNullaryFapAfterProgram #[`main] := by
  intro admissible
  exact deadNullaryFapNotNullarySafeProgram
    admissible.noDeletedNullaryFap

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

/-- The fail-closed checker accepts the complete closed write chain and
computes the same exact target as the transparent traversal. -/
theorem closedWritesCheckedRun :
    nullarySafeShadowCode? 8 {} closedWritesBefore =
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
  rw [nullarySafeShadowCode?]
  rw [nullarySafeShadowCode?]
  rw [nullarySafeShadowCode?]
  rw [nullarySafeShadowCode?]
  rw [deletedWritesCheckedRun]
  simp [closedWritesAfter, neutralAfter, neutralUsed, deletedWritesAfter,
    liveDecl, closedWritesObjectDecl, closedWritesUSizeDecl,
    closedWritesScalarDecl, letDecl, safeToElim, isNullaryFap,
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

theorem closedReuseShadowRun :
    shadowCode? 5 {} closedReuseBefore =
      some (closedReuseAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have tokenAbsent :
      reuseTokenVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have argumentAbsent :
      reuseArgVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [closedReuseBefore, closedReuseAfter, closedReuseTokenDecl,
    closedReuseArgDecl, closedReuseLiveDecl, deadReuseDecl, letDecl,
    neutralUsed, shadowCode?, safeToElim, collectLetValue, liveMember, tokenAbsent,
    argumentAbsent, deadAbsent]

theorem closedConcreteReuseShadowRun :
    shadowCode? 6 {} closedConcreteReuseBefore =
      some (closedConcreteReuseAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have objectAbsent :
      resetObjectVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have tokenAbsent :
      reuseTokenVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have argumentAbsent :
      reuseArgVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [closedConcreteReuseBefore, closedConcreteReuseAfter,
    closedConcreteReuseObjectDecl, closedConcreteReuseTokenDecl,
    closedReuseAfter, closedReuseArgDecl, closedReuseLiveDecl,
    deadReuseDecl, letDecl, neutralUsed, shadowCode?, safeToElim,
    collectLetValue, collectArgs, collectArgList, collectArg,
    liveMember, objectAbsent, tokenAbsent, argumentAbsent, deadAbsent]

/-- The checked policy accepts the complete one-cell reset/reuse chain. -/
theorem closedConcreteReuseCheckedRun :
    nullarySafeShadowCode? 6 {} closedConcreteReuseBefore =
      some (closedConcreteReuseAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have objectAbsent :
      resetObjectVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have tokenAbsent :
      reuseTokenVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have argumentAbsent :
      reuseArgVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [closedConcreteReuseBefore, closedConcreteReuseAfter,
    closedConcreteReuseObjectDecl, closedConcreteReuseTokenDecl,
    closedReuseAfter, closedReuseArgDecl, closedReuseLiveDecl,
    deadReuseDecl, letDecl, neutralUsed, nullarySafeShadowCode?,
    safeToElim, isNullaryFap,
    collectLetValue, collectArgs, collectArgList, collectArg,
    liveMember, objectAbsent, tokenAbsent, argumentAbsent, deadAbsent]

theorem closedOwnedReuseShadowRun :
    shadowCode? 7 {} closedOwnedReuseBefore =
      some (closedOwnedReuseAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have childAbsent :
      resetChildVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have objectAbsent :
      resetObjectVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have tokenAbsent :
      reuseTokenVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have argumentAbsent :
      reuseArgVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [closedOwnedReuseBefore, closedOwnedReuseAfter,
    closedOwnedReuseChildDecl, closedOwnedReuseObjectDecl,
    closedOwnedReuseTokenDecl, closedReuseAfter,
    closedReuseArgDecl, closedReuseLiveDecl,
    deadReuseDecl, letDecl, neutralUsed, shadowCode?, safeToElim,
    collectLetValue, collectArgs, collectArgList, collectArg,
    liveMember, childAbsent, objectAbsent, tokenAbsent,
    argumentAbsent, deadAbsent]

/-- The checked policy also accepts recursive child release followed by
concrete-token reuse. -/
theorem closedOwnedReuseCheckedRun :
    nullarySafeShadowCode? 7 {} closedOwnedReuseBefore =
      some (closedOwnedReuseAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have childAbsent :
      resetChildVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have objectAbsent :
      resetObjectVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have tokenAbsent :
      reuseTokenVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have argumentAbsent :
      reuseArgVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [closedOwnedReuseBefore, closedOwnedReuseAfter,
    closedOwnedReuseChildDecl, closedOwnedReuseObjectDecl,
    closedOwnedReuseTokenDecl, closedReuseAfter,
    closedReuseArgDecl, closedReuseLiveDecl,
    deadReuseDecl, letDecl, neutralUsed, nullarySafeShadowCode?,
    safeToElim, isNullaryFap,
    collectLetValue, collectArgs, collectArgList, collectArg,
    liveMember, childAbsent, objectAbsent, tokenAbsent,
    argumentAbsent, deadAbsent]

theorem closedPapBoxShadowRun :
    shadowCode? 6 {} closedPapBoxBefore =
      some (closedPapBoxAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have papArgAbsent :
      papArgVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have papGarbageAbsent :
      papGarbageVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have boxInputAbsent :
      boxInputVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have boxGarbageAbsent :
      boxGarbageVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [closedPapBoxBefore, closedPapBoxAfter,
    closedReuseAfter, closedReuseLiveDecl,
    closedPapBoxPapArgDecl, closedPapBoxPapDecl,
    closedPapBoxInputDecl, closedPapBoxBoxDecl,
    letDecl, neutralUsed, shadowCode?, safeToElim,
    collectLetValue, collectArgs, collectArgList, collectArg,
    liveMember, papArgAbsent, papGarbageAbsent,
    boxInputAbsent, boxGarbageAbsent]

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

theorem closedReuseProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 5)
      closedReuseBeforeProgram closedReuseAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    closedReuseBeforeProgram, closedReuseAfterProgram,
    fixtureDecl, decl, closedReuseShadowRun]

theorem closedConcreteReuseProgramShadowRelated :
    ProgramRelated (ShadowCodeRelated 6)
      closedConcreteReuseBeforeProgram closedConcreteReuseAfterProgram := by
  apply shadowProgram_related
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    closedConcreteReuseBeforeProgram, closedConcreteReuseAfterProgram,
    fixtureDecl, decl, closedConcreteReuseShadowRun]

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

/-- Ordinary inductive ownership contract for the neutral compiler fixture.
The chosen predicate is source-only and indexed by the entry arguments; the
generic bridge below supplies the hereditary non-lockstep premise. -/
def neutralSourceOwnershipContract
    (externals : ExternalSpec) :
    ElimDeadSourceOwnershipContract externals 3
      neutralBeforeProgram #[`main] where
  invariant := fun _ arguments state =>
    NeutralSourceReachable arguments state
  initial := by
    intro entry member arguments
    have entryEq : entry = `main := by
      simpa using member
    subst entry
    exact .entry
  preserved := by
    intro entry arguments before after reachable step
    exact neutralSourceReachable_step reachable step
  ready := by
    intro entry arguments state reachable
    exact neutralSourceReachable_ready state reachable

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
  exact (neutralSourceOwnershipContract externals).initialInvariant

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

/-- The neutral fixture's exact pass graph satisfies the conservative policy:
the erased let is deleted, but no nullary full application occurs. -/
theorem neutralNoDeletedNullaryFapCode :
    NullarySafeExactShadowCodeRelated 3 neutralBefore neutralAfter := by
  refine ⟨neutralUsed, ?_⟩
  change NullarySafeShadowCodeRun 3 {} neutralUsed
    (.let liveDecl (.let deadErasedDecl (.return live)))
    (.let liveDecl (.return live))
  have returned : NullarySafeShadowCodeRun 1 {} neutralUsed
      (.return live) (.return live) := by
    simpa [neutralUsed] using
      (NullarySafeShadowCodeRun.return
        (fuel := 1) (initial := {}) (result := live))
  have inner : NullarySafeShadowCodeRun 2 {} neutralUsed
      (.let deadErasedDecl (.return live)) (.return live) := by
    apply NullarySafeShadowCodeRun.letDeleted returned
    · native_decide
    · rfl
    · rintro ⟨name, arguments, impossible, _empty⟩
      cases impossible
  have outer :=
    NullarySafeShadowCodeRun.letRetained
      (declaration := liveDecl) inner (Or.inl (by native_decide))
  simpa [liveDecl, letDecl, collectLetValue] using outer

/-- The executable checker is complete for the same manually audited graph. -/
theorem neutralCheckedCodeRun :
    nullarySafeShadowCode? 3 {} neutralBefore =
      some (neutralAfter, neutralUsed) := by
  rcases neutralNoDeletedNullaryFapCode with ⟨used, run⟩
  have ordinary := nullarySafeShadowCode_result run.checkedResult
  rw [neutralShadowRun] at ordinary
  have finalEq : neutralUsed = used :=
    congrArg Prod.snd (Option.some.inj ordinary)
  simpa [finalEq] using run.checkedResult

/-- A single executable program equation now supplies both the ordinary
transparent result and the conservative policy certificate. -/
theorem neutralCheckedProgramRun :
    nullarySafeShadowProgram? 3 neutralBeforeProgram =
      some neutralAfterProgram := by
  simp [nullarySafeShadowProgram?, nullarySafeShadowDecls?,
    nullarySafeShadowDecl?, neutralBeforeProgram,
    neutralAfterProgram, fixtureDecl, decl,
    neutralCheckedCodeRun]

/-- Program-level conservative nullary policy for the neutral fixture. -/
theorem neutralNoDeletedNullaryFapProgramRun :
    NoDeletedNullaryFapProgramRun 3
      neutralBeforeProgram neutralAfterProgram := by
  exact (nullarySafeShadowProgram_certifies
    neutralCheckedProgramRun).2

/-- The first concrete compiler-admissible package is constructed from the
single checked-pass equation plus the independent source runtime/ownership
certificate. -/
theorem neutralCompilerAdmissibleRun
    (externals : ExternalSpec) :
    ElimDeadCompilerAdmissibleRun externals 3
      neutralBeforeProgram neutralAfterProgram #[`main] :=
  ElimDeadCompilerAdmissibleRun.ofCheckedOwnership
    neutralBeforeProgramElimDeadWellFormed
    neutralCheckedProgramRun
    (ElimDeadOwnershipContract.ofSource
      (neutralSourceOwnershipContract externals))

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
  nullarySafeShadowProgram_loweringCorrect_of_ownership
    neutralBeforeProgramElimDeadWellFormed
    neutralCheckedProgramRun
    (ElimDeadOwnershipContract.ofSource
      (neutralSourceOwnershipContract externals))
    compatible

/-- The neutral checked-pass fixture also exercises the source-owned
whole-program endpoint. The existing compiler/runtime certificate is reused;
only the explicit foreign heap/frontier law is added. -/
theorem neutralProgramLoweringCorrect_sourceOwned
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 3)
    (sourceCompatible :
      SourceExternalSpecOwnershipCompatible externals) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      neutralBeforeProgram neutralAfterProgram #[`main] :=
  nullarySafeShadowProgram_loweringCorrect_sourceOwned_of_ownership
    neutralBeforeProgramElimDeadWellFormed
    neutralCheckedProgramRun
    (ElimDeadOwnershipContract.ofSource
      (neutralSourceOwnershipContract externals))
    compatible sourceCompatible

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
  apply DeletedReuseReadyAt.none_of_effect
      (values := #[.erased]) (updateHeader := true)
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

/-- Runtime after one retained paired allocation. -/
def nonemptyLedgerPairedRuntime : RuntimeState :=
  (alloc ({} : RuntimeState) (.natural 9223372036854775808)).1

/-- Source runtime after a second, deleted constructor allocation. -/
def nonemptyLedgerSourceRuntime : RuntimeState :=
  (alloc nonemptyLedgerPairedRuntime (.ctor deletedWriteObject)).1

/-- The target retains the first allocation and omits only the second. -/
def nonemptyLedgerTargetRuntime : RuntimeState :=
  nonemptyLedgerPairedRuntime

def nonemptyLedgerSourceEnv : Env :=
  bind liveEnv dead (.object (.heap 1))

def nonemptyLedgerSourceState : MachineState :=
  { program := deletedWritesBeforeProgram
    control := .code deletedWritesBefore
    env := nonemptyLedgerSourceEnv
    runtime := nonemptyLedgerSourceRuntime }

/-- A non-empty target exercises the allocation-ledger bridge end to end.
Location `0` is a retained paired allocation; source location `1` is allocated
after the ledger snapshot and is therefore unmapped and safe for the deleted
write. -/
theorem nonemptyTargetAllocationLedger_objectSetReady :
    ∃ rho : AddressRenaming,
      ∃ ledger : TargetAllocationLedger rho
          nonemptyLedgerTargetRuntime.nextLocation,
      ShadowRuntimeRel rho
          nonemptyLedgerSourceRuntime nonemptyLedgerTargetRuntime
          [.object (.heap 0)] [.object (.heap 0)] ∧
        SourceOnlyUnderTargetLedger ledger 1 ∧
        DeletedObjectSetReadyAt nonemptyLedgerSourceState
          (runtimeRoots nonemptyLedgerSourceRuntime
            [.object (.heap 0)])
          dead 0 .erased := by
  let paired := LedgerShadowRuntimeRel.empty.allocBoth
      (HeapObjectRel.natural 9223372036854775808)
      (by simp [RootSubset, HeapObject.ownedValues])
      (by simp [RootSubset, HeapObject.ownedValues])
      false
  let sourceOnlyRuntime :=
    paired.runtime.allocLeftGarbage (.ctor deletedWriteObject) false
  have fresh : paired.larger.forward 1 = none := by
    apply paired.runtime.runtime.leftMappingFresh
    simp [alloc]
  have sourceOnly :
      SourceOnlyUnderTargetLedger sourceOnlyRuntime.ledger 1 :=
    sourceOnlyRuntime.ledger.sourceOnly_of_forwardUnmapped fresh
  have related :
      ShadowRuntimeRel paired.larger
        nonemptyLedgerSourceRuntime nonemptyLedgerTargetRuntime
        [.object (.heap 0)] [.object (.heap 0)] := by
    simpa [nonemptyLedgerSourceRuntime, nonemptyLedgerTargetRuntime,
      nonemptyLedgerPairedRuntime, alloc] using sourceOnlyRuntime.runtime
  refine ⟨paired.larger, sourceOnlyRuntime.ledger,
    related, sourceOnly, ?_⟩
  have binding :
      SourceOnlyHeapBinding sourceOnlyRuntime.ledger
        nonemptyLedgerSourceState.env dead 1 := {
    read := by
      simp [nonemptyLedgerSourceState, nonemptyLedgerSourceEnv,
        lookupValue, Impure.bind, lookup, dead]
    sourceOnly
  }
  apply binding.deletedObjectSetReadyAt_of_effect
      (related := related)
  · rfl
  · rfl

/-- The retained target allocation is visible through `live`; the reset
object is the source-only allocation at location `1`. -/
def nonemptyLedgerRetainedEnv : Env :=
  bind [] live (.object (.heap 0))

def nonemptyLedgerResetEnv : Env :=
  bind nonemptyLedgerRetainedEnv resetObjectVar (.object (.heap 1))

def nonemptyLedgerResetState : MachineState :=
  { program := deletedResetBeforeProgram
    control := .code deletedResetBefore
    env := nonemptyLedgerResetEnv
    runtime := nonemptyLedgerSourceRuntime }

def nonemptyLedgerClearedObject : ConstructorObject :=
  { deletedWriteObject with
    objectFields := #[.object (.tagged 0)] }

def nonemptyLedgerClearedCell : HeapCell :=
  { object := .ctor nonemptyLedgerClearedObject }

/-- Reset rewrites only source location `1`; retained source owner `0`
remains byte-for-byte unchanged. -/
def nonemptyLedgerResetRuntime : RuntimeState :=
  { nonemptyLedgerSourceRuntime with
    heap :=
      [(1, nonemptyLedgerClearedCell),
        (0, { object := .natural 9223372036854775808 })] }

def nonemptyLedgerReuseEnv : Env :=
  bind
    (bind nonemptyLedgerResetEnv reuseTokenVar
      (.reuseToken (some 1)))
    reuseArgVar .erased

def nonemptyLedgerReuseState : MachineState :=
  { program := deletedReuseBeforeProgram
    control := .code deletedReuseBefore
    env := nonemptyLedgerReuseEnv
    runtime := nonemptyLedgerResetRuntime }

theorem nonemptyLedgerResetEffect :
    reset nonemptyLedgerSourceRuntime 1 (.object (.heap 1)) =
      .ok (nonemptyLedgerResetRuntime, .reuseToken (some 1)) := by
  rfl

def nonemptyLedgerResetLocalReady :
    DeletedResetLocalReadyAt
      nonemptyLedgerResetState 1 resetObjectVar := by
  apply DeletedResetLocalReadyAt.of_evalLetValue
      (fvarId := dead)
      (binderName := dead.name)
      (type := objType)
      (nextRuntime := nonemptyLedgerResetRuntime)
      (tokenValue := .reuseToken (some 1))
  rfl

/-- Nonempty-ledger reset/reuse ownership regression. The ledger records
target owner `0`; reset and concrete reuse operate on source-only location
`1`. Reset preserves the recorded owner, after which the same ledger proves
that overwriting location `1` is unreachable from every published root. -/
theorem nonemptyTargetAllocationLedger_resetReuseReady :
    ∃ rho : AddressRenaming,
      ∃ ledger : TargetAllocationLedger rho
          nonemptyLedgerTargetRuntime.nextLocation,
      ShadowRuntimeRel rho
          nonemptyLedgerSourceRuntime nonemptyLedgerTargetRuntime
          [.object (.heap 0)] [.object (.heap 0)] ∧
        SourceOnlyUnderTargetLedger ledger 1 ∧
        DeletedResetReadyAt nonemptyLedgerResetState
          (runtimeRoots nonemptyLedgerSourceRuntime
            [.object (.heap 0)])
          1 resetObjectVar ∧
        ShadowRuntimeRel rho
          nonemptyLedgerResetRuntime nonemptyLedgerTargetRuntime
          [.object (.heap 0)] [.object (.heap 0)] ∧
        DeletedReuseReadyAt nonemptyLedgerReuseState
          (runtimeRoots nonemptyLedgerResetRuntime
            [.object (.heap 0)])
          reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] := by
  let paired := LedgerShadowRuntimeRel.empty.allocBoth
      (HeapObjectRel.natural 9223372036854775808)
      (by simp [RootSubset, HeapObject.ownedValues])
      (by simp [RootSubset, HeapObject.ownedValues])
      false
  let sourceOnlyRuntime :=
    paired.runtime.allocLeftGarbage (.ctor deletedWriteObject) false
  have fresh : paired.larger.forward 1 = none := by
    apply paired.runtime.runtime.leftMappingFresh
    simp [alloc]
  have sourceOnly :
      SourceOnlyUnderTargetLedger sourceOnlyRuntime.ledger 1 :=
    sourceOnlyRuntime.ledger.sourceOnly_of_forwardUnmapped fresh
  have related :
      ShadowRuntimeRel paired.larger
        nonemptyLedgerSourceRuntime nonemptyLedgerTargetRuntime
        [.object (.heap 0)] [.object (.heap 0)] := by
    simpa [nonemptyLedgerSourceRuntime, nonemptyLedgerTargetRuntime,
      nonemptyLedgerPairedRuntime, alloc] using sourceOnlyRuntime.runtime
  have objectBinding :
      SourceOnlyHeapBinding sourceOnlyRuntime.ledger
        nonemptyLedgerResetState.env resetObjectVar 1 := {
    read := by
      simp [nonemptyLedgerResetState, nonemptyLedgerResetEnv,
        nonemptyLedgerRetainedEnv, lookupValue, Impure.bind, lookup,
        resetObjectVar, live]
    sourceOnly
  }
  have found :
      findCell? nonemptyLedgerSourceRuntime.heap 1 =
        some ({ object := .ctor deletedWriteObject } : HeapCell) := by
    rfl
  have noChildren : ∀ child,
      Value.object (.heap child) ∉
        ({ object := .ctor deletedWriteObject } :
          HeapCell).object.ownedValues.toList := by
    intro child member
    simp [HeapObject.ownedValues, deletedWriteObject] at member
  have closure :
      SourceOnlyHeapClosureBinding sourceOnlyRuntime.ledger
        nonemptyLedgerResetState.env resetObjectVar 1
        nonemptyLedgerSourceRuntime.heap :=
    objectBinding.closure_of_no_heap_children found noChildren
  have ownerFrame :=
    nonemptyLedgerResetLocalReady
      |>.ownerFrame_of_sourceOnlyHeapClosureBinding
        sourceOnlyRuntime.ledger closure
  have afterFresh : ∀ location,
      nonemptyLedgerResetRuntime.nextLocation ≤ location →
        findCell? nonemptyLedgerResetRuntime.heap location = none := by
    intro location bounded
    change 2 ≤ location at bounded
    have oneLt : 1 < location :=
      Nat.lt_of_lt_of_le (by decide) bounded
    have zeroLt : 0 < location :=
      Nat.lt_trans (by decide) oneLt
    have notOne : (1 : Nat) ≠ location := Nat.ne_of_lt oneLt
    have notZero : (0 : Nat) ≠ location := Nat.ne_of_lt zeroLt
    simp [nonemptyLedgerResetRuntime, findCell?, notOne, notZero]
  have frame :
      RuntimeReachableFrame nonemptyLedgerSourceRuntime
        nonemptyLedgerResetRuntime
        (runtimeRoots nonemptyLedgerSourceRuntime
          [.object (.heap 0)]) :=
    related.leftRuntimeReachableFrame_of_targetAllocationLedger
      sourceOnlyRuntime.ledger rfl rfl rfl rfl ownerFrame afterFresh
  have resetReady :
      DeletedResetReadyAt nonemptyLedgerResetState
        (runtimeRoots nonemptyLedgerSourceRuntime
          [.object (.heap 0)])
        1 resetObjectVar :=
    nonemptyLedgerResetLocalReady
      |>.deletedReadyAt_of_targetAllocationLedger_sourceOnlyClosure
        related sourceOnlyRuntime.ledger closure rfl rfl rfl afterFresh
  have relatedAfter :
      ShadowRuntimeRel paired.larger
        nonemptyLedgerResetRuntime nonemptyLedgerTargetRuntime
        [.object (.heap 0)] [.object (.heap 0)] :=
    related.frameLeft frame
  have reuseReady :
      DeletedReuseReadyAt nonemptyLedgerReuseState
        (runtimeRoots nonemptyLedgerResetRuntime
          [.object (.heap 0)])
        reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] :=
    by
      have binding :
          SourceOnlyReuseTokenBinding sourceOnlyRuntime.ledger
            nonemptyLedgerReuseState.env reuseTokenVar 1 := {
        read := by
          simp [nonemptyLedgerReuseState, nonemptyLedgerReuseEnv,
            nonemptyLedgerResetEnv, nonemptyLedgerRetainedEnv,
            lookupValue, Impure.bind, lookup,
            reuseTokenVar, reuseArgVar, resetObjectVar, live]
        sourceOnly
      }
      apply binding.deletedReuseSomeReadyAt_of_effect
          (values := #[.erased]) (updateHeader := true)
          (related := relatedAfter)
      · simp [nonemptyLedgerReuseState, nonemptyLedgerReuseEnv,
          nonemptyLedgerResetEnv, nonemptyLedgerRetainedEnv,
          evalArgs, evalArg, Impure.bind, lookup,
          reuseTokenVar, reuseArgVar, resetObjectVar, live]
        rfl
      · rfl
  exact ⟨paired.larger, sourceOnlyRuntime.ledger, related, sourceOnly,
    resetReady, relatedAfter, reuseReady⟩

def nonemptyLedgerResetTargetState : MachineState :=
  { program := deletedResetAfterProgram
    control := .code deletedResetAfter
    env := nonemptyLedgerRetainedEnv
    runtime := nonemptyLedgerTargetRuntime }

def nonemptyLedgerReuseTargetState : MachineState :=
  { program := deletedReuseAfterProgram
    control := .code deletedReuseAfter
    env := nonemptyLedgerRetainedEnv
    runtime := nonemptyLedgerTargetRuntime }

theorem neutralUsed_toList :
    neutralUsed.toList = [live] := by
  apply List.Perm.eq_singleton
  simpa [neutralUsed] using
    (Std.HashSet.toList_insert_perm
      (m := ({} : UsedLocals)) (k := live))

theorem nonemptyLedgerResetEnvRoots :
    envRootsOn neutralUsed nonemptyLedgerResetState.env =
      [.object (.heap 0)] := by
  simp [envRootsOn, neutralUsed_toList,
    nonemptyLedgerResetState, nonemptyLedgerResetEnv,
    nonemptyLedgerRetainedEnv, Impure.bind, lookup,
    resetObjectVar, live]

theorem nonemptyLedgerReuseEnvRoots :
    envRootsOn neutralUsed nonemptyLedgerReuseState.env =
      [.object (.heap 0)] := by
  simp [envRootsOn, neutralUsed_toList,
    nonemptyLedgerReuseState, nonemptyLedgerReuseEnv,
    nonemptyLedgerResetEnv, nonemptyLedgerRetainedEnv,
    Impure.bind, lookup, reuseTokenVar, reuseArgVar,
    resetObjectVar, live]

theorem nonemptyLedgerResetTargetEnvRoots :
    envRootsOn neutralUsed nonemptyLedgerResetTargetState.env =
      [.object (.heap 0)] := by
  simp [envRootsOn, neutralUsed_toList,
    nonemptyLedgerResetTargetState, nonemptyLedgerRetainedEnv,
    Impure.bind, lookup, live]

theorem nonemptyLedgerReuseTargetEnvRoots :
    envRootsOn neutralUsed nonemptyLedgerReuseTargetState.env =
      [.object (.heap 0)] := by
  simp [envRootsOn, neutralUsed_toList,
    nonemptyLedgerReuseTargetState, nonemptyLedgerRetainedEnv,
    Impure.bind, lookup, live]

theorem nonemptyLedgerResetEnvRelated
    (mapping : rho.forward 0 = some 0) :
    EnvRelOn rho neutralUsed
      nonemptyLedgerResetState.env
      nonemptyLedgerResetTargetState.env := by
  intro fvarId member
  have same : live = fvarId := by
    simpa [neutralUsed] using member
  subst fvarId
  exact .some (.heap mapping)

theorem nonemptyLedgerReuseEnvRelated
    (mapping : rho.forward 0 = some 0) :
    EnvRelOn rho neutralUsed
      nonemptyLedgerReuseState.env
      nonemptyLedgerReuseTargetState.env := by
  intro fvarId member
  have same : live = fvarId := by
    simpa [neutralUsed] using member
  subst fvarId
  exact .some (.heap mapping)

theorem nonemptyLedgerResetExactCodeReadyAt
    (ready :
      DeletedResetReadyAt nonemptyLedgerResetState
        (runtimeRoots nonemptyLedgerSourceRuntime
          [.object (.heap 0)])
        1 resetObjectVar) :
    BinderReadyShadowCodeReadyAt 2 neutralUsed
      nonemptyLedgerResetState
      (runtimeRoots nonemptyLedgerResetState.runtime
        (envRootsOn neutralUsed nonemptyLedgerResetState.env ++ []))
      deletedResetBefore deletedResetAfter := by
  refine ⟨2, neutralUsed, Nat.le_refl 2,
    deletedResetExactGraph, UsedSubset.refl neutralUsed,
    deletedResetExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt nonemptyLedgerResetState
        (runtimeRoots nonemptyLedgerResetState.runtime
          (envRootsOn neutralUsed nonemptyLedgerResetState.env ++ []))
        deadResetDecl := by
    unfold deadResetDecl letDecl
    exact .reset dead dead.name objType 1 resetObjectVar
      (by
        rw [nonemptyLedgerResetEnvRoots]
        simpa [nonemptyLedgerResetState] using ready)
  have kept :
      RetainedLetReadyAt nonemptyLedgerResetState
        (runtimeRoots nonemptyLedgerResetState.runtime
          (envRootsOn neutralUsed nonemptyLedgerResetState.env ++ []))
        deadResetDecl.value := by
    trivial
  exact ExactShadowCodeRuntimeReadyAt.let_of_ready removed kept

theorem nonemptyLedgerReuseExactCodeReadyAt
    (ready :
      DeletedReuseReadyAt nonemptyLedgerReuseState
        (runtimeRoots nonemptyLedgerResetRuntime
          [.object (.heap 0)])
        reuseTokenVar oneFieldInfo #[.fvar reuseArgVar]) :
    BinderReadyShadowCodeReadyAt 2 neutralUsed
      nonemptyLedgerReuseState
      (runtimeRoots nonemptyLedgerReuseState.runtime
        (envRootsOn neutralUsed nonemptyLedgerReuseState.env ++ []))
      deletedReuseBefore deletedReuseAfter := by
  refine ⟨2, neutralUsed, Nat.le_refl 2,
    deletedReuseSomeExactGraph, UsedSubset.refl neutralUsed,
    deletedReuseSomeExactBinderReady, ?_⟩
  have removed :
      DeletedLetReadyAt nonemptyLedgerReuseState
        (runtimeRoots nonemptyLedgerReuseState.runtime
          (envRootsOn neutralUsed nonemptyLedgerReuseState.env ++ []))
        deadReuseDecl := by
    unfold deadReuseDecl letDecl
    exact .reuse dead dead.name objType reuseTokenVar oneFieldInfo true
      #[.fvar reuseArgVar]
      (by
        rw [nonemptyLedgerReuseEnvRoots]
        simpa [nonemptyLedgerReuseState] using ready)
  have decision :
      deletedReuseSomeExactGraph.view.runtimeDecision = .deletedLet :=
    ExactShadowCodeView.runtimeDecision_eq_deletedLet_of_target_not_let
      deletedReuseSomeExactGraph.view
        (by
          intro targetDeclaration targetContinuation
          simp [deletedReuseAfter])
  exact ExactShadowCodeRuntimeReadyAt.letDeleted decision removed

/-- The nonempty-ledger runtime witnesses lift to exact machine readiness for
both source-only operations. These are the two active-code obligations that
the retained-prefix whole-program invariant will dispatch at reset and reuse
residuals. -/
theorem nonemptyTargetAllocationLedger_resetReuseMachineReady :
    LedgerBinderReadyReachableMachineReadyAt 2
        nonemptyLedgerResetState nonemptyLedgerResetTargetState ∧
      LedgerBinderReadyReachableMachineReadyAt 2
        nonemptyLedgerReuseState nonemptyLedgerReuseTargetState := by
  rcases nonemptyTargetAllocationLedger_resetReuseReady with
    ⟨rho, ledger, related, sourceOnly, resetReady,
      relatedAfter, reuseReady⟩
  have mapping : rho.forward 0 = some 0 := by
    have roots := related.extra
    cases roots with
    | cons values tail =>
      cases values with
      | heap mapped => exact mapped
  constructor
  · refine ⟨rho,
      envRootsOn neutralUsed nonemptyLedgerResetState.env,
      envRootsOn neutralUsed nonemptyLedgerResetTargetState.env,
      [], [], ledger, ?_, ?_, .nil, ?_⟩
    · simpa [nonemptyLedgerResetState,
        nonemptyLedgerResetTargetState] using
        deletedResetProgramBinderReadyRelated
    · exact .code
        (nonemptyLedgerResetExactCodeReadyAt resetReady)
        (BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed)
        (nonemptyLedgerResetEnvRelated mapping)
    · rw [nonemptyLedgerResetEnvRoots,
        nonemptyLedgerResetTargetEnvRoots]
      simpa [nonemptyLedgerResetState,
        nonemptyLedgerResetTargetState] using related
  · refine ⟨rho,
      envRootsOn neutralUsed nonemptyLedgerReuseState.env,
      envRootsOn neutralUsed nonemptyLedgerReuseTargetState.env,
      [], [], ledger, ?_, ?_, .nil, ?_⟩
    · simpa [nonemptyLedgerReuseState,
        nonemptyLedgerReuseTargetState] using
        deletedReuseSomeProgramBinderReadyRelated
    · exact .code
        (nonemptyLedgerReuseExactCodeReadyAt reuseReady)
        (BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed)
        (nonemptyLedgerReuseEnvRelated mapping)
    · rw [nonemptyLedgerReuseEnvRoots,
        nonemptyLedgerReuseTargetEnvRoots]
      simpa [nonemptyLedgerReuseState,
        nonemptyLedgerReuseTargetState] using relatedAfter

/-- Unified ledger-dispatch regression for the deleted reset edge with one
retained target allocation. -/
theorem nonemptyLedgerResetExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals nonemptyLedgerResetState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
          nonemptyLedgerResetTargetState targetAfter ∧
        SomeLedgerBinderReadyReachableMachineRelated 2
          sourceAfter targetAfter :=
  nonemptyTargetAllocationLedger_resetReuseMachineReady.1.related
    |>.matchCodeStep_of_ready
      nonemptyTargetAllocationLedger_resetReuseMachineReady.1 rfl step

/-- Unified ledger-dispatch regression for the concrete reuse edge under the
same nonempty owner table. -/
theorem nonemptyLedgerReuseExactStepPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals nonemptyLedgerReuseState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
          nonemptyLedgerReuseTargetState targetAfter ∧
        SomeLedgerBinderReadyReachableMachineRelated 2
          sourceAfter targetAfter :=
  nonemptyTargetAllocationLedger_resetReuseMachineReady.2.related
    |>.matchCodeStep_of_ready
      nonemptyTargetAllocationLedger_resetReuseMachineReady.2 rfl step

/-- A retained large natural forces the paired-allocation branch of the
ledger-aware literal matcher. -/
def retainedLargeNatDecl : LCNF.LetDecl .impure :=
  letDecl live objType (.lit (.nat 9223372036854775808))

def retainedLargeNatCode : LCNF.Code .impure :=
  .let retainedLargeNatDecl (.return live)

theorem retainedLargeNatShadowRun :
    shadowCode? 2 {} retainedLargeNatCode =
      some (retainedLargeNatCode, neutralUsed) := by
  simp [retainedLargeNatCode, retainedLargeNatDecl, letDecl,
    neutralUsed, shadowCode?, safeToElim, collectLetValue, live]

def retainedLargeNatExactGraph :
    ExactShadowCodeGraph 2 neutralUsed
      retainedLargeNatCode retainedLargeNatCode :=
  ExactShadowCodeGraph.ofResult retainedLargeNatShadowRun

theorem retainedLargeNatExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      retainedLargeNatExactGraph.view := by
  apply retainedLargeNatExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [retainedLargeNatCode, retainedLargeNatDecl, letDecl,
      codeBinderIds, BinderNamesUnique, live]

/-- The exact one-layer view used by the ledger matcher, with the
continuation seed and liveness output exposed definitionally. -/
def retainedLargeNatContinuationRun :
    ExactShadowCodeRun 1 {} neutralUsed
      (.return live) (.return live) where
  result := by
    simp [shadowCode?, neutralUsed]

theorem retainedLargeNatStepBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedLargeNatDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedLargeNatDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · simp [codeBinderIds, BinderNamesUnique]

def retainedLargeNatState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedLargeNatCode }

theorem retainedLargeNatSourceOwnership :
    SourceMachineOwnershipBelowFrontier retainedLargeNatState := by
  exact {
    heap := by
      simpa [retainedLargeNatState] using
        HeapOwnershipBelowFrontier.empty
    env := by
      intro fvarId value found
      simp [retainedLargeNatState, lookup] at found
    frames := trivial
  }

/-- Compiler-facing regression for the paired branch: one concrete
heap-backed retained literal takes one source and one target step and returns
a post-state carrying the enlarged target-allocation ledger. -/
theorem retainedLargeNatExactStepLedgerPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedLargeNatState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedLargeNatState targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedLargeNatState.program retainedLargeNatState.program := by
    simpa [retainedLargeNatState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedLargeNatState.frames retainedLargeNatState.frames [] [] := by
    simpa [retainedLargeNatState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        retainedLargeNatState.joins retainedLargeNatState.joins := by
    simpa [retainedLargeNatState] using
      BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        retainedLargeNatState.env retainedLargeNatState.env := by
    simpa [retainedLargeNatState] using
      EnvRelOn.empty emptyAddressRenaming neutralUsed
  have runtime :
      LedgerShadowRuntimeRel emptyAddressRenaming
        retainedLargeNatState.runtime retainedLargeNatState.runtime
        (envRootsOn neutralUsed retainedLargeNatState.env ++ [])
        (envRootsOn neutralUsed retainedLargeNatState.env ++ []) := by
    have emptyRoots (used : UsedLocals) :
        envRootsOn used ([] : Env) = [] := by
      unfold envRootsOn
      induction used.toList with
      | nil => rfl
      | cons head tail ih =>
          simp [lookup]
    simpa [retainedLargeNatState, emptyRoots] using
      LedgerShadowRuntimeRel.empty
  simpa [retainedLargeNatState, retainedLargeNatCode,
    retainedLargeNatDecl, letDecl] using
    retainedLargeNatStepBinderReady.match_retainedLiteralLetStep_ledger
      (fuelBound := Nat.le_refl 2)
      (usedBound := UsedSubset.refl neutralUsed)
    retainedLargeNatState retainedLargeNatState programs frames joins env
      runtime step

/-- The same concrete heap-backed literal allocation preserves the complete
source ownership carrier while extending the paired address renaming. -/
theorem retainedLargeNatExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedLargeNatState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedLargeNatState targetAfter ∧
      BinderReadyReachableMachineRelated 2 larger sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedLargeNatState.program retainedLargeNatState.program := by
    simpa [retainedLargeNatState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedLargeNatState.frames retainedLargeNatState.frames [] [] := by
    simpa [retainedLargeNatState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        retainedLargeNatState.joins retainedLargeNatState.joins := by
    simpa [retainedLargeNatState] using
      BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        retainedLargeNatState.env retainedLargeNatState.env := by
    simpa [retainedLargeNatState] using
      EnvRelOn.empty emptyAddressRenaming neutralUsed
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        retainedLargeNatState.runtime retainedLargeNatState.runtime
        (envRootsOn neutralUsed retainedLargeNatState.env ++ [])
        (envRootsOn neutralUsed retainedLargeNatState.env ++ []) := by
    simpa [retainedLargeNatState] using
      emptyRuntime_shadowRelated_of_roots (envRootsOn_related env)
  simpa [retainedLargeNatState, retainedLargeNatCode,
    retainedLargeNatDecl, letDecl] using
    retainedLargeNatStepBinderReady
      |>.match_retainedLiteralLetStep_withOwnership
        (fuelBound := Nat.le_refl 2)
        (usedBound := UsedSubset.refl neutralUsed)
        retainedLargeNatState retainedLargeNatState programs frames joins env
        runtime retainedLargeNatSourceOwnership step

/-- The exact retained object-projection fixture publishes both the returned
binder and the object local read by the let value. -/
def retainedObjectProjectionUsed : UsedLocals :=
  neutralUsed.insert dead

def retainedObjectProjectionDecl : LCNF.LetDecl .impure :=
  letDecl live objType (.oproj 0 dead)

def retainedObjectProjectionCode : LCNF.Code .impure :=
  .let retainedObjectProjectionDecl (.return live)

theorem retainedObjectProjectionShadowRun :
    shadowCode? 2 {} retainedObjectProjectionCode =
      some (retainedObjectProjectionCode, retainedObjectProjectionUsed) := by
  simp [retainedObjectProjectionCode, retainedObjectProjectionDecl, letDecl,
    retainedObjectProjectionUsed, neutralUsed, shadowCode?, safeToElim,
    collectLetValue, live, dead]

theorem retainedObjectProjectionStepBinderReady :
    ExactShadowCodeBinderReady retainedObjectProjectionUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedObjectProjectionDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedObjectProjectionDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.view.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
    (binders := [])
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact .ret
  · simp [BinderNamesUnique]
  · intro forbidden member
    simp at member

/-- Focused API regression for retained object projections. Once the caller
supplies related machines and a ledger, the exact compiler view alone derives
the object-local coverage needed by the hereditary projection matcher. -/
theorem retainedObjectProjectionExactStepLedgerPreserved
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (BinderReadyShadowCodeRelated 2)
      sourceState.program targetState.program)
    (frames : BinderReadyReachableFramesRelated 2 rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (joins : BinderReadyShadowJoinEnvRelated 2
      retainedObjectProjectionUsed sourceState.joins targetState.joins)
    (env : EnvRelOn rho retainedObjectProjectionUsed
      sourceState.env targetState.env)
    (runtime : LedgerShadowRuntimeRel rho
      sourceState.runtime targetState.runtime
      (envRootsOn retainedObjectProjectionUsed sourceState.env ++
        sourceFrameRoots)
      (envRootsOn retainedObjectProjectionUsed targetState.env ++
        targetFrameRoots))
    (step : Step externals
      { sourceState with control := .code retainedObjectProjectionCode }
      sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code retainedObjectProjectionCode }
        targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 rho
        sourceAfter targetAfter := by
  have usedBound : UsedSubset
      (collectLetValue neutralUsed
        (LCNF.LetValue.oproj 0 dead : LCNF.LetValue .impure))
      retainedObjectProjectionUsed := by
    simpa [retainedObjectProjectionUsed, neutralUsed, collectLetValue]
      using UsedSubset.refl retainedObjectProjectionUsed
  simpa [retainedObjectProjectionCode, retainedObjectProjectionDecl,
    letDecl] using
    retainedObjectProjectionStepBinderReady
      |>.match_retainedObjectProjectionLetStep_ledger
        (fuelBound := Nat.le_refl 2) (usedBound := usedBound)
        sourceState targetState programs frames joins env runtime step

/-- Focused ownership regression for retained object projections. The
successful exact semantic step may bind a heap-valued child; the source heap
carrier proves that child was already below the allocation frontier. -/
theorem retainedObjectProjectionExactStepOwnershipPreserved
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (BinderReadyShadowCodeRelated 2)
      sourceState.program targetState.program)
    (frames : BinderReadyReachableFramesRelated 2 rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (joins : BinderReadyShadowJoinEnvRelated 2
      retainedObjectProjectionUsed sourceState.joins targetState.joins)
    (env : EnvRelOn rho retainedObjectProjectionUsed
      sourceState.env targetState.env)
    (runtime : ShadowRuntimeRel rho
      sourceState.runtime targetState.runtime
      (envRootsOn retainedObjectProjectionUsed sourceState.env ++
        sourceFrameRoots)
      (envRootsOn retainedObjectProjectionUsed targetState.env ++
        targetFrameRoots))
    (ownership : SourceMachineOwnershipBelowFrontier sourceState)
    (step : Step externals
      { sourceState with control := .code retainedObjectProjectionCode }
      sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code retainedObjectProjectionCode }
        targetAfter ∧
      BinderReadyReachableMachineRelated 2 rho sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have usedBound : UsedSubset
      (collectLetValue neutralUsed
        (LCNF.LetValue.oproj 0 dead : LCNF.LetValue .impure))
      retainedObjectProjectionUsed := by
    simpa [retainedObjectProjectionUsed, neutralUsed, collectLetValue]
      using UsedSubset.refl retainedObjectProjectionUsed
  simpa [retainedObjectProjectionCode, retainedObjectProjectionDecl,
    letDecl] using
    retainedObjectProjectionStepBinderReady
      |>.match_retainedObjectProjectionLetStep_withOwnership
        (fuelBound := Nat.le_refl 2) (usedBound := usedBound)
        sourceState targetState programs frames joins env runtime ownership
        step

/-- One paired constructor exercises both root-free retained layout reads. -/
def retainedRootFreeProjectionObject : ConstructorObject :=
  { tag := 0
    objectFields := #[]
    usizeFields := #[7]
    scalarFields := [{
      width := 8
      offset := 0
      value := .uint8 9
    }] }

def retainedRootFreeProjectionRuntime : RuntimeState :=
  (alloc ({} : RuntimeState) (.ctor retainedRootFreeProjectionObject)).1

def retainedRootFreeProjectionEnv : Env :=
  bind [] dead (.object (.heap 0))

def retainedUSizeProjectionDecl : LCNF.LetDecl .impure :=
  letDecl live usizeType (.uproj 0 dead)

def retainedUSizeProjectionCode : LCNF.Code .impure :=
  .let retainedUSizeProjectionDecl (.return live)

def retainedScalarProjectionDecl : LCNF.LetDecl .impure :=
  letDecl live u8Type (.sproj 8 0 dead)

def retainedScalarProjectionCode : LCNF.Code .impure :=
  .let retainedScalarProjectionDecl (.return live)

def retainedUnboxDecl : LCNF.LetDecl .impure :=
  letDecl live u8Type (.unbox dead)

def retainedUnboxCode : LCNF.Code .impure :=
  .let retainedUnboxDecl (.return live)

def retainedIsSharedDecl : LCNF.LetDecl .impure :=
  letDecl live u8Type (.isShared dead)

def retainedIsSharedCode : LCNF.Code .impure :=
  .let retainedIsSharedDecl (.return live)

theorem retainedUSizeProjectionShadowRun :
    shadowCode? 2 {} retainedUSizeProjectionCode =
      some (retainedUSizeProjectionCode, retainedObjectProjectionUsed) := by
  simp [retainedUSizeProjectionCode, retainedUSizeProjectionDecl, letDecl,
    retainedObjectProjectionUsed, neutralUsed, shadowCode?, safeToElim,
    collectLetValue, live, dead]

theorem retainedScalarProjectionShadowRun :
    shadowCode? 2 {} retainedScalarProjectionCode =
      some (retainedScalarProjectionCode, retainedObjectProjectionUsed) := by
  simp [retainedScalarProjectionCode, retainedScalarProjectionDecl, letDecl,
    retainedObjectProjectionUsed, neutralUsed, shadowCode?, safeToElim,
    collectLetValue, live, dead]

theorem retainedUnboxShadowRun :
    shadowCode? 2 {} retainedUnboxCode =
      some (retainedUnboxCode, retainedObjectProjectionUsed) := by
  simp [retainedUnboxCode, retainedUnboxDecl, letDecl,
    retainedObjectProjectionUsed, neutralUsed, shadowCode?, safeToElim,
    collectLetValue, live, dead]

theorem retainedIsSharedShadowRun :
    shadowCode? 2 {} retainedIsSharedCode =
      some (retainedIsSharedCode, retainedObjectProjectionUsed) := by
  simp [retainedIsSharedCode, retainedIsSharedDecl, letDecl,
    retainedObjectProjectionUsed, neutralUsed, shadowCode?, safeToElim,
    collectLetValue, live, dead]

theorem retainedUSizeProjectionStepBinderReady :
    ExactShadowCodeBinderReady retainedObjectProjectionUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedUSizeProjectionDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedUSizeProjectionDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.view.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
    (binders := [])
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact .ret
  · simp [BinderNamesUnique]
  · intro forbidden member
    simp at member

theorem retainedScalarProjectionStepBinderReady :
    ExactShadowCodeBinderReady retainedObjectProjectionUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedScalarProjectionDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedScalarProjectionDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.view.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
    (binders := [])
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact .ret
  · simp [BinderNamesUnique]
  · intro forbidden member
    simp at member

theorem retainedUnboxStepBinderReady :
    ExactShadowCodeBinderReady retainedObjectProjectionUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedUnboxDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedUnboxDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.view.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
    (binders := [])
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact .ret
  · simp [BinderNamesUnique]
  · intro forbidden member
    simp at member

theorem retainedIsSharedStepBinderReady :
    ExactShadowCodeBinderReady retainedObjectProjectionUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedIsSharedDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedIsSharedDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.view.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
    (binders := [])
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact .ret
  · simp [BinderNamesUnique]
  · intro forbidden member
    simp at member

def retainedUSizeProjectionState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedUSizeProjectionCode
    env := retainedRootFreeProjectionEnv
    runtime := retainedRootFreeProjectionRuntime }

def retainedScalarProjectionState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedScalarProjectionCode
    env := retainedRootFreeProjectionEnv
    runtime := retainedRootFreeProjectionRuntime }

def retainedIsSharedState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedIsSharedCode
    env := retainedRootFreeProjectionEnv
    runtime := retainedRootFreeProjectionRuntime }

def retainedTaggedUnboxEnv : Env :=
  bind [] dead (.object (.tagged 9))

def retainedTaggedUnboxState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedUnboxCode
    env := retainedTaggedUnboxEnv }

/-- The paired projection fixture owns its sole heap cell and the matching
environment reference below frontier one. -/
theorem retainedRootFreeProjectionSourceOwnership
    (code : LCNF.Code .impure) :
    SourceMachineOwnershipBelowFrontier
      { program := { decls := #[] }
        control := .code code
        env := retainedRootFreeProjectionEnv
        runtime := retainedRootFreeProjectionRuntime } := by
  have objectBelow :
      HeapLocationsBelowFrontier retainedRootFreeProjectionRuntime
        [.object (.heap 0)] := by
    intro location member
    simp at member
    subst location
    simp [retainedRootFreeProjectionRuntime, alloc]
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · exact {
      heap := by
        change HeapOwnershipBelowFrontier
          (alloc ({} : RuntimeState)
            (.ctor retainedRootFreeProjectionObject) false).1
        apply HeapOwnershipBelowFrontier.empty.alloc
        simp [RootSubset, retainedRootFreeProjectionObject,
          HeapObject.ownedValues]
      env := by
        change EnvironmentBelowFrontier
          retainedRootFreeProjectionRuntime retainedRootFreeProjectionEnv
        rw [retainedRootFreeProjectionEnv]
        exact EnvironmentBelowFrontier.bind
          (runtime := retainedRootFreeProjectionRuntime)
          (env := ([] : Env))
          (binder := dead) (value := .object (.heap 0))
          EnvironmentBelowFrontier.empty objectBelow
    }
  · exact trivial

def retainedRootFreeProjectionObjectRelated :
    HeapObjectRel emptyAddressRenaming
      (.ctor retainedRootFreeProjectionObject)
      (.ctor retainedRootFreeProjectionObject) := by
  apply HeapObjectRel.ctor
  · rfl
  · change ListRel (ValueRel emptyAddressRenaming) [] []
    exact .nil
  · rfl
  · rfl

noncomputable def retainedRootFreeProjectionPaired :=
  LedgerShadowRuntimeRel.empty.allocBoth
    retainedRootFreeProjectionObjectRelated
    (by
      simp [RootSubset, retainedRootFreeProjectionObject,
        HeapObject.ownedValues])
    (by
      simp [RootSubset, retainedRootFreeProjectionObject,
        HeapObject.ownedValues])
    false

theorem retainedRootFreeProjectionValues :
    ValueRel retainedRootFreeProjectionPaired.larger
      (.object (.heap 0)) (.object (.heap 0)) := by
  simpa [retainedRootFreeProjectionPaired, alloc] using
    retainedRootFreeProjectionPaired.values

theorem retainedRootFreeProjectionEnvRelated :
    EnvRelOn retainedRootFreeProjectionPaired.larger
      retainedObjectProjectionUsed
      retainedRootFreeProjectionEnv retainedRootFreeProjectionEnv := by
  simpa [retainedRootFreeProjectionEnv] using
    (EnvRelOn.empty retainedRootFreeProjectionPaired.larger
      retainedObjectProjectionUsed).bindBoth
        (binder := dead) retainedRootFreeProjectionValues

theorem retainedRootFreeProjectionRuntimeRelated :
    ShadowRuntimeRel retainedRootFreeProjectionPaired.larger
      retainedRootFreeProjectionRuntime retainedRootFreeProjectionRuntime
      (envRootsOn retainedObjectProjectionUsed
        retainedRootFreeProjectionEnv ++ [])
      (envRootsOn retainedObjectProjectionUsed
        retainedRootFreeProjectionEnv ++ []) := by
  have rootsSubset : RootSubset
      (envRootsOn retainedObjectProjectionUsed
        retainedRootFreeProjectionEnv)
      [.object (.heap 0)] := by
    intro root member
    have rooted :
        root ∈ .object (.heap 0) ::
          envRootsOn retainedObjectProjectionUsed ([] : Env) :=
      envRootsOn_bind_subset root
        (by simpa [retainedRootFreeProjectionEnv] using member)
    rcases List.mem_cons.mp rooted with rfl | empty
    · simp
    · have emptyRoots :
          envRootsOn retainedObjectProjectionUsed ([] : Env) = [] := by
        unfold envRootsOn
        induction retainedObjectProjectionUsed.toList with
        | nil => rfl
        | cons head tail ih => simp [lookup]
      rw [emptyRoots] at empty
      simp at empty
  simpa only [List.append_nil, retainedRootFreeProjectionRuntime] using
    retainedRootFreeProjectionPaired.runtime.runtime.restrictExtra
      (envRootsOn_related retainedRootFreeProjectionEnvRelated)
      rootsSubset rootsSubset

/-- The tagged unbox fixture relates its immediate object environment under
the empty address renaming. -/
theorem retainedTaggedUnboxEnvRelated :
    EnvRelOn emptyAddressRenaming retainedObjectProjectionUsed
      retainedTaggedUnboxEnv retainedTaggedUnboxEnv := by
  simpa [retainedTaggedUnboxEnv] using
    (EnvRelOn.empty emptyAddressRenaming retainedObjectProjectionUsed)
      |>.bindBoth (binder := dead) (ValueRel.tagged 9)

theorem retainedTaggedUnboxRuntimeRelated :
    ShadowRuntimeRel emptyAddressRenaming
      retainedTaggedUnboxState.runtime retainedTaggedUnboxState.runtime
      (envRootsOn retainedObjectProjectionUsed
        retainedTaggedUnboxState.env ++ [])
      (envRootsOn retainedObjectProjectionUsed
        retainedTaggedUnboxState.env ++ []) := by
  simpa [retainedTaggedUnboxState] using
    emptyRuntime_shadowRelated_of_roots
      (envRootsOn_related retainedTaggedUnboxEnvRelated)

theorem retainedTaggedUnboxOwnership :
    SourceMachineOwnershipBelowFrontier retainedTaggedUnboxState := by
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · exact {
      heap := by
        simpa [retainedTaggedUnboxState] using
          HeapOwnershipBelowFrontier.empty
      env := by
        change EnvironmentBelowFrontier
          retainedTaggedUnboxState.runtime retainedTaggedUnboxState.env
        rw [retainedTaggedUnboxState, retainedTaggedUnboxEnv]
        apply EnvironmentBelowFrontier.bind
          (runtime := ({} : RuntimeState))
          (env := ([] : Env))
          EnvironmentBelowFrontier.empty
        intro location member
        simp at member
    }
  · exact trivial

/-- Concrete exact-dispatch regression for tagged unboxing. -/
theorem retainedTaggedUnboxExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedTaggedUnboxState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals retainedTaggedUnboxState targetAfter ∧
      BinderReadyReachableMachineRelated 2 emptyAddressRenaming
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedTaggedUnboxState.program retainedTaggedUnboxState.program := by
    simpa [retainedTaggedUnboxState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedTaggedUnboxState.frames retainedTaggedUnboxState.frames
        [] [] := by
    simpa [retainedTaggedUnboxState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedObjectProjectionUsed
        retainedTaggedUnboxState.joins retainedTaggedUnboxState.joins := by
    simpa [retainedTaggedUnboxState] using
      BinderReadyShadowJoinEnvRelated.empty 2
        retainedObjectProjectionUsed
  have usedBound : UsedSubset
      (collectLetValue neutralUsed
        (LCNF.LetValue.unbox dead : LCNF.LetValue .impure))
      retainedObjectProjectionUsed := by
    simpa [retainedObjectProjectionUsed, neutralUsed, collectLetValue]
      using UsedSubset.refl retainedObjectProjectionUsed
  simpa [retainedTaggedUnboxState, retainedUnboxCode,
    retainedUnboxDecl, letDecl] using
    retainedUnboxStepBinderReady
      |>.match_retainedUnboxLetStep_withOwnership
        (fuelBound := Nat.le_refl 2) (usedBound := usedBound)
        retainedTaggedUnboxState retainedTaggedUnboxState programs frames
        joins
        (by
          simpa [retainedTaggedUnboxState] using
            retainedTaggedUnboxEnvRelated)
        retainedTaggedUnboxRuntimeRelated retainedTaggedUnboxOwnership step

/-- Concrete exact-dispatch regression for heap sharedness metadata. -/
theorem retainedIsSharedExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedIsSharedState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals retainedIsSharedState targetAfter ∧
      BinderReadyReachableMachineRelated 2
        retainedRootFreeProjectionPaired.larger sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedIsSharedState.program retainedIsSharedState.program := by
    simpa [retainedIsSharedState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2
        retainedRootFreeProjectionPaired.larger
        retainedIsSharedState.frames retainedIsSharedState.frames [] [] := by
    simpa [retainedIsSharedState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2
          retainedRootFreeProjectionPaired.larger [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedObjectProjectionUsed
        retainedIsSharedState.joins retainedIsSharedState.joins := by
    simpa [retainedIsSharedState] using
      BinderReadyShadowJoinEnvRelated.empty 2
        retainedObjectProjectionUsed
  have usedBound : UsedSubset
      (collectLetValue neutralUsed
        (LCNF.LetValue.isShared dead : LCNF.LetValue .impure))
      retainedObjectProjectionUsed := by
    simpa [retainedObjectProjectionUsed, neutralUsed, collectLetValue]
      using UsedSubset.refl retainedObjectProjectionUsed
  simpa [retainedIsSharedState, retainedIsSharedCode,
    retainedIsSharedDecl, letDecl] using
    retainedIsSharedStepBinderReady
      |>.match_retainedIsSharedLetStep_withOwnership
        (fuelBound := Nat.le_refl 2) (usedBound := usedBound)
        retainedIsSharedState retainedIsSharedState programs frames joins
        (by
          simpa [retainedIsSharedState] using
            retainedRootFreeProjectionEnvRelated)
        (by
          simpa [retainedIsSharedState] using
            retainedRootFreeProjectionRuntimeRelated)
        (by
          simpa [retainedIsSharedState] using
            retainedRootFreeProjectionSourceOwnership retainedIsSharedCode)
        step

/-- Concrete exact-dispatch regression for a retained `USize` projection:
the successful root-free read advances both machines and preserves complete
source ownership. -/
theorem retainedUSizeProjectionExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedUSizeProjectionState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals retainedUSizeProjectionState targetAfter ∧
      BinderReadyReachableMachineRelated 2
        retainedRootFreeProjectionPaired.larger sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedUSizeProjectionState.program
        retainedUSizeProjectionState.program := by
    simpa [retainedUSizeProjectionState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2
        retainedRootFreeProjectionPaired.larger
        retainedUSizeProjectionState.frames
        retainedUSizeProjectionState.frames [] [] := by
    simpa [retainedUSizeProjectionState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2
          retainedRootFreeProjectionPaired.larger [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedObjectProjectionUsed
        retainedUSizeProjectionState.joins
        retainedUSizeProjectionState.joins := by
    simpa [retainedUSizeProjectionState] using
      BinderReadyShadowJoinEnvRelated.empty 2
        retainedObjectProjectionUsed
  have usedBound : UsedSubset
      (collectLetValue neutralUsed
        (LCNF.LetValue.uproj 0 dead : LCNF.LetValue .impure))
      retainedObjectProjectionUsed := by
    simpa [retainedObjectProjectionUsed, neutralUsed, collectLetValue]
      using UsedSubset.refl retainedObjectProjectionUsed
  simpa [retainedUSizeProjectionState, retainedUSizeProjectionCode,
    retainedUSizeProjectionDecl, letDecl] using
    retainedUSizeProjectionStepBinderReady
      |>.match_retainedUSizeProjectionLetStep_withOwnership
        (fuelBound := Nat.le_refl 2) (usedBound := usedBound)
        retainedUSizeProjectionState retainedUSizeProjectionState
        programs frames joins
        (by
          simpa [retainedUSizeProjectionState] using
            retainedRootFreeProjectionEnvRelated)
        (by
          simpa [retainedUSizeProjectionState] using
            retainedRootFreeProjectionRuntimeRelated)
        (by
          simpa [retainedUSizeProjectionState] using
            retainedRootFreeProjectionSourceOwnership
              retainedUSizeProjectionCode)
        step

/-- Concrete exact-dispatch regression for a retained packed-scalar
projection. Its scalar result contains no heap location, so the read preserves
the same source ownership carrier. -/
theorem retainedScalarProjectionExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedScalarProjectionState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals retainedScalarProjectionState
        targetAfter ∧
      BinderReadyReachableMachineRelated 2
        retainedRootFreeProjectionPaired.larger sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedScalarProjectionState.program
        retainedScalarProjectionState.program := by
    simpa [retainedScalarProjectionState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2
        retainedRootFreeProjectionPaired.larger
        retainedScalarProjectionState.frames
        retainedScalarProjectionState.frames [] [] := by
    simpa [retainedScalarProjectionState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2
          retainedRootFreeProjectionPaired.larger [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedObjectProjectionUsed
        retainedScalarProjectionState.joins
        retainedScalarProjectionState.joins := by
    simpa [retainedScalarProjectionState] using
      BinderReadyShadowJoinEnvRelated.empty 2
        retainedObjectProjectionUsed
  have usedBound : UsedSubset
      (collectLetValue neutralUsed
        (LCNF.LetValue.sproj 8 0 dead : LCNF.LetValue .impure))
      retainedObjectProjectionUsed := by
    simpa [retainedObjectProjectionUsed, neutralUsed, collectLetValue]
      using UsedSubset.refl retainedObjectProjectionUsed
  simpa [retainedScalarProjectionState, retainedScalarProjectionCode,
    retainedScalarProjectionDecl, letDecl] using
    retainedScalarProjectionStepBinderReady
      |>.match_retainedScalarProjectionLetStep_withOwnership
        (fuelBound := Nat.le_refl 2) (usedBound := usedBound)
        retainedScalarProjectionState retainedScalarProjectionState
        programs frames joins
        (by
          simpa [retainedScalarProjectionState] using
            retainedRootFreeProjectionEnvRelated)
        (by
          simpa [retainedScalarProjectionState] using
            retainedRootFreeProjectionRuntimeRelated)
        (by
          simpa [retainedScalarProjectionState] using
            retainedRootFreeProjectionSourceOwnership
              retainedScalarProjectionCode)
        step

/-- The ordinary transparent traversal also retains the live nullary full
application exactly; the checked-policy theorem above is a stricter
conformance statement about the same branch. -/
theorem retainedNullaryFapShadowRun :
    shadowCode? 2 {} retainedNullaryFap =
      some (retainedNullaryFap, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  simp [retainedNullaryFap, retainedNullaryFapDecl, letDecl,
    neutralUsed, shadowCode?, safeToElim,
    collectLetValue, collectArgs, collectArgList, liveMember]

theorem retainedNullaryFapStepBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedNullaryFapDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedNullaryFapDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · simp [codeBinderIds, BinderNamesUnique]

def retainedNullaryFapState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedNullaryFap }

/-- The retained-call fixture starts from an empty heap, environment, and
frame stack, so its complete source ownership carrier is immediate. -/
theorem retainedNullaryFapSourceMachineOwnershipBelowFrontier :
    SourceMachineOwnershipBelowFrontier retainedNullaryFapState := by
  exact {
    heap := by
      simpa [retainedNullaryFapState] using
        HeapOwnershipBelowFrontier.empty
    env := by
      intro fvarId value found
      simp [retainedNullaryFapState, lookup] at found
    frames := by
      exact trivial
  }

/-- Exact retained-call regression. The nullary full application pushes the
paired bind continuation and enters named invocation on both machines while
the target remains at allocation frontier zero with its empty ledger. -/
theorem retainedNullaryFapExactStepLedgerPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedNullaryFapState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals retainedNullaryFapState targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 emptyAddressRenaming
        sourceAfter targetAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedNullaryFapState.program retainedNullaryFapState.program := by
    simpa [retainedNullaryFapState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedNullaryFapState.frames retainedNullaryFapState.frames
        [] [] := by
    simpa [retainedNullaryFapState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        retainedNullaryFapState.joins retainedNullaryFapState.joins := by
    simpa [retainedNullaryFapState] using
      BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        retainedNullaryFapState.env retainedNullaryFapState.env := by
    simpa [retainedNullaryFapState] using
      EnvRelOn.empty emptyAddressRenaming neutralUsed
  have runtime :
      LedgerShadowRuntimeRel emptyAddressRenaming
        retainedNullaryFapState.runtime retainedNullaryFapState.runtime
        (envRootsOn neutralUsed retainedNullaryFapState.env ++ [])
        (envRootsOn neutralUsed retainedNullaryFapState.env ++ []) := by
    have emptyRoots (used : UsedLocals) :
        envRootsOn used ([] : Env) = [] := by
      unfold envRootsOn
      induction used.toList with
      | nil => rfl
      | cons head tail ih =>
          simp [lookup]
    simpa [retainedNullaryFapState, emptyRoots] using
      LedgerShadowRuntimeRel.empty
  simpa [retainedNullaryFapState, retainedNullaryFap,
    retainedNullaryFapDecl, letDecl] using
    retainedNullaryFapStepBinderReady.match_retainedFapLetStep_ledger
      (fuelBound := Nat.le_refl 2)
      (usedBound := UsedSubset.refl neutralUsed)
      retainedNullaryFapState retainedNullaryFapState programs frames joins
      env runtime step

/-- The same exact retained named-call edge preserves the complete source
ownership carrier while pushing its bind continuation. -/
theorem retainedNullaryFapExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedNullaryFapState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals retainedNullaryFapState targetAfter ∧
      BinderReadyReachableMachineRelated 2 emptyAddressRenaming
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedNullaryFapState.program retainedNullaryFapState.program := by
    simpa [retainedNullaryFapState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedNullaryFapState.frames retainedNullaryFapState.frames
        [] [] := by
    simpa [retainedNullaryFapState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        retainedNullaryFapState.joins retainedNullaryFapState.joins := by
    simpa [retainedNullaryFapState] using
      BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        retainedNullaryFapState.env retainedNullaryFapState.env := by
    simpa [retainedNullaryFapState] using
      EnvRelOn.empty emptyAddressRenaming neutralUsed
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        retainedNullaryFapState.runtime retainedNullaryFapState.runtime
        (envRootsOn neutralUsed retainedNullaryFapState.env ++ [])
        (envRootsOn neutralUsed retainedNullaryFapState.env ++ []) := by
    simpa [retainedNullaryFapState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related
          (EnvRelOn.empty emptyAddressRenaming neutralUsed))
  simpa [retainedNullaryFapState, retainedNullaryFap,
    retainedNullaryFapDecl, letDecl] using
    retainedNullaryFapStepBinderReady
      |>.match_retainedFapLetStep_withOwnership
        (fuelBound := Nat.le_refl 2)
        (usedBound := UsedSubset.refl neutralUsed)
        retainedNullaryFapState retainedNullaryFapState programs frames joins
        env runtime retainedNullaryFapSourceMachineOwnershipBelowFrontier step

/-- A retained one-field constructor forces the paired heap-allocation branch
of the ledger-aware constructor matcher. -/
def retainedCtorDecl : LCNF.LetDecl .impure :=
  letDecl live objType (.ctor oneFieldInfo #[.erased])

def retainedCtorCode : LCNF.Code .impure :=
  .let retainedCtorDecl (.return live)

theorem retainedCtorShadowRun :
    shadowCode? 2 {} retainedCtorCode =
      some (retainedCtorCode, neutralUsed) := by
  simp [retainedCtorCode, retainedCtorDecl, letDecl, oneFieldInfo,
    neutralUsed, shadowCode?, safeToElim, collectLetValue,
    collectArgs, collectArgList, collectArg, live]

def retainedCtorExactGraph :
    ExactShadowCodeGraph 2 neutralUsed retainedCtorCode retainedCtorCode :=
  ExactShadowCodeGraph.ofResult retainedCtorShadowRun

theorem retainedCtorExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      retainedCtorExactGraph.view := by
  apply retainedCtorExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [retainedCtorCode, retainedCtorDecl, letDecl,
      codeBinderIds, BinderNamesUnique, live]

theorem retainedCtorStepBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedCtorDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedCtorDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · simp [codeBinderIds, BinderNamesUnique]

def retainedCtorState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedCtorCode }

theorem retainedCtorSourceOwnership :
    SourceMachineOwnershipBelowFrontier retainedCtorState := by
  exact {
    heap := by
      simpa [retainedCtorState] using
        HeapOwnershipBelowFrontier.empty
    env := by
      intro fvarId value found
      simp [retainedCtorState, lookup] at found
    frames := trivial
  }

/-- Compiler-facing regression for retained constructors: the one-field
constructor takes one source and one target step and exposes the enlarged
allocation ledger selected by their paired heap allocation. -/
theorem retainedCtorExactStepLedgerPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedCtorState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedCtorState targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedCtorState.program retainedCtorState.program := by
    simpa [retainedCtorState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedCtorState.frames retainedCtorState.frames [] [] := by
    simpa [retainedCtorState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        retainedCtorState.joins retainedCtorState.joins := by
    simpa [retainedCtorState] using
      BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        retainedCtorState.env retainedCtorState.env := by
    simpa [retainedCtorState] using
      EnvRelOn.empty emptyAddressRenaming neutralUsed
  have runtime :
      LedgerShadowRuntimeRel emptyAddressRenaming
        retainedCtorState.runtime retainedCtorState.runtime
        (envRootsOn neutralUsed retainedCtorState.env ++ [])
        (envRootsOn neutralUsed retainedCtorState.env ++ []) := by
    have emptyRoots (used : UsedLocals) :
        envRootsOn used ([] : Env) = [] := by
      unfold envRootsOn
      induction used.toList with
      | nil => rfl
      | cons head tail ih =>
          simp [lookup]
    simpa [retainedCtorState, emptyRoots] using
      LedgerShadowRuntimeRel.empty
  simpa [retainedCtorState, retainedCtorCode,
    retainedCtorDecl, letDecl] using
    retainedCtorStepBinderReady.match_retainedCtorLetStep_ledger
      (fuelBound := Nat.le_refl 2)
      (usedBound := UsedSubset.refl neutralUsed)
      retainedCtorState retainedCtorState programs frames joins env runtime
      step

/-- The paired retained-constructor allocation also preserves the source
heap/environment/frame ownership carrier. -/
theorem retainedCtorExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedCtorState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedCtorState targetAfter ∧
      BinderReadyReachableMachineRelated 2 larger sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedCtorState.program retainedCtorState.program := by
    simpa [retainedCtorState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedCtorState.frames retainedCtorState.frames [] [] := by
    simpa [retainedCtorState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        retainedCtorState.joins retainedCtorState.joins := by
    simpa [retainedCtorState] using
      BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        retainedCtorState.env retainedCtorState.env := by
    simpa [retainedCtorState] using
      EnvRelOn.empty emptyAddressRenaming neutralUsed
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        retainedCtorState.runtime retainedCtorState.runtime
        (envRootsOn neutralUsed retainedCtorState.env ++ [])
        (envRootsOn neutralUsed retainedCtorState.env ++ []) := by
    simpa [retainedCtorState] using
      emptyRuntime_shadowRelated_of_roots (envRootsOn_related env)
  simpa [retainedCtorState, retainedCtorCode,
    retainedCtorDecl, letDecl] using
    retainedCtorStepBinderReady
      |>.match_retainedCtorLetStep_withOwnership
        (fuelBound := Nat.le_refl 2)
        (usedBound := UsedSubset.refl neutralUsed)
        retainedCtorState retainedCtorState programs frames joins env runtime
        retainedCtorSourceOwnership step

/-- A nullary constructor is immediate: the ledger-aware constructor runtime
result keeps both empty runtimes, the empty renaming, and target frontier
zero. This covers the retained constructor matcher's no-allocation branch. -/
def nullaryCtorInfo : LCNF.CtorInfo :=
  { name := `Retained.nullary, cidx := 3, size := 0, usize := 0, ssize := 0 }

noncomputable def retainedNullaryCtorResult :
    LedgerCtorBothResult emptyAddressRenaming
      ({} : RuntimeState) ({} : RuntimeState) [] []
      nullaryCtorInfo #[] #[] :=
  LedgerShadowRuntimeRel.empty.allocCtorBoth
    (show ArrayRel (ValueRel emptyAddressRenaming) #[] #[] from .nil)
    (show ListRel (ValueRel emptyAddressRenaming) [] [] from .nil)
    nullaryCtorInfo rfl

theorem retainedNullaryCtorKeepsAllocationLedger :
    retainedNullaryCtorResult.larger = emptyAddressRenaming ∧
    retainedNullaryCtorResult.leftRuntime = ({} : RuntimeState) ∧
    retainedNullaryCtorResult.rightRuntime = ({} : RuntimeState) ∧
    retainedNullaryCtorResult.runtime.ledger.owner = fun _ => 0 := by
  simp [retainedNullaryCtorResult,
    LedgerShadowRuntimeRel.allocCtorBoth, nullaryCtorInfo,
    LedgerShadowRuntimeRel.empty, TargetAllocationLedger.empty]

/-- A retained underapplied function allocates a closure on both sides and
therefore exercises the paired PAP ledger branch. -/
def retainedPapDecl : LCNF.LetDecl .impure :=
  letDecl live objType (.pap `first #[.erased])

def retainedPapCode : LCNF.Code .impure :=
  .let retainedPapDecl (.return live)

theorem retainedPapShadowRun :
    shadowCode? 2 {} retainedPapCode =
      some (retainedPapCode, neutralUsed) := by
  simp [retainedPapCode, retainedPapDecl, letDecl, neutralUsed,
    shadowCode?, safeToElim, collectLetValue, collectArgs, collectArgList,
    collectArg, live]

def retainedPapExactGraph :
    ExactShadowCodeGraph 2 neutralUsed retainedPapCode retainedPapCode :=
  ExactShadowCodeGraph.ofResult retainedPapShadowRun

theorem retainedPapExactBinderReady :
    ExactShadowCodeBinderReady neutralUsed retainedPapExactGraph.view := by
  apply retainedPapExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [retainedPapCode, retainedPapDecl, letDecl,
      codeBinderIds, BinderNamesUnique, live]

theorem retainedPapStepBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedPapDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedPapDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · simp [codeBinderIds, BinderNamesUnique]

def retainedPapProgram : ImpureProgram :=
  { decls := #[firstDecl] }

def retainedPapState : MachineState :=
  { program := retainedPapProgram
    control := .code retainedPapCode }

theorem retainedPapSourceOwnership :
    SourceMachineOwnershipBelowFrontier retainedPapState := by
  exact {
    heap := by
      simpa [retainedPapState] using
        HeapOwnershipBelowFrontier.empty
    env := by
      intro fvarId value found
      simp [retainedPapState, lookup] at found
    frames := trivial
  }

theorem retainedPapProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 2)
      retainedPapProgram retainedPapProgram := by
  unfold retainedPapProgram ProgramRelated
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated 2))
    [firstDecl] [firstDecl]
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
  · exact .nil

/-- Compiler-facing PAP regression: successful retained underapplication
takes one source and target step and returns the proof-relevant paired closure
ledger. -/
theorem retainedPapExactStepLedgerPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedPapState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedPapState targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter := by
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedPapState.frames retainedPapState.frames [] [] := by
    simpa [retainedPapState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        retainedPapState.joins retainedPapState.joins := by
    simpa [retainedPapState] using
      BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        retainedPapState.env retainedPapState.env := by
    simpa [retainedPapState] using
      EnvRelOn.empty emptyAddressRenaming neutralUsed
  have runtime :
      LedgerShadowRuntimeRel emptyAddressRenaming
        retainedPapState.runtime retainedPapState.runtime
        (envRootsOn neutralUsed retainedPapState.env ++ [])
        (envRootsOn neutralUsed retainedPapState.env ++ []) := by
    have emptyRoots (used : UsedLocals) :
        envRootsOn used ([] : Env) = [] := by
      unfold envRootsOn
      induction used.toList with
      | nil => rfl
      | cons head tail ih =>
          simp [lookup]
    simpa [retainedPapState, emptyRoots] using
      LedgerShadowRuntimeRel.empty
  simpa [retainedPapState, retainedPapCode,
    retainedPapDecl, letDecl] using
    retainedPapStepBinderReady.match_retainedPapLetStep_ledger
      (fuelBound := Nat.le_refl 2)
      (usedBound := UsedSubset.refl neutralUsed)
      retainedPapState retainedPapState
      retainedPapProgramBinderReadyRelated frames joins env runtime step

/-- The same concrete paired closure allocation preserves complete source
ownership while extending the semantic address renaming. -/
theorem retainedPapExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedPapState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedPapState targetAfter ∧
      BinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedPapState.frames retainedPapState.frames [] [] := by
    simpa [retainedPapState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        retainedPapState.joins retainedPapState.joins := by
    simpa [retainedPapState] using
      BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        retainedPapState.env retainedPapState.env := by
    simpa [retainedPapState] using
      EnvRelOn.empty emptyAddressRenaming neutralUsed
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        retainedPapState.runtime retainedPapState.runtime
        (envRootsOn neutralUsed retainedPapState.env ++ [])
        (envRootsOn neutralUsed retainedPapState.env ++ []) := by
    simpa [retainedPapState] using
      emptyRuntime_shadowRelated_of_roots (envRootsOn_related env)
  simpa [retainedPapState, retainedPapCode,
    retainedPapDecl, letDecl] using
    retainedPapStepBinderReady
      |>.match_retainedPapLetStep_withOwnership
        (fuelBound := Nat.le_refl 2)
        (usedBound := UsedSubset.refl neutralUsed)
        retainedPapState retainedPapState
        retainedPapProgramBinderReadyRelated frames joins env runtime
        retainedPapSourceOwnership step

/-- The deleted PAP fixture's successful source-only closure allocation keeps
the empty target ledger unchanged. -/
noncomputable def deletedPapLedgerResult :
    LedgerPapLeftGarbageResult emptyAddressRenaming
      deletedPapSourceState deletedPapTargetState.runtime
      (envRootsOn neutralUsed deletedPapSourceState.env)
      (envRootsOn neutralUsed deletedPapTargetState.env)
      dead dead.name objType `first #[.fvar papArgVar] :=
  let related : LedgerShadowRuntimeRel emptyAddressRenaming
      deletedPapSourceState.runtime deletedPapTargetState.runtime
      (envRootsOn neutralUsed deletedPapSourceState.env)
      (envRootsOn neutralUsed deletedPapTargetState.env) := {
    runtime := deletedPapRuntimeRelated
    ledger := by
      simpa [deletedPapTargetState] using
        TargetAllocationLedger.empty emptyAddressRenaming
  }
  related.evalLetValuePapLeftGarbage
    (fvarId := dead) (binderName := dead.name) (type := objType)
    (values := #[.erased]) (target := firstDecl)
    (by
      simp [deletedPapSourceState, deletedPapSourceEnv, evalArgs, evalArg,
        Impure.bind, lookup, papArgVar]
      rfl)
    rfl
    (by simp [firstDecl, decl])

theorem deletedPapSourceOnlyKeepsAllocationLedger :
    deletedPapLedgerResult.runtime.ledger.owner = fun _ => 0 := by
  simp [deletedPapLedgerResult,
    LedgerShadowRuntimeRel.evalLetValuePapLeftGarbage,
    LedgerShadowRuntimeRel.allocLeftGarbage,
    TargetAllocationLedger.empty]

theorem deletedPapHeapResultSourceOnly :
    SourceOnlyUnderTargetLedger
      deletedPapLedgerResult.runtime.ledger 0 :=
  deletedPapLedgerResult.heapSourceOnly 0 (by rfl)

/-- The retained heap-box fixture keeps its live input in the ambient
liveness set and its box result in the continuation. -/
def retainedBoxUsed : UsedLocals :=
  neutralUsed.insert boxInputVar

def retainedBoxDecl : LCNF.LetDecl .impure :=
  letDecl live objType (.box u64Type boxInputVar)

def retainedBoxCode : LCNF.Code .impure :=
  .let retainedBoxDecl (.return live)

theorem retainedBoxShadowRun :
    shadowCode? 2 {} retainedBoxCode =
      some (retainedBoxCode, retainedBoxUsed) := by
  simp [retainedBoxCode, retainedBoxDecl, retainedBoxUsed, neutralUsed,
    letDecl, shadowCode?, safeToElim, collectLetValue, live, boxInputVar]

def retainedBoxExactGraph :
    ExactShadowCodeGraph 2 retainedBoxUsed
      retainedBoxCode retainedBoxCode :=
  ExactShadowCodeGraph.ofResult retainedBoxShadowRun

theorem retainedBoxExactBinderReady :
    ExactShadowCodeBinderReady retainedBoxUsed
      retainedBoxExactGraph.view := by
  apply retainedBoxExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty boxInputVar)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, .uint64⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [retainedBoxCode, retainedBoxDecl, letDecl,
      codeBinderIds, BinderNamesUnique, live, boxInputVar]

theorem retainedBoxStepBinderReady :
    ExactShadowCodeBinderReady retainedBoxUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedBoxDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedBoxDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply ExactShadowCodeView.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact CodeBinderList.ret
  · simp [BinderNamesUnique]
  · simp [BinderAbsenceTransfers]

def retainedBoxEnv : Env :=
  bind [] boxInputVar (.scalar (.uint64 18446744073709551615))

def retainedBoxState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedBoxCode
    env := retainedBoxEnv }

theorem retainedBoxSourceOwnership :
    SourceMachineOwnershipBelowFrontier retainedBoxState := by
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · exact {
      heap := by
        simpa [retainedBoxState] using
          HeapOwnershipBelowFrontier.empty
      env := by
        change EnvironmentBelowFrontier
          ({} : RuntimeState) retainedBoxEnv
        rw [retainedBoxEnv]
        apply EnvironmentBelowFrontier.bind
          (binder := boxInputVar)
          EnvironmentBelowFrontier.empty
        intro location member
        simp at member
    }
  · exact trivial

/-- Compiler-facing retained-box regression: a large `UInt64` payload forces
paired heap allocation and returns the extended target owner ledger. -/
theorem retainedBoxExactStepLedgerPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedBoxState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedBoxState targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedBoxState.program retainedBoxState.program := by
    simpa [retainedBoxState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedBoxState.frames retainedBoxState.frames [] [] := by
    simpa [retainedBoxState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedBoxUsed
        retainedBoxState.joins retainedBoxState.joins := by
    simpa [retainedBoxState] using
      BinderReadyShadowJoinEnvRelated.empty 2 retainedBoxUsed
  have env :
      EnvRelOn emptyAddressRenaming retainedBoxUsed
        retainedBoxState.env retainedBoxState.env := by
    simpa [retainedBoxState, retainedBoxEnv] using
      (EnvRelOn.empty emptyAddressRenaming retainedBoxUsed).bindBoth
        (binder := boxInputVar)
        (ValueRel.scalar (.uint64 18446744073709551615))
  have runtime :
      LedgerShadowRuntimeRel emptyAddressRenaming
        retainedBoxState.runtime retainedBoxState.runtime
        (envRootsOn retainedBoxUsed retainedBoxState.env ++ [])
        (envRootsOn retainedBoxUsed retainedBoxState.env ++ []) := {
    runtime := by
      simpa [retainedBoxState] using
        emptyRuntime_shadowRelated_of_roots (envRootsOn_related env)
    ledger := by
      simpa [retainedBoxState] using
        TargetAllocationLedger.empty emptyAddressRenaming
  }
  have usedBound :
      UsedSubset
        (collectLetValue neutralUsed
          (LCNF.LetValue.box u64Type boxInputVar :
            LCNF.LetValue .impure))
        retainedBoxUsed := by
    simpa [collectLetValue, retainedBoxUsed] using
      UsedSubset.refl retainedBoxUsed
  simpa [retainedBoxState, retainedBoxCode,
    retainedBoxDecl, letDecl] using
    retainedBoxStepBinderReady.match_retainedBoxLetStep_ledger
      (fuelBound := Nat.le_refl 2)
      usedBound retainedBoxState retainedBoxState programs frames joins env
      runtime step

/-- The concrete heap-backed box allocation preserves complete source
ownership alongside the paired non-lockstep relation. -/
theorem retainedBoxExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedBoxState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedBoxState targetAfter ∧
      BinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedBoxState.program retainedBoxState.program := by
    simpa [retainedBoxState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedBoxState.frames retainedBoxState.frames [] [] := by
    simpa [retainedBoxState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedBoxUsed
        retainedBoxState.joins retainedBoxState.joins := by
    simpa [retainedBoxState] using
      BinderReadyShadowJoinEnvRelated.empty 2 retainedBoxUsed
  have env :
      EnvRelOn emptyAddressRenaming retainedBoxUsed
        retainedBoxState.env retainedBoxState.env := by
    simpa [retainedBoxState, retainedBoxEnv] using
      (EnvRelOn.empty emptyAddressRenaming retainedBoxUsed).bindBoth
        (binder := boxInputVar)
        (ValueRel.scalar (.uint64 18446744073709551615))
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        retainedBoxState.runtime retainedBoxState.runtime
        (envRootsOn retainedBoxUsed retainedBoxState.env ++ [])
        (envRootsOn retainedBoxUsed retainedBoxState.env ++ []) := by
    simpa [retainedBoxState] using
      emptyRuntime_shadowRelated_of_roots (envRootsOn_related env)
  have usedBound :
      UsedSubset
        (collectLetValue neutralUsed
          (LCNF.LetValue.box u64Type boxInputVar :
            LCNF.LetValue .impure))
        retainedBoxUsed := by
    simpa [collectLetValue, retainedBoxUsed] using
      UsedSubset.refl retainedBoxUsed
  simpa [retainedBoxState, retainedBoxCode,
    retainedBoxDecl, letDecl] using
    retainedBoxStepBinderReady
      |>.match_retainedBoxLetStep_withOwnership
        (fuelBound := Nat.le_refl 2)
        usedBound retainedBoxState retainedBoxState programs frames joins env
        runtime retainedBoxSourceOwnership step

/-- The deleted large scalar box may allocate one source-only cell while the
target's empty allocation ledger remains unchanged. -/
noncomputable def deletedBoxLedgerResult :
    LedgerBoxLeftGarbageResult emptyAddressRenaming
      deletedBoxSourceState.runtime deletedBoxTargetState.runtime
      (envRootsOn neutralUsed deletedBoxSourceState.env)
      (envRootsOn neutralUsed deletedBoxTargetState.env)
      u64Type (.scalar (.uint64 18446744073709551615)) :=
  let related : LedgerShadowRuntimeRel emptyAddressRenaming
      deletedBoxSourceState.runtime deletedBoxTargetState.runtime
      (envRootsOn neutralUsed deletedBoxSourceState.env)
      (envRootsOn neutralUsed deletedBoxTargetState.env) := {
    runtime := deletedBoxRuntimeRelated
    ledger := by
      simpa [deletedBoxTargetState] using
        TargetAllocationLedger.empty emptyAddressRenaming
  }
  related.boxScalarLeftGarbage u64Type
    (.uint64 18446744073709551615)

theorem deletedBoxSourceOnlyKeepsAllocationLedger :
    deletedBoxLedgerResult.runtime.ledger.owner = fun _ => 0 := by
  simp [deletedBoxLedgerResult,
    LedgerShadowRuntimeRel.boxScalarLeftGarbage,
    LedgerShadowRuntimeRel.allocLeftGarbage,
    ScalarValue.toUInt64, maxTaggedPayload,
    TargetAllocationLedger.empty]

theorem deletedBoxHeapResultSourceOnly :
    SourceOnlyUnderTargetLedger
      deletedBoxLedgerResult.runtime.ledger 0 :=
  deletedBoxLedgerResult.heapSourceOnly 0 (by rfl)

/-- A retained heap reset keeps its token result live.  The concrete object
owns one erased field, so resetting that field exercises the successful
heap-backed branch without introducing another ordinary heap root. -/
def retainedResetDecl : LCNF.LetDecl .impure :=
  letDecl reuseTokenVar objType (.reset 1 resetObjectVar)

def retainedResetCode : LCNF.Code .impure :=
  .let retainedResetDecl (.return reuseTokenVar)

def retainedResetContinuationUsed : UsedLocals :=
  ({} : UsedLocals).insert reuseTokenVar

def retainedResetUsed : UsedLocals :=
  retainedResetContinuationUsed.insert resetObjectVar

theorem retainedResetShadowRun :
    shadowCode? 2 {} retainedResetCode =
      some (retainedResetCode, retainedResetUsed) := by
  simp [retainedResetCode, retainedResetDecl,
    retainedResetContinuationUsed, retainedResetUsed, letDecl,
    shadowCode?, safeToElim, collectLetValue,
    reuseTokenVar, resetObjectVar]

def retainedResetContinuationRun :
    ExactShadowCodeRun 1 {} retainedResetContinuationUsed
      (.return reuseTokenVar) (.return reuseTokenVar) where
  result := by
    simp [shadowCode?, retainedResetContinuationUsed]

theorem retainedResetStepBinderReady :
    ExactShadowCodeBinderReady retainedResetUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedResetDecl)
        retainedResetContinuationRun
        (Or.inl (by
          simp [retainedResetDecl, letDecl,
            retainedResetContinuationUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply ExactShadowCodeView.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty
        reuseTokenVar)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact CodeBinderList.ret
  · simp [BinderNamesUnique]
  · simp [BinderAbsenceTransfers]

def retainedResetEnv : Env :=
  bind [] resetObjectVar (.object (.heap 0))

def retainedResetState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedResetCode
    env := retainedResetEnv
    runtime := deletedWriteSourceRuntime }

theorem retainedResetSourceOwnership :
    SourceMachineOwnershipBelowFrontier retainedResetState := by
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · constructor
    · simpa [retainedResetState, deletedWriteSourceRuntime, alloc] using
        (HeapOwnershipBelowFrontier.empty.alloc
          (object := .ctor deletedWriteObject)
          (by
            simp [HeapObject.ownedValues, deletedWriteObject])
          false)
    · have objectBelow :
          HeapLocationsBelowFrontier deletedWriteSourceRuntime
            [.object (.heap 0)] := by
        intro location member
        have locationEq : location = 0 := by
          simpa using member
        subst location
        simp [deletedWriteSourceRuntime, alloc]
      change EnvironmentBelowFrontier
        deletedWriteSourceRuntime retainedResetEnv
      intro fvarId value found
      unfold retainedResetEnv Fir.LeanIR.Impure.bind at found
      simp only [lookup] at found
      split at found
      · have valueEq := Option.some.inj found
        subst value
        exact @objectBelow
      · simp at found
  · exact trivial

/-- Exact retained-reset regression: both sides clear the paired constructor,
bind related concrete reuse tokens, and preserve complete source ownership. -/
theorem retainedResetExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedResetState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedResetState targetAfter ∧
      BinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have objects :
      HeapObjectRel emptyAddressRenaming
        (.ctor deletedWriteObject) (.ctor deletedWriteObject) := by
    apply HeapObjectRel.ctor
    · rfl
    · change ListRel (ValueRel emptyAddressRenaming)
        [.erased] [.erased]
      exact .cons .erased .nil
    · rfl
    · rfl
  let base : LedgerShadowRuntimeRel emptyAddressRenaming
      ({} : RuntimeState) ({} : RuntimeState) [.erased] [.erased] := {
    runtime :=
      emptyRuntime_shadowRelated_of_roots
        (ListRel.cons ValueRel.erased ListRel.nil)
    ledger := TargetAllocationLedger.empty emptyAddressRenaming
  }
  let paired := base.allocBoth
      objects
      (by
        intro value member
        apply extra_subset_runtimeRoots
        simpa [HeapObject.ownedValues, deletedWriteObject] using member)
      (by
        intro value member
        apply extra_subset_runtimeRoots
        simpa [HeapObject.ownedValues, deletedWriteObject] using member)
      false
  have objectValues :
      ValueRel paired.larger
        (.object (.heap 0)) (.object (.heap 0)) := by
    simpa [alloc] using paired.values
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedResetState.program retainedResetState.program := by
    simpa [retainedResetState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 paired.larger
        retainedResetState.frames retainedResetState.frames [] [] := by
    simpa [retainedResetState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 paired.larger
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedResetUsed
        retainedResetState.joins retainedResetState.joins := by
    simpa [retainedResetState] using
      BinderReadyShadowJoinEnvRelated.empty 2 retainedResetUsed
  have env :
      EnvRelOn paired.larger retainedResetUsed
        retainedResetState.env retainedResetState.env := by
    simpa [retainedResetState, retainedResetEnv] using
      (EnvRelOn.empty paired.larger retainedResetUsed).bindBoth
        (binder := resetObjectVar) objectValues
  have runtime :
      ShadowRuntimeRel paired.larger
        retainedResetState.runtime retainedResetState.runtime
        (envRootsOn retainedResetUsed retainedResetState.env ++ [])
        (envRootsOn retainedResetUsed retainedResetState.env ++ []) := by
    have rootsSubset : RootSubset
        (envRootsOn retainedResetUsed retainedResetState.env)
        [.object (.heap 0), .erased] := by
      intro value member
      have valueEq : value = .object (.heap 0) := by
        symm
        simpa [retainedResetState, retainedResetEnv,
          retainedResetUsed, retainedResetContinuationUsed,
          envRootsOn, Impure.bind, lookup, reuseTokenVar,
          resetObjectVar] using member
      subst value
      simp
    have restricted :=
      paired.runtime.runtime.restrictExtra
        (envRootsOn_related env) rootsSubset rootsSubset
    simpa [retainedResetState, deletedWriteSourceRuntime,
      List.append_nil] using restricted
  have usedBound :
      UsedSubset
        (collectLetValue retainedResetContinuationUsed
          (LCNF.LetValue.reset 1 resetObjectVar :
            LCNF.LetValue .impure))
        retainedResetUsed := by
    simpa [collectLetValue, retainedResetUsed] using
      UsedSubset.refl retainedResetUsed
  rcases
      retainedResetStepBinderReady
        |>.match_retainedResetLetStep_withOwnership
          (fuelBound := Nat.le_refl 2) usedBound
          retainedResetState retainedResetState programs frames joins env
          runtime retainedResetSourceOwnership step with
    ⟨targetAfter, path, related, ownership⟩
  exact ⟨paired.larger, targetAfter, paired.extension,
    by
      simpa [retainedResetState, retainedResetCode,
        retainedResetDecl, letDecl] using path,
    related, ownership⟩

/-- A retained failed reuse keeps the token live in the ambient set and uses
its result in the continuation. -/
def retainedReuseNoneUsed : UsedLocals :=
  neutralUsed.insert reuseTokenVar

def retainedReuseNoneDecl : LCNF.LetDecl .impure :=
  letDecl live objType
    (.reuse reuseTokenVar oneFieldInfo true #[.erased])

def retainedReuseNoneCode : LCNF.Code .impure :=
  .let retainedReuseNoneDecl (.return live)

theorem retainedReuseNoneShadowRun :
    shadowCode? 2 {} retainedReuseNoneCode =
      some (retainedReuseNoneCode, retainedReuseNoneUsed) := by
  simp [retainedReuseNoneCode, retainedReuseNoneDecl,
    retainedReuseNoneUsed, neutralUsed, letDecl, shadowCode?, safeToElim,
    collectLetValue, collectArgs, collectArgList, collectArg, live,
    reuseTokenVar]

def retainedReuseNoneExactGraph :
    ExactShadowCodeGraph 2 retainedReuseNoneUsed
      retainedReuseNoneCode retainedReuseNoneCode :=
  ExactShadowCodeGraph.ofResult retainedReuseNoneShadowRun

theorem retainedReuseNoneExactBinderReady :
    ExactShadowCodeBinderReady retainedReuseNoneUsed
      retainedReuseNoneExactGraph.view := by
  apply retainedReuseNoneExactGraph.binderReady_of_canonical
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty reuseTokenVar)
  · apply ScopedCodeWellFormedTree.letE
    · native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · apply freshForScope_of_not_contains
      native_decide
    · exact ⟨.object, trivial⟩
    · apply ScopedCodeWellFormedTree.ret
      native_decide
  · simp [retainedReuseNoneCode, retainedReuseNoneDecl, letDecl,
      codeBinderIds, BinderNamesUnique, live, reuseTokenVar]

theorem retainedReuseNoneStepBinderReady :
    ExactShadowCodeBinderReady retainedReuseNoneUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedReuseNoneDecl)
        retainedLargeNatContinuationRun
        (Or.inl (by
          simp [retainedReuseNoneDecl, letDecl, neutralUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply ExactShadowCodeView.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact CodeBinderList.ret
  · simp [BinderNamesUnique]
  · simp [BinderAbsenceTransfers]

def retainedReuseNoneEnv : Env :=
  bind [] reuseTokenVar (.reuseToken none)

def retainedReuseNoneState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedReuseNoneCode
    env := retainedReuseNoneEnv }

/-- Compiler-facing retained failed-reuse regression: constructor allocation
on both sides returns the proof-relevant paired owner ledger. -/
theorem retainedReuseNoneExactStepLedgerPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedReuseNoneState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedReuseNoneState targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedReuseNoneState.program retainedReuseNoneState.program := by
    simpa [retainedReuseNoneState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedReuseNoneState.frames retainedReuseNoneState.frames [] [] := by
    simpa [retainedReuseNoneState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedReuseNoneUsed
        retainedReuseNoneState.joins retainedReuseNoneState.joins := by
    simpa [retainedReuseNoneState] using
      BinderReadyShadowJoinEnvRelated.empty 2 retainedReuseNoneUsed
  have env :
      EnvRelOn emptyAddressRenaming retainedReuseNoneUsed
        retainedReuseNoneState.env retainedReuseNoneState.env := by
    simpa [retainedReuseNoneState, retainedReuseNoneEnv] using
      (EnvRelOn.empty emptyAddressRenaming retainedReuseNoneUsed).bindBoth
        (binder := reuseTokenVar) ValueRel.reuseNone
  have runtime :
      LedgerShadowRuntimeRel emptyAddressRenaming
        retainedReuseNoneState.runtime retainedReuseNoneState.runtime
        (envRootsOn retainedReuseNoneUsed retainedReuseNoneState.env ++ [])
        (envRootsOn retainedReuseNoneUsed retainedReuseNoneState.env ++ []) := {
    runtime := by
      simpa [retainedReuseNoneState] using
        emptyRuntime_shadowRelated_of_roots (envRootsOn_related env)
    ledger := by
      simpa [retainedReuseNoneState] using
        TargetAllocationLedger.empty emptyAddressRenaming
  }
  have tokenRead :
      lookupValue retainedReuseNoneState.env reuseTokenVar =
        .ok (.reuseToken none) := by
    simp [retainedReuseNoneState, retainedReuseNoneEnv,
      lookupValue, Impure.bind, lookup, reuseTokenVar]
  have argumentsRead :
      evalArgs retainedReuseNoneState.env #[.erased] =
        .ok #[.erased] := by
    simp [evalArgs, evalArg]
    rfl
  have usedBound :
      UsedSubset
        (collectLetValue neutralUsed
          (LCNF.LetValue.reuse reuseTokenVar oneFieldInfo true #[.erased] :
            LCNF.LetValue .impure))
        retainedReuseNoneUsed := by
    simpa [collectLetValue, collectArgs, collectArgList, collectArg,
      retainedReuseNoneUsed] using
      UsedSubset.refl retainedReuseNoneUsed
  simpa [retainedReuseNoneState, retainedReuseNoneCode,
    retainedReuseNoneDecl, letDecl] using
    retainedReuseNoneStepBinderReady.match_retainedReuseNoneLetStep_ledger
      (fuelBound := Nat.le_refl 2) usedBound
      retainedReuseNoneState retainedReuseNoneState programs frames joins env
      tokenRead argumentsRead (by rfl) runtime step

/-- The retained missing-token state has no ordinary heap addresses before
reuse allocates its result. -/
theorem retainedReuseNoneSourceOwnership :
    SourceMachineOwnershipBelowFrontier retainedReuseNoneState := by
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · constructor
    · simpa [retainedReuseNoneState] using
        HeapOwnershipBelowFrontier.empty
    · have tokenBelow :
          HeapLocationsBelowFrontier ({} : RuntimeState)
            [.reuseToken none] := by
        intro location member
        simp at member
      have extended :
          EnvironmentBelowFrontier ({} : RuntimeState)
            (bind [] reuseTokenVar (.reuseToken none)) :=
        EnvironmentBelowFrontier.bind
          (binder := reuseTokenVar) (value := .reuseToken none)
          EnvironmentBelowFrontier.empty tokenBelow
      intro fvarId value found
      apply @extended fvarId value
      simpa [retainedReuseNoneState, retainedReuseNoneEnv] using found
  · exact trivial

/-- Exact retained failed-reuse regression: the fallback constructor
allocation extends the paired address map and preserves complete ownership. -/
theorem retainedReuseNoneExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedReuseNoneState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedReuseNoneState targetAfter ∧
      BinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedReuseNoneState.program retainedReuseNoneState.program := by
    simpa [retainedReuseNoneState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        retainedReuseNoneState.frames retainedReuseNoneState.frames [] [] := by
    simpa [retainedReuseNoneState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 emptyAddressRenaming
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedReuseNoneUsed
        retainedReuseNoneState.joins retainedReuseNoneState.joins := by
    simpa [retainedReuseNoneState] using
      BinderReadyShadowJoinEnvRelated.empty 2 retainedReuseNoneUsed
  have env :
      EnvRelOn emptyAddressRenaming retainedReuseNoneUsed
        retainedReuseNoneState.env retainedReuseNoneState.env := by
    simpa [retainedReuseNoneState, retainedReuseNoneEnv] using
      (EnvRelOn.empty emptyAddressRenaming retainedReuseNoneUsed).bindBoth
        (binder := reuseTokenVar) ValueRel.reuseNone
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        retainedReuseNoneState.runtime retainedReuseNoneState.runtime
        (envRootsOn retainedReuseNoneUsed retainedReuseNoneState.env ++ [])
        (envRootsOn retainedReuseNoneUsed retainedReuseNoneState.env ++ []) := by
    simpa [retainedReuseNoneState] using
      emptyRuntime_shadowRelated_of_roots (envRootsOn_related env)
  have retainedReady :
      RetainedLetReadyAt retainedReuseNoneState
        (runtimeRoots retainedReuseNoneState.runtime
          (envRootsOn retainedReuseNoneUsed retainedReuseNoneState.env ++ []))
        (.reuse reuseTokenVar oneFieldInfo true #[.erased]) := by
    intro location tokenRead
    simp [retainedReuseNoneState, retainedReuseNoneEnv,
      lookupValue, Impure.bind, lookup, reuseTokenVar] at tokenRead
  have usedBound :
      UsedSubset
        (collectLetValue neutralUsed
          (LCNF.LetValue.reuse reuseTokenVar oneFieldInfo true #[.erased] :
            LCNF.LetValue .impure))
        retainedReuseNoneUsed := by
    simpa [collectLetValue, collectArgs, collectArgList, collectArg,
      retainedReuseNoneUsed] using
      UsedSubset.refl retainedReuseNoneUsed
  simpa [retainedReuseNoneState, retainedReuseNoneCode,
    retainedReuseNoneDecl, letDecl] using
    retainedReuseNoneStepBinderReady
      |>.match_retainedReuseLetStep_withOwnership
        (fuelBound := Nat.le_refl 2) usedBound
        retainedReuseNoneState retainedReuseNoneState programs frames joins
        env retainedReady runtime retainedReuseNoneSourceOwnership step

/-- The deleted failed-reuse fixture's source-only constructor allocation
retains the empty target owner ledger. -/
noncomputable def deletedReuseNoneLedgerResult :
    LedgerReuseNoneLeftGarbageResult emptyAddressRenaming
      deletedReuseNoneSourceState.runtime deletedReuseTargetState.runtime
      (envRootsOn neutralUsed deletedReuseNoneSourceState.env)
      (envRootsOn neutralUsed deletedReuseTargetState.env)
      oneFieldInfo true #[.erased] :=
  let related : LedgerShadowRuntimeRel emptyAddressRenaming
      deletedReuseNoneSourceState.runtime deletedReuseTargetState.runtime
      (envRootsOn neutralUsed deletedReuseNoneSourceState.env)
      (envRootsOn neutralUsed deletedReuseTargetState.env) := {
    runtime := deletedReuseNoneRuntimeRelated
    ledger := by
      simpa [deletedReuseTargetState] using
        TargetAllocationLedger.empty emptyAddressRenaming
  }
  related.reuseNoneLeftGarbage oneFieldInfo #[.erased] (by rfl) true

/-- The failed-token fixture's complete source environment is bounded even
though its erased reuse argument is dead in the target continuation. -/
theorem deletedReuseNoneSourceEnvironmentOwnershipBelowFrontier :
    SourceEnvironmentOwnershipBelowFrontier
      deletedReuseNoneSourceState := by
  have erasedBelow :
      HeapLocationsBelowFrontier ({} : RuntimeState) [.erased] := by
    intro location member
    simp at member
  have tokenBelow :
      HeapLocationsBelowFrontier ({} : RuntimeState)
        [.reuseToken none] := by
    intro location member
    simp at member
  have emptyEnv :
      EnvironmentBelowFrontier ({} : RuntimeState) [] :=
    EnvironmentBelowFrontier.empty
  have liveEnvBound :
      EnvironmentBelowFrontier ({} : RuntimeState) liveEnv := by
    have extended :
        EnvironmentBelowFrontier ({} : RuntimeState)
          (bind [] live .erased) :=
      EnvironmentBelowFrontier.bind
        (binder := live) (value := .erased)
        emptyEnv erasedBelow
    intro fvarId value found
    apply @extended fvarId value
    simpa [liveEnv] using found
  have tokenEnvBound :
      EnvironmentBelowFrontier ({} : RuntimeState)
        (bind liveEnv reuseTokenVar (.reuseToken none)) :=
    EnvironmentBelowFrontier.bind
      (binder := reuseTokenVar) (value := .reuseToken none)
      liveEnvBound tokenBelow
  have sourceEnvBound :
      EnvironmentBelowFrontier
        deletedReuseNoneSourceState.runtime
        deletedReuseNoneSourceState.env := by
    have extended :
        EnvironmentBelowFrontier ({} : RuntimeState)
          (bind
            (bind liveEnv reuseTokenVar (.reuseToken none))
            reuseArgVar .erased) :=
      EnvironmentBelowFrontier.bind
        (binder := reuseArgVar) (value := .erased)
        tokenEnvBound erasedBelow
    intro fvarId value found
    apply @extended fvarId value
    simpa [deletedReuseNoneSourceState,
      deletedReuseNoneSourceEnv] using found
  let bounded :
      SourceEnvironmentOwnershipBelowFrontier
        deletedReuseNoneSourceState := {
    heap := by
      simpa [deletedReuseNoneSourceState] using
        HeapOwnershipBelowFrontier.empty
    env := sourceEnvBound
  }
  exact bounded

/-- The ownership-strengthened active-code matcher carries the complete source
machine invariant across the failed-token reuse allocation and dead result
binding while the target stutters at its retained continuation. -/
theorem deletedReuseNoneExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedReuseNoneSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedReuseTargetState targetAfter ∧
      BinderReadyReachableMachineRelated 2 emptyAddressRenaming
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        deletedReuseNoneSourceState.program
        deletedReuseTargetState.program := by
    simpa [deletedReuseNoneSourceState, deletedReuseTargetState] using
      deletedReuseSomeProgramBinderReadyRelated
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        deletedReuseNoneSourceState.frames
        deletedReuseTargetState.frames [] [] := by
    exact .nil
  have continuation :
      BinderReadyShadowCodeGraph 2 neutralUsed
        (.return live) (.return live) := by
    apply retainedLargeNatContinuationRun.toBinderReadyShadowCodeGraphAt
    · omega
    · exact UsedSubset.refl neutralUsed
    · apply
        retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
        (index :=
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
            Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
      · apply ScopedCodeWellFormedTree.ret
        native_decide
      · simp [codeBinderIds, BinderNamesUnique]
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        deletedReuseNoneSourceState.joins
        deletedReuseTargetState.joins :=
    BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        deletedReuseNoneSourceState.env deletedReuseTargetState.env := by
    simpa [deletedReuseNoneSourceState, deletedReuseTargetState] using
      deletedReuseNoneEnvReachableRelated
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        deletedReuseNoneSourceState.runtime
        deletedReuseTargetState.runtime
        (envRootsOn neutralUsed deletedReuseNoneSourceState.env ++ [])
        (envRootsOn neutralUsed deletedReuseTargetState.env ++ []) := by
    simpa using deletedReuseNoneRuntimeRelated
  have ownership :
      SourceMachineOwnershipBelowFrontier
        deletedReuseNoneSourceState :=
    SourceMachineOwnershipBelowFrontier.ofEnvironment
      deletedReuseNoneSourceEnvironmentOwnershipBelowFrontier
      (by trivial)
  simpa [deletedReuseNoneSourceState, deletedReuseTargetState,
    deletedReuseBefore, deletedReuseAfter, deadReuseDecl, letDecl] using
    (match_deletedReuseStep_binderReady_withOwnership
      (sourceState := deletedReuseNoneSourceState)
      (targetState := deletedReuseTargetState)
      (sourceContinuation := .return live)
      (targetContinuation := .return live)
      (fvarId := dead)
      (binderName := dead.name)
      (type := objType)
      (token := reuseTokenVar)
      (info := oneFieldInfo)
      (updateHeader := true)
      (arguments := #[.fvar reuseArgVar])
      programs frames continuation joins env (by native_decide)
      runtime (by simpa using deletedReuseNoneReady) ownership step)

/-- The failed-token fixture exercises the complete-environment bridge. Its
dead source operand suffices to preserve heap ownership across the allocation
fallback without widening target continuation liveness. -/
theorem deletedReuseNoneOwnershipBelowFrontier :
    HeapOwnershipBelowFrontier
      deletedReuseNoneLedgerResult.nextRuntime := by
  apply
    deletedReuseNoneSourceEnvironmentOwnershipBelowFrontier.reuseHeap
      (argumentExprs := #[.fvar reuseArgVar])
      (arguments := #[.erased])
      (tokenLocation := none)
      (info := oneFieldInfo)
      (updateHeader := true)
  · simp [deletedReuseNoneSourceState, deletedReuseNoneSourceEnv,
      evalArgs, evalArg, Impure.bind, lookup, reuseTokenVar, reuseArgVar]
    rfl
  · exact deletedReuseNoneLedgerResult.effect

/-- The same fixture crosses the next non-leaf boundary: after the deleted
reuse allocates, its returned heap value is bound under the dead source local
and execution proceeds into the retained continuation with the complete
environment/heap carrier intact. -/
theorem deletedReuseNoneBoundContinuationOwnershipBelowFrontier :
    SourceEnvironmentOwnershipBelowFrontier
      { deletedReuseNoneSourceState with
        runtime := deletedReuseNoneLedgerResult.nextRuntime
        env := bind deletedReuseNoneSourceState.env dead
          deletedReuseNoneLedgerResult.value
        control := .code (.return live) } := by
  have next :=
    deletedReuseNoneSourceEnvironmentOwnershipBelowFrontier.reuseState
      (binder := dead)
      (argumentExprs := #[.fvar reuseArgVar])
      (arguments := #[.erased])
      (tokenLocation := none)
      (info := oneFieldInfo)
      (updateHeader := true)
      (by
        simp [deletedReuseNoneSourceState, deletedReuseNoneSourceEnv,
          evalArgs, evalArg, Impure.bind, lookup,
          reuseTokenVar, reuseArgVar]
        rfl)
      deletedReuseNoneLedgerResult.effect
  constructor
  · exact next.heap
  · exact @next.env

/-- A yielded bind-frame state over the source-only failed-reuse heap. The
saved source environment deliberately contains locals absent from the target
continuation's liveness set. -/
noncomputable def deletedReuseYieldedBindSourceState : MachineState :=
  { deletedReuseNoneSourceState with
    runtime := deletedReuseNoneLedgerResult.nextRuntime
    control := .yielded .erased
    frames := [
      .bind dead (.return live) deletedReuseNoneSourceState.env []] }

def deletedReuseYieldedBindTargetState : MachineState :=
  { deletedReuseTargetState with
    control := .yielded .erased
    frames := [
      .bind dead (.return live) deletedReuseTargetState.env []] }

noncomputable def deletedReuseYieldedBindSourceAfter : MachineState :=
  { deletedReuseNoneSourceState with
    runtime := deletedReuseNoneLedgerResult.nextRuntime
    control := .code (.return live)
    env := bind deletedReuseNoneSourceState.env dead .erased
    joins := []
    frames := [] }

def deletedReuseYieldedBindTargetAfter : MachineState :=
  { deletedReuseTargetState with
    control := .code (.return live)
    env := bind deletedReuseTargetState.env dead .erased
    joins := []
    frames := [] }

/-- Exact bind-frame restoration now preserves both hereditary compiler
provenance and the complete source machine ownership carrier. This fixture
keeps the earlier source-only allocation in the heap while restoring a saved
environment containing target-dead locals. -/
theorem deletedReuseYieldedBindOwnershipPreserved :
    coreStep deletedReuseYieldedBindSourceState =
        .next deletedReuseYieldedBindSourceAfter ∧
      coreStep deletedReuseYieldedBindTargetState =
        .next deletedReuseYieldedBindTargetAfter ∧
      BinderReadyReachableMachineRelated 2 emptyAddressRenaming
        deletedReuseYieldedBindSourceAfter
        deletedReuseYieldedBindTargetAfter ∧
      SourceMachineOwnershipBelowFrontier
        deletedReuseYieldedBindSourceAfter := by
  have continuation :
      BinderReadyShadowCodeGraph 2 neutralUsed
        (.return live) (.return live) := by
    apply
      retainedLargeNatContinuationRun.toBinderReadyShadowCodeGraphAt
    · omega
    · exact UsedSubset.refl neutralUsed
    · apply
        retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
        (index :=
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
            Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
      · apply ScopedCodeWellFormedTree.ret
        native_decide
      · simp [codeBinderIds, BinderNamesUnique]
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        [] [] [] [] :=
    BinderReadyReachableFramesRelated.nil
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed [] [] :=
    BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        deletedReuseNoneLedgerResult.nextRuntime
        deletedReuseTargetState.runtime
        ([.erased] ++
          (envRootsOn neutralUsed deletedReuseNoneSourceState.env ++ []))
        ([.erased] ++
          (envRootsOn neutralUsed deletedReuseTargetState.env ++ [])) := by
    simpa using
      deletedReuseNoneLedgerResult.runtime.runtime.prependErased
  have resultBound :=
    deletedReuseNoneSourceEnvironmentOwnershipBelowFrontier.heap
      |>.reuseResultBelowFrontier
        deletedReuseNoneLedgerResult.effect
  have sourceEnvBound :
      EnvironmentBelowFrontier
        deletedReuseNoneLedgerResult.nextRuntime
        deletedReuseNoneSourceState.env := by
    exact EnvironmentBelowFrontier.monoFrontier
      (before := deletedReuseNoneSourceState.runtime)
      (after := deletedReuseNoneLedgerResult.nextRuntime)
      (env := deletedReuseNoneSourceState.env)
      deletedReuseNoneSourceEnvironmentOwnershipBelowFrontier.env
      resultBound.frontier
  have ownership :
      SourceMachineOwnershipBelowFrontier
        deletedReuseYieldedBindSourceState := by
    refine {
      heap := deletedReuseNoneOwnershipBelowFrontier
      env := ?_
      frames := ?_
    }
    · change EnvironmentBelowFrontier
        deletedReuseNoneLedgerResult.nextRuntime
        deletedReuseNoneSourceState.env
      exact sourceEnvBound
    · change
        EnvironmentBelowFrontier
            deletedReuseNoneLedgerResult.nextRuntime
            deletedReuseNoneSourceState.env ∧
          True
      exact And.intro sourceEnvBound True.intro
  simpa [deletedReuseYieldedBindSourceState,
    deletedReuseYieldedBindTargetState,
    deletedReuseYieldedBindSourceAfter,
    deletedReuseYieldedBindTargetAfter,
    deletedReuseNoneSourceState,
    deletedReuseTargetState] using
    (coreStep_yieldedBind_binderReadyReachableRelated_withOwnership
      (binder := dead)
      (sourceState :=
        { deletedReuseNoneSourceState with
          runtime := deletedReuseNoneLedgerResult.nextRuntime })
      (targetState := deletedReuseTargetState)
      deletedReuseSomeProgramBinderReadyRelated frames continuation
      joins deletedReuseNoneEnvReachableRelated ValueRel.erased
      runtime ownership)

/-- Cache restoration over the same source-only heap persists and publishes
the yielded value without allocating or disturbing complete source bounds. -/
noncomputable def deletedReuseYieldedCacheSourceState : MachineState :=
  { deletedReuseNoneSourceState with
    runtime := deletedReuseNoneLedgerResult.nextRuntime
    control := .yielded .erased
    frames := [.cache `main] }

def deletedReuseYieldedCacheTargetState : MachineState :=
  { deletedReuseTargetState with
    control := .yielded .erased
    frames := [.cache `main] }

noncomputable def deletedReuseYieldedCacheSourceAfter : MachineState :=
  { deletedReuseNoneSourceState with
    runtime :=
      deletedReuseNoneLedgerResult.nextRuntime.setGlobal `main .erased
    control := .yielded .erased
    frames := [] }

def deletedReuseYieldedCacheTargetAfter : MachineState :=
  { deletedReuseTargetState with
    runtime := deletedReuseTargetState.runtime.setGlobal `main .erased
    control := .yielded .erased
    frames := [] }

/-- Exact cache-frame restoration keeps hereditary compiler provenance and
the complete source machine ownership carrier across persistence/global
installation, even when the source heap contains compiler-only garbage. -/
theorem deletedReuseYieldedCacheOwnershipPreserved :
    coreStep deletedReuseYieldedCacheSourceState =
        .next deletedReuseYieldedCacheSourceAfter ∧
      coreStep deletedReuseYieldedCacheTargetState =
        .next deletedReuseYieldedCacheTargetAfter ∧
      BinderReadyReachableMachineRelated 2 emptyAddressRenaming
        deletedReuseYieldedCacheSourceAfter
        deletedReuseYieldedCacheTargetAfter ∧
      SourceMachineOwnershipBelowFrontier
        deletedReuseYieldedCacheSourceAfter := by
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        [] [] [] [] :=
    BinderReadyReachableFramesRelated.nil
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        deletedReuseNoneLedgerResult.nextRuntime
        deletedReuseTargetState.runtime
        [.erased] [.erased] := by
    apply
      deletedReuseNoneLedgerResult.runtime.runtime.prependErased.restrictExtra
        (.cons ValueRel.erased .nil)
    · intro value member
      simp only [List.mem_singleton] at member
      subst value
      simp
    · intro value member
      simp only [List.mem_singleton] at member
      subst value
      simp
  have resultBound :=
    deletedReuseNoneSourceEnvironmentOwnershipBelowFrontier.heap
      |>.reuseResultBelowFrontier
        deletedReuseNoneLedgerResult.effect
  have sourceEnvBound :
      EnvironmentBelowFrontier
        deletedReuseNoneLedgerResult.nextRuntime
        deletedReuseNoneSourceState.env := by
    exact EnvironmentBelowFrontier.monoFrontier
      (before := deletedReuseNoneSourceState.runtime)
      (after := deletedReuseNoneLedgerResult.nextRuntime)
      (env := deletedReuseNoneSourceState.env)
      deletedReuseNoneSourceEnvironmentOwnershipBelowFrontier.env
      resultBound.frontier
  have ownership :
      SourceMachineOwnershipBelowFrontier
        deletedReuseYieldedCacheSourceState := by
    refine {
      heap := deletedReuseNoneOwnershipBelowFrontier
      env := ?_
      frames := ?_
    }
    · change EnvironmentBelowFrontier
        deletedReuseNoneLedgerResult.nextRuntime
        deletedReuseNoneSourceState.env
      exact sourceEnvBound
    · trivial
  simpa [deletedReuseYieldedCacheSourceState,
    deletedReuseYieldedCacheTargetState,
    deletedReuseYieldedCacheSourceAfter,
    deletedReuseYieldedCacheTargetAfter,
    deletedReuseNoneSourceState,
    deletedReuseTargetState] using
    (coreStep_yieldedCache_binderReadyReachableRelated_withOwnership
      (name := `main)
      (sourceState :=
        { deletedReuseNoneSourceState with
          runtime := deletedReuseNoneLedgerResult.nextRuntime })
      (targetState := deletedReuseTargetState)
      deletedReuseSomeProgramBinderReadyRelated frames ValueRel.erased
      runtime ownership)

/-- The deleted-write fixture starts from the same ownership invariant: its
single constructor cell owns only the erased value. -/
theorem deletedWriteSourceOwnershipBelowFrontier :
    HeapOwnershipBelowFrontier deletedWriteSourceRuntime := by
  change HeapOwnershipBelowFrontier
    (alloc ({} : RuntimeState) (.ctor deletedWriteObject) false).1
  apply HeapOwnershipBelowFrontier.empty.alloc
  intro child member
  simp [deletedWriteObject, HeapObject.ownedValues] at member

/-- The deleted object write exercises the complete-environment single
argument bridge; the erased field introduces no future address and the
existing cell update therefore retains the ownership invariant. -/
theorem deletedObjectWritePreservesOwnershipBelowFrontier
    (effect :
      setObjectField deletedWriteSourceRuntime
          (.object (.heap 0)) 0 .erased =
        .ok result) :
    HeapOwnershipBelowFrontier result := by
  have erasedBelow :
      HeapLocationsBelowFrontier
        deletedWriteSourceRuntime [.erased] := by
    intro location member
    simp at member
  have objectBelow :
      HeapLocationsBelowFrontier deletedWriteSourceRuntime
        [.object (.heap 0)] := by
    intro location member
    simp at member
    subst location
    simp [deletedWriteSourceRuntime, alloc]
  have usizeBelow :
      HeapLocationsBelowFrontier deletedWriteSourceRuntime
        [.usize 7] := by
    intro location member
    simp at member
  have scalarBelow :
      HeapLocationsBelowFrontier deletedWriteSourceRuntime
        [.scalar (.uint8 9)] := by
    intro location member
    simp at member
  have emptyEnv :
      EnvironmentBelowFrontier deletedWriteSourceRuntime [] :=
    EnvironmentBelowFrontier.empty
  have liveBound :
      EnvironmentBelowFrontier deletedWriteSourceRuntime
        (bind [] live .erased) :=
    EnvironmentBelowFrontier.bind
      (binder := live) (value := .erased)
      emptyEnv erasedBelow
  have objectBound :
      EnvironmentBelowFrontier deletedWriteSourceRuntime
        (bind (bind [] live .erased) dead (.object (.heap 0))) :=
    EnvironmentBelowFrontier.bind
      (binder := dead) (value := .object (.heap 0))
      liveBound objectBelow
  have usizeBound :
      EnvironmentBelowFrontier deletedWriteSourceRuntime
        (bind
          (bind (bind [] live .erased) dead (.object (.heap 0)))
          usizeField (.usize 7)) :=
    EnvironmentBelowFrontier.bind
      (binder := usizeField) (value := .usize 7)
      objectBound usizeBelow
  have extended :
      EnvironmentBelowFrontier deletedWriteSourceRuntime
        (bind
          (bind
            (bind (bind [] live .erased) dead (.object (.heap 0)))
            usizeField (.usize 7))
          scalarField (.scalar (.uint8 9))) :=
    EnvironmentBelowFrontier.bind
      (binder := scalarField) (value := .scalar (.uint8 9))
      usizeBound scalarBelow
  have envBound :
      EnvironmentBelowFrontier deletedWriteSourceRuntime
        deletedWriteSourceEnv := by
    intro fvarId value found
    apply @extended fvarId value
    simpa [deletedWriteSourceEnv, liveEnv] using found
  let bounded :
      SourceEnvironmentOwnershipBelowFrontier
        deletedObjectSetSourceState := {
    heap := by
      simpa [deletedObjectSetSourceState] using
        deletedWriteSourceOwnershipBelowFrontier
    env := by
      intro fvarId value found
      apply @envBound fvarId value
      simpa [deletedObjectSetSourceState] using found
  }
  exact
    (bounded.setObjectFieldState
      (fieldArgument := .erased) rfl effect).heap

theorem deletedReuseNoneSourceOnlyKeepsAllocationLedger :
    deletedReuseNoneLedgerResult.runtime.ledger.owner = fun _ => 0 := by
  simp [deletedReuseNoneLedgerResult,
    LedgerShadowRuntimeRel.reuseNoneLeftGarbage,
    LedgerShadowRuntimeRel.allocCtorLeftGarbage,
    LedgerShadowRuntimeRel.allocLeftGarbage,
    TargetAllocationLedger.empty, oneFieldInfo]

/-- The deleted failed-reuse result now exposes the stronger fact needed by
later concrete reuse: its heap result is outside the target owner ledger. -/
theorem deletedReuseNoneHeapResultSourceOnly :
    SourceOnlyUnderTargetLedger
      deletedReuseNoneLedgerResult.runtime.ledger 0 :=
  deletedReuseNoneLedgerResult.heapSourceOnly 0 (by rfl)

/-- A deleted constructor allocation followed by an unrelated retained
paired allocation is the minimal non-lockstep ownership lifecycle. -/
noncomputable def deletedCtorLifecycleSourceOnly :=
  LedgerShadowRuntimeRel.empty.allocCtorLeftGarbage
    oneFieldInfo #[.erased] (by rfl)

noncomputable def deletedCtorLifecyclePaired :=
  deletedCtorLifecycleSourceOnly.runtime.allocBoth
    (HeapObjectRel.natural 9223372036854775808)
    (by simp [RootSubset, HeapObject.ownedValues])
    (by simp [RootSubset, HeapObject.ownedValues])
    false

/-- The later retained allocation adds a target owner without claiming the
earlier deleted constructor's source address. -/
theorem deletedCtorSourceOnlySurvivesPairedAllocation :
    SourceOnlyUnderTargetLedger
      deletedCtorLifecyclePaired.runtime.ledger 0 := by
  apply deletedCtorLifecyclePaired.sourceOnly_of_found
    deletedCtorLifecycleSourceOnly.runtime
  · exact deletedCtorLifecycleSourceOnly.heapSourceOnly 0 (by rfl)
  · rfl

/-- The source runtime produced by the deleted constructor allocation
satisfies the reusable ownership bound at its new frontier. -/
theorem deletedCtorLifecycleSourceOwnershipBelowFrontier :
    HeapOwnershipBelowFrontier
      deletedCtorLifecycleSourceOnly.nextRuntime := by
  change HeapOwnershipBelowFrontier
    (alloc ({} : RuntimeState)
      (.ctor {
        tag := oneFieldInfo.cidx
        objectFields := #[.erased]
        usizeFields := Array.replicate oneFieldInfo.usize 0
        scalarFields := []
      }) false).1
  apply HeapOwnershipBelowFrontier.empty.alloc
  intro child member
  simp [HeapObject.ownedValues] at member

/-- The stronger hereditary certificate survives the same paired allocation.
The deleted constructor is a leaf, so its closure excludes the fresh source
frontier; the generic lifecycle theorem transports both its heap closure and
the enlarged target ledger. -/
theorem deletedCtorHeapClosureSurvivesPairedAllocation :
    SourceOnlyHeapClosureBinding
      deletedCtorLifecyclePaired.runtime.ledger
      (bind [] resetObjectVar (.object (.heap 0)))
      resetObjectVar 0
      (alloc deletedCtorLifecycleSourceOnly.nextRuntime
        (.natural 9223372036854775808) false).1.heap := by
  have objectBinding :
      SourceOnlyHeapBinding
        deletedCtorLifecycleSourceOnly.runtime.ledger
        (bind [] resetObjectVar (.object (.heap 0)))
        resetObjectVar 0 := {
    read := by rfl
    sourceOnly :=
      deletedCtorLifecycleSourceOnly.heapSourceOnly 0 (by rfl)
  }
  have found :
      findCell? deletedCtorLifecycleSourceOnly.nextRuntime.heap 0 =
        some ({
          object := .ctor {
            tag := oneFieldInfo.cidx
            objectFields := #[.erased]
            usizeFields := Array.replicate oneFieldInfo.usize 0
            scalarFields := []
          }
        } : HeapCell) := by
    rfl
  have noChildren : ∀ child,
      Value.object (.heap child) ∉
        ({
          object := .ctor {
            tag := oneFieldInfo.cidx
            objectFields := #[.erased]
            usizeFields := Array.replicate oneFieldInfo.usize 0
            scalarFields := []
          }
        } : HeapCell).object.ownedValues.toList := by
    intro child member
    simp [HeapObject.ownedValues] at member
  have closure :=
    objectBinding.closure_of_no_heap_children found noChildren
  exact
    deletedCtorLifecyclePaired
      |>.heapClosureBinding_of_heapOwnershipBelowFrontier
        deletedCtorLifecycleSourceOnly.runtime.ledger
        closure deletedCtorLifecycleSourceOwnershipBelowFrontier
          ⟨_, found⟩

/-- Bind the deleted constructor under the object local consumed by reset. -/
noncomputable def deletedCtorLifecycleResetState : MachineState :=
  { program := { decls := #[] }
    control := .yielded .erased
    env := bind [] resetObjectVar (.object (.heap 0))
    runtime := deletedCtorLifecycleSourceOnly.nextRuntime }

noncomputable def deletedCtorLifecycleResetLocalReady :
    DeletedResetLocalReadyAt
      deletedCtorLifecycleResetState 1 resetObjectVar := by
  apply DeletedResetLocalReadyAt.of_evalLetValue
      (fvarId := reuseTokenVar)
      (binderName := reuseTokenVar.name)
      (type := objType)
  rfl

/-- The successful reset result retains the source runtime's static ownership
bound without a fixture-specific heap calculation. -/
theorem deletedCtorLifecycleResetPreservesOwnershipBelowFrontier :
    HeapOwnershipBelowFrontier
      deletedCtorLifecycleResetLocalReady.nextRuntime :=
  deletedCtorLifecycleSourceOwnershipBelowFrontier.reset
    deletedCtorLifecycleResetLocalReady.effect

/-- The concrete reset token installed in the successor environment retains
the deleted constructor's certified source-only address. -/
theorem deletedCtorSourceOnlyBindingTransfersToResetToken :
    SourceOnlyReuseTokenBinding
      deletedCtorLifecycleSourceOnly.runtime.ledger
      (bind deletedCtorLifecycleResetState.env reuseTokenVar
        deletedCtorLifecycleResetLocalReady.token)
      reuseTokenVar 0 := by
  have objectBinding :
      SourceOnlyHeapBinding
        deletedCtorLifecycleSourceOnly.runtime.ledger
        deletedCtorLifecycleResetState.env resetObjectVar 0 := {
    read := by rfl
    sourceOnly :=
      deletedCtorLifecycleSourceOnly.heapSourceOnly 0 (by rfl)
  }
  exact
    deletedCtorLifecycleResetLocalReady.sourceOnlyReuseTokenBinding
      objectBinding (by rfl) reuseTokenVar

/-- A later retained paired allocation preserves the reset token's provenance:
the token still names a source allocation absent from the enlarged target
owner ledger. -/
theorem deletedCtorResetTokenSurvivesPairedAllocation :
    SourceOnlyReuseTokenBinding
      deletedCtorLifecyclePaired.runtime.ledger
      (bind deletedCtorLifecycleResetState.env reuseTokenVar
        deletedCtorLifecycleResetLocalReady.token)
      reuseTokenVar 0 :=
  deletedCtorSourceOnlyBindingTransfersToResetToken.monoLedger
    deletedCtorSourceOnlySurvivesPairedAllocation

/-- The existing concrete-token deletion starts with an empty target owner
ledger; its source cell is therefore source-only by construction. -/
noncomputable def deletedReuseSomeLedgerRuntime :
    LedgerShadowRuntimeRel emptyAddressRenaming
      deletedReuseSomeSourceState.runtime deletedReuseTargetState.runtime
      (envRootsOn neutralUsed deletedReuseSomeSourceState.env ++ [])
      (envRootsOn neutralUsed deletedReuseTargetState.env ++ []) where
  runtime := by simpa using deletedReuseSomeRuntimeRelated
  ledger := by
    simpa [deletedReuseTargetState] using
      TargetAllocationLedger.empty emptyAddressRenaming

def deletedReuseSomeLocalReady :
    DeletedReuseSomeLocalReadyAt deletedReuseSomeSourceState
      reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] 0 := by
  apply DeletedReuseSomeLocalReadyAt.of_reuseEffect
      (values := #[.erased]) (updateHeader := true)
  · simp [deletedReuseSomeSourceState, deletedReuseSomeSourceEnv,
      lookupValue, Impure.bind, lookup, reuseTokenVar, reuseArgVar]
  · simp [deletedReuseSomeSourceState, deletedReuseSomeSourceEnv,
      evalArgs, evalArg, Impure.bind, lookup, reuseTokenVar, reuseArgVar]
    rfl
  · rfl

theorem deletedReuseSomeLedgerSourceOnly :
    SourceOnlyUnderTargetLedger
      deletedReuseSomeLedgerRuntime.ledger 0 := by
  intro rightLocation bounded
  exact (Nat.not_lt_zero rightLocation bounded).elim

theorem deletedReuseSomeStepBinderReady :
    ExactShadowCodeBinderReady neutralUsed
      (ExactShadowCodeView.letDeleted
        (declaration := deadReuseDecl)
        retainedLargeNatContinuationRun
        (by native_decide)
        (by native_decide)) := by
  apply ExactShadowCodeBinderReady.letDeleted
  · native_decide
  · apply retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
      (index :=
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
    · apply ScopedCodeWellFormedTree.ret
      native_decide
    · simp [codeBinderIds, BinderNamesUnique]

/-- Exact deleted existing-address regression: the ledger proves that the
concrete reuse cell is source-only, the source overwrites it, and the target
stutters without changing its empty owner ledger. -/
theorem deletedReuseSomeExactStepLedgerPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedReuseSomeSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals deletedReuseTargetState targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 emptyAddressRenaming
        sourceAfter targetAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        deletedReuseSomeSourceState.program
        deletedReuseTargetState.program := by
    simpa [deletedReuseSomeSourceState, deletedReuseTargetState] using
      deletedReuseSomeProgramBinderReadyRelated
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        deletedReuseSomeSourceState.frames deletedReuseTargetState.frames
        [] [] := by
    exact .nil
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        deletedReuseSomeSourceState.joins
        deletedReuseTargetState.joins := by
    exact BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        deletedReuseSomeSourceState.env deletedReuseTargetState.env := by
    simpa [deletedReuseSomeSourceState, deletedReuseTargetState] using
      deletedReuseSomeEnvReachableRelated
  simpa [deletedReuseSomeSourceState, deletedReuseTargetState,
    deletedReuseBefore, deletedReuseAfter, deadReuseDecl, letDecl] using
    deletedReuseSomeStepBinderReady.match_deletedReuseSomeLetStep_ledger
      (fuelBound := Nat.le_refl 2)
      (usedBound := UsedSubset.refl neutralUsed)
      deletedReuseSomeSourceState deletedReuseTargetState programs frames
      joins env deletedReuseSomeLedgerRuntime deletedReuseSomeLocalReady
      deletedReuseSomeLedgerSourceOnly step

/-- A retained concrete reuse begins from one paired nullary constructor.
The live argument names that object directly, so the token's capability is
backed by an ordinary reachable root before the in-place overwrite. -/
def retainedReuseSomeInitialObject : ConstructorObject :=
  { tag := 0
    objectFields := #[]
    usizeFields := #[]
    scalarFields := [] }

def retainedReuseSomeUpdatedObject : ConstructorObject :=
  { tag := oneFieldInfo.cidx
    objectFields := #[.object (.heap 0)]
    usizeFields := #[]
    scalarFields := [] }

def retainedReuseSomeRuntime : RuntimeState :=
  (alloc ({} : RuntimeState)
    (.ctor retainedReuseSomeInitialObject)).1

def retainedReuseSomeResultRuntime : RuntimeState :=
  { retainedReuseSomeRuntime with
    heap := [(0, { object := .ctor retainedReuseSomeUpdatedObject })] }

def retainedReuseSomeDecl : LCNF.LetDecl .impure :=
  letDecl dead objType
    (.reuse reuseTokenVar oneFieldInfo true #[.fvar reuseArgVar])

def retainedReuseSomeCode : LCNF.Code .impure :=
  .let retainedReuseSomeDecl (.return dead)

def retainedReuseSomeContinuationUsed : UsedLocals :=
  ({} : UsedLocals).insert dead

def retainedReuseSomeUsed : UsedLocals :=
  ((retainedReuseSomeContinuationUsed.insert reuseTokenVar).insert
    reuseArgVar)

theorem retainedReuseSomeShadowRun :
    shadowCode? 2 {} retainedReuseSomeCode =
      some (retainedReuseSomeCode, retainedReuseSomeUsed) := by
  simp [retainedReuseSomeCode, retainedReuseSomeDecl, letDecl,
    retainedReuseSomeContinuationUsed, retainedReuseSomeUsed, shadowCode?,
    safeToElim, collectLetValue, collectArgs, collectArgList, collectArg,
    dead, reuseTokenVar, reuseArgVar]

def retainedReuseSomeExactGraph :
    ExactShadowCodeGraph 2 retainedReuseSomeUsed
      retainedReuseSomeCode retainedReuseSomeCode :=
  ExactShadowCodeGraph.ofResult retainedReuseSomeShadowRun

def retainedReuseSomeContinuationRun :
    ExactShadowCodeRun 1 {} retainedReuseSomeContinuationUsed
      (.return dead) (.return dead) where
  result := by
    simp [shadowCode?, retainedReuseSomeContinuationUsed]

theorem retainedReuseSomeStepBinderReady :
    ExactShadowCodeBinderReady retainedReuseSomeUsed
      (ExactShadowCodeView.letRetained
        (declaration := retainedReuseSomeDecl)
        retainedReuseSomeContinuationRun
        (Or.inl (by
          simp [retainedReuseSomeDecl, letDecl,
            retainedReuseSomeContinuationUsed]))) := by
  apply ExactShadowCodeBinderReady.letRetained
  apply ExactShadowCodeView.binderReady
    (index :=
      Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
        Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty dead)
  · apply ScopedCodeWellFormedTree.ret
    native_decide
  · exact CodeBinderList.ret
  · simp [BinderNamesUnique]
  · simp [BinderAbsenceTransfers]

def retainedReuseSomeEnv : Env :=
  bind (bind [] reuseArgVar (.object (.heap 0)))
    reuseTokenVar (.reuseToken (some 0))

def retainedReuseSomeState : MachineState :=
  { program := { decls := #[] }
    control := .code retainedReuseSomeCode
    env := retainedReuseSomeEnv
    runtime := retainedReuseSomeRuntime }

theorem retainedReuseSomeEnvRootsSubset :
    RootSubset
      (envRootsOn retainedReuseSomeUsed retainedReuseSomeEnv)
      [.reuseToken (some 0), .object (.heap 0)] := by
  intro value member
  have outer :
      value ∈
        .reuseToken (some 0) ::
          envRootsOn retainedReuseSomeUsed
            (bind [] reuseArgVar (.object (.heap 0))) :=
    envRootsOn_bind_subset value member
  rcases List.mem_cons.mp outer with rfl | inner
  · simp
  have inner' :
      value ∈
        .object (.heap 0) ::
          envRootsOn retainedReuseSomeUsed [] :=
    envRootsOn_bind_subset value inner
  rcases List.mem_cons.mp inner' with rfl | empty
  · simp
  have emptyRoots :
      envRootsOn retainedReuseSomeUsed ([] : Env) = [] := by
    unfold envRootsOn
    induction retainedReuseSomeUsed.toList with
    | nil => rfl
    | cons head tail ih => simp [lookup]
  rw [emptyRoots] at empty
  simp at empty

theorem retainedReuseSomeReady :
    RetainedLetReadyAt retainedReuseSomeState
      (runtimeRoots retainedReuseSomeState.runtime
        (envRootsOn retainedReuseSomeUsed retainedReuseSomeState.env ++ []))
      (.reuse reuseTokenVar oneFieldInfo true #[.fvar reuseArgVar]) := by
  intro location tokenRead
  have locationEq : location = 0 := by
    symm
    simpa [retainedReuseSomeState, retainedReuseSomeEnv, lookupValue,
      Impure.bind, lookup, reuseTokenVar, reuseArgVar] using tokenRead
  subst location
  apply Reachable.root
  apply extra_subset_runtimeRoots
  apply List.mem_append_left
  exact lookup_mem_envRootsOn (fvarId := reuseArgVar)
    (by native_decide)
    (by
      simp [retainedReuseSomeState, retainedReuseSomeEnv,
        Impure.bind, lookup, reuseArgVar, reuseTokenVar])

/-- Before concrete reuse, both the ordinary argument root and every saved
environment value lie below the one-cell allocation frontier. -/
theorem retainedReuseSomeSourceOwnership :
    SourceMachineOwnershipBelowFrontier retainedReuseSomeState := by
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · constructor
    · simpa [retainedReuseSomeState, retainedReuseSomeRuntime, alloc] using
        (HeapOwnershipBelowFrontier.empty.alloc
          (object := .ctor retainedReuseSomeInitialObject)
          (by
            simp [HeapObject.ownedValues,
              retainedReuseSomeInitialObject])
          false)
    · have objectBelow :
          HeapLocationsBelowFrontier retainedReuseSomeRuntime
            [.object (.heap 0)] := by
        intro location member
        have locationEq : location = 0 := by
          simpa using member
        subst location
        simp [retainedReuseSomeRuntime, alloc]
      have tokenBelow :
          HeapLocationsBelowFrontier retainedReuseSomeRuntime
            [.reuseToken (some 0)] := by
        intro location member
        simp at member
      have objectEnv :
          EnvironmentBelowFrontier retainedReuseSomeRuntime
            (bind [] reuseArgVar (.object (.heap 0))) :=
        EnvironmentBelowFrontier.bind
          (binder := reuseArgVar) (value := .object (.heap 0))
          EnvironmentBelowFrontier.empty objectBelow
      have fullEnv :
          EnvironmentBelowFrontier retainedReuseSomeRuntime
            (bind (bind [] reuseArgVar (.object (.heap 0)))
              reuseTokenVar (.reuseToken (some 0))) :=
        EnvironmentBelowFrontier.bind
          (binder := reuseTokenVar) (value := .reuseToken (some 0))
          objectEnv tokenBelow
      intro fvarId value found
      apply @fullEnv fvarId value
      simpa [retainedReuseSomeState, retainedReuseSomeEnv] using found
  · exact trivial

/-- Exact retained existing-address regression: both sides overwrite their
paired live cell, expose any larger hidden renaming chosen by the mature
runtime theorem, and transport the target owner ledger at frontier `1`. -/
theorem retainedReuseSomeExactStepLedgerPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedReuseSomeState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedReuseSomeState targetAfter ∧
      LedgerBinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter := by
  have initialObjects :
      HeapObjectRel emptyAddressRenaming
        (.ctor retainedReuseSomeInitialObject)
        (.ctor retainedReuseSomeInitialObject) := by
    apply HeapObjectRel.ctor
    · rfl
    · change ListRel (ValueRel emptyAddressRenaming) [] []
      exact .nil
    · rfl
    · rfl
  let paired := LedgerShadowRuntimeRel.empty.allocBoth
      initialObjects
      (by
        simp [RootSubset, HeapObject.ownedValues,
          retainedReuseSomeInitialObject])
      (by
        simp [RootSubset, HeapObject.ownedValues,
          retainedReuseSomeInitialObject])
      false
  have objectValues :
      ValueRel paired.larger
        (.object (.heap 0)) (.object (.heap 0)) := by
    simpa [alloc] using paired.values
  have mapping : paired.larger.forward 0 = some 0 := by
    cases objectValues with
    | heap mapping => exact mapping
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedReuseSomeState.program retainedReuseSomeState.program := by
    simpa [retainedReuseSomeState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 paired.larger
        retainedReuseSomeState.frames retainedReuseSomeState.frames [] [] := by
    simpa [retainedReuseSomeState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 paired.larger
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedReuseSomeUsed
        retainedReuseSomeState.joins retainedReuseSomeState.joins := by
    simpa [retainedReuseSomeState] using
      BinderReadyShadowJoinEnvRelated.empty 2 retainedReuseSomeUsed
  have env :
      EnvRelOn paired.larger retainedReuseSomeUsed
        retainedReuseSomeState.env retainedReuseSomeState.env := by
    simpa [retainedReuseSomeState, retainedReuseSomeEnv] using
      ((EnvRelOn.empty paired.larger retainedReuseSomeUsed).bindBoth
        (binder := reuseArgVar) objectValues).bindBoth
          (binder := reuseTokenVar) (.reuseSome mapping)
  have published :
      ShadowRuntimeRel paired.larger
        retainedReuseSomeState.runtime retainedReuseSomeState.runtime
        [.reuseToken (some 0), .object (.heap 0)]
        [.reuseToken (some 0), .object (.heap 0)] := by
    simpa [retainedReuseSomeState, retainedReuseSomeRuntime, alloc] using
      paired.runtime.runtime.prependNonHeap (.reuseSome mapping)
        (by intro location impossible; cases impossible)
        (by intro location impossible; cases impossible)
  have runtime :
      LedgerShadowRuntimeRel paired.larger
        retainedReuseSomeState.runtime retainedReuseSomeState.runtime
        (envRootsOn retainedReuseSomeUsed retainedReuseSomeState.env ++ [])
        (envRootsOn retainedReuseSomeUsed retainedReuseSomeState.env ++ []) := {
    runtime := by
      simpa only [List.append_nil] using
        published.restrictExtra (envRootsOn_related env)
          (by
            simpa [retainedReuseSomeState] using
              retainedReuseSomeEnvRootsSubset)
          (by
            simpa [retainedReuseSomeState] using
              retainedReuseSomeEnvRootsSubset)
    ledger := by
      simpa [retainedReuseSomeState, retainedReuseSomeRuntime, alloc] using
        paired.runtime.ledger
  }
  have tokenRead :
      lookupValue retainedReuseSomeState.env reuseTokenVar =
        .ok (.reuseToken (some 0)) := by
    simp [retainedReuseSomeState, retainedReuseSomeEnv, lookupValue,
      Impure.bind, lookup, reuseTokenVar, reuseArgVar]
  have argumentsRead :
      evalArgs retainedReuseSomeState.env #[.fvar reuseArgVar] =
        .ok #[.object (.heap 0)] := by
    simp [retainedReuseSomeState, retainedReuseSomeEnv, evalArgs, evalArg,
      Impure.bind, lookup, reuseTokenVar, reuseArgVar]
    rfl
  have sourceEffect :
      reuse retainedReuseSomeState.runtime (.reuseToken (some 0))
        oneFieldInfo true #[.object (.heap 0)] =
          .ok (retainedReuseSomeResultRuntime, .object (.heap 0)) := by
    simp [retainedReuseSomeState, retainedReuseSomeRuntime,
      retainedReuseSomeResultRuntime, retainedReuseSomeInitialObject,
      retainedReuseSomeUpdatedObject, reuse, getLiveCell, setCell,
      findCell?, replaceCell, alloc, oneFieldInfo, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have usedBound :
      UsedSubset
        (collectLetValue retainedReuseSomeContinuationUsed
          (LCNF.LetValue.reuse reuseTokenVar oneFieldInfo true
            #[.fvar reuseArgVar] : LCNF.LetValue .impure))
        retainedReuseSomeUsed := by
    simpa [collectLetValue, collectArgs, collectArgList, collectArg,
      retainedReuseSomeContinuationUsed, retainedReuseSomeUsed] using
      UsedSubset.refl retainedReuseSomeUsed
  rcases
      retainedReuseSomeStepBinderReady.match_retainedReuseSomeLetStep_ledger
      (fuelBound := Nat.le_refl 2) usedBound
      retainedReuseSomeState retainedReuseSomeState programs frames joins env
      retainedReuseSomeReady tokenRead argumentsRead (by rfl) sourceEffect
      runtime step with
    ⟨larger, targetAfter, extension, path, related⟩
  exact ⟨larger, targetAfter, paired.extension.trans extension,
    by
      simpa [retainedReuseSomeState, retainedReuseSomeCode,
        retainedReuseSomeDecl, letDecl] using path,
    related⟩

/-- Exact retained concrete-token regression: the in-place overwrite keeps
the one-cell frontier fixed and preserves complete source ownership. -/
theorem retainedReuseSomeExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals retainedReuseSomeState sourceAfter) :
    ∃ larger targetAfter,
      RenamingExtends emptyAddressRenaming larger ∧
      NonLockstep.Reaches externals retainedReuseSomeState targetAfter ∧
      BinderReadyReachableMachineRelated 2 larger
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have initialObjects :
      HeapObjectRel emptyAddressRenaming
        (.ctor retainedReuseSomeInitialObject)
        (.ctor retainedReuseSomeInitialObject) := by
    apply HeapObjectRel.ctor
    · rfl
    · change ListRel (ValueRel emptyAddressRenaming) [] []
      exact .nil
    · rfl
    · rfl
  let paired := LedgerShadowRuntimeRel.empty.allocBoth
      initialObjects
      (by
        simp [RootSubset, HeapObject.ownedValues,
          retainedReuseSomeInitialObject])
      (by
        simp [RootSubset, HeapObject.ownedValues,
          retainedReuseSomeInitialObject])
      false
  have objectValues :
      ValueRel paired.larger
        (.object (.heap 0)) (.object (.heap 0)) := by
    simpa [alloc] using paired.values
  have mapping : paired.larger.forward 0 = some 0 := by
    cases objectValues with
    | heap mapping => exact mapping
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        retainedReuseSomeState.program retainedReuseSomeState.program := by
    simpa [retainedReuseSomeState, ProgramRelated] using
      (ListRel.nil :
        ListRel (DeclRelated (BinderReadyShadowCodeRelated 2)) [] [])
  have frames :
      BinderReadyReachableFramesRelated 2 paired.larger
        retainedReuseSomeState.frames retainedReuseSomeState.frames [] [] := by
    simpa [retainedReuseSomeState] using
      (BinderReadyReachableFramesRelated.nil :
        BinderReadyReachableFramesRelated 2 paired.larger
          [] [] [] [])
  have joins :
      BinderReadyShadowJoinEnvRelated 2 retainedReuseSomeUsed
        retainedReuseSomeState.joins retainedReuseSomeState.joins := by
    simpa [retainedReuseSomeState] using
      BinderReadyShadowJoinEnvRelated.empty 2 retainedReuseSomeUsed
  have env :
      EnvRelOn paired.larger retainedReuseSomeUsed
        retainedReuseSomeState.env retainedReuseSomeState.env := by
    simpa [retainedReuseSomeState, retainedReuseSomeEnv] using
      ((EnvRelOn.empty paired.larger retainedReuseSomeUsed).bindBoth
        (binder := reuseArgVar) objectValues).bindBoth
          (binder := reuseTokenVar) (.reuseSome mapping)
  have published :
      ShadowRuntimeRel paired.larger
        retainedReuseSomeState.runtime retainedReuseSomeState.runtime
        [.reuseToken (some 0), .object (.heap 0)]
        [.reuseToken (some 0), .object (.heap 0)] := by
    simpa [retainedReuseSomeState, retainedReuseSomeRuntime, alloc] using
      paired.runtime.runtime.prependNonHeap (.reuseSome mapping)
        (by intro location impossible; cases impossible)
        (by intro location impossible; cases impossible)
  have runtime :
      ShadowRuntimeRel paired.larger
        retainedReuseSomeState.runtime retainedReuseSomeState.runtime
        (envRootsOn retainedReuseSomeUsed retainedReuseSomeState.env ++ [])
        (envRootsOn retainedReuseSomeUsed retainedReuseSomeState.env ++ []) := by
    simpa only [List.append_nil] using
      published.restrictExtra (envRootsOn_related env)
        (by
          simpa [retainedReuseSomeState] using
            retainedReuseSomeEnvRootsSubset)
        (by
          simpa [retainedReuseSomeState] using
            retainedReuseSomeEnvRootsSubset)
  have usedBound :
      UsedSubset
        (collectLetValue retainedReuseSomeContinuationUsed
          (LCNF.LetValue.reuse reuseTokenVar oneFieldInfo true
            #[.fvar reuseArgVar] : LCNF.LetValue .impure))
        retainedReuseSomeUsed := by
    simpa [collectLetValue, collectArgs, collectArgList, collectArg,
      retainedReuseSomeContinuationUsed, retainedReuseSomeUsed] using
      UsedSubset.refl retainedReuseSomeUsed
  rcases
      retainedReuseSomeStepBinderReady
        |>.match_retainedReuseLetStep_withOwnership
          (fuelBound := Nat.le_refl 2) usedBound
          retainedReuseSomeState retainedReuseSomeState programs frames joins
          env retainedReuseSomeReady runtime
          retainedReuseSomeSourceOwnership step with
    ⟨larger, targetAfter, extension, path, related, ownership⟩
  exact ⟨larger, targetAfter, paired.extension.trans extension,
    by
      simpa [retainedReuseSomeState, retainedReuseSomeCode,
        retainedReuseSomeDecl, letDecl] using path,
    related, ownership⟩

/-- The three deleted-write fixtures obtain their local heap shapes by
inverting the successful runtime operations, rather than by restating cell
layout and bounds manually. -/
theorem deletedObjectSetLocalReadyFromEffect :
    Nonempty
      (Σ location,
        DeletedObjectSetLocalReadyAt deletedObjectSetSourceState
          dead 0 .erased location) := by
  apply DeletedObjectSetLocalReadyAt.of_effect_nonempty
      (objectValue := .object (.heap 0))
      (fieldValue := .erased)
  · simp [deletedObjectSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl
  · rfl

theorem deletedUSizeSetLocalReadyFromEffect :
    Nonempty
      (Σ location,
        DeletedUSizeSetLocalReadyAt deletedUSizeSetSourceState
          dead 1 usizeField location) := by
  apply DeletedUSizeSetLocalReadyAt.of_effect_nonempty
      (objectValue := .object (.heap 0))
      (fieldValue := .usize 7)
  · simp [deletedUSizeSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · simp [deletedUSizeSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl

theorem deletedScalarSetLocalReadyFromEffect :
    Nonempty
      (Σ location,
        DeletedScalarSetLocalReadyAt deletedScalarSetSourceState
          dead scalarField location) := by
  apply DeletedScalarSetLocalReadyAt.of_effect_nonempty
      (width := 8) (offset := 0)
      (objectValue := .object (.heap 0))
      (fieldValue := .scalar (.uint8 9))
  · simp [deletedScalarSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · simp [deletedScalarSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl

theorem deletedObjectSetReady :
    DeletedObjectSetReadyAt deletedObjectSetSourceState
      (runtimeRoots deletedObjectSetSourceState.runtime
        (envRootsOn neutralUsed deletedObjectSetSourceState.env))
      dead 0 .erased := by
  let selected :=
    Classical.choice deletedObjectSetLocalReadyFromEffect
  rcases selected with ⟨location, shape⟩
  have locationEq : location = 0 := by
    simpa [deletedObjectSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
      using shape.objectRead.symm
  subst location
  exact shape.deletedReadyAt
    (by simpa [deletedObjectSetSourceState] using
      deletedWriteDestinationUnreachable)

theorem deletedUSizeSetReady :
    DeletedUSizeSetReadyAt deletedUSizeSetSourceState
      (runtimeRoots deletedUSizeSetSourceState.runtime
        (envRootsOn neutralUsed deletedUSizeSetSourceState.env))
      dead 1 usizeField := by
  let selected :=
    Classical.choice deletedUSizeSetLocalReadyFromEffect
  rcases selected with ⟨location, shape⟩
  have locationEq : location = 0 := by
    simpa [deletedUSizeSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
      using shape.objectRead.symm
  subst location
  exact shape.deletedReadyAt
    (by simpa [deletedUSizeSetSourceState] using
      deletedWriteDestinationUnreachable)

theorem deletedScalarSetReady :
    DeletedScalarSetReadyAt deletedScalarSetSourceState
      (runtimeRoots deletedScalarSetSourceState.runtime
        (envRootsOn neutralUsed deletedScalarSetSourceState.env))
      dead scalarField := by
  let selected :=
    Classical.choice deletedScalarSetLocalReadyFromEffect
  rcases selected with ⟨location, shape⟩
  have locationEq : location = 0 := by
    simpa [deletedScalarSetSourceState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
      using shape.objectRead.symm
  subst location
  exact shape.deletedReadyAt
    (by simpa [deletedScalarSetSourceState] using
      deletedWriteDestinationUnreachable)

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

/-- The allocating constructor fixture starts from a complete, trivially
owned source machine: its runtime is empty and its only environment value is
erased. -/
theorem allocatingSourceInnerMachineOwnershipBelowFrontier :
    SourceMachineOwnershipBelowFrontier
      allocatingSourceInnerState := by
  have erasedBelow :
      HeapLocationsBelowFrontier ({} : RuntimeState) [.erased] := by
    intro location member
    simp at member
  have envBound :
      EnvironmentBelowFrontier ({} : RuntimeState) liveEnv :=
    EnvironmentBelowFrontier.bind
      (binder := live) (value := .erased)
      EnvironmentBelowFrontier.empty erasedBelow
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · exact {
      heap := by
        simpa [allocatingSourceInnerState] using
          HeapOwnershipBelowFrontier.empty
      env := by
        intro fvarId value found
        apply @envBound fvarId value
        simpa [allocatingSourceInnerState, liveEnv] using found
    }
  · trivial

/-- Every value in the deleted-write source environment is below the single
allocated cell's frontier, including the target-dead object operand. -/
theorem deletedWriteSourceEnvironmentBelowFrontier :
    EnvironmentBelowFrontier
      deletedWriteSourceRuntime deletedWriteSourceEnv := by
  have erasedBelow :
      HeapLocationsBelowFrontier
        deletedWriteSourceRuntime [.erased] := by
    intro location member
    simp at member
  have objectBelow :
      HeapLocationsBelowFrontier deletedWriteSourceRuntime
        [.object (.heap 0)] := by
    intro location member
    simp at member
    subst location
    simp [deletedWriteSourceRuntime, alloc]
  have usizeBelow :
      HeapLocationsBelowFrontier deletedWriteSourceRuntime
        [.usize 7] := by
    intro location member
    simp at member
  have scalarBelow :
      HeapLocationsBelowFrontier deletedWriteSourceRuntime
        [.scalar (.uint8 9)] := by
    intro location member
    simp at member
  have liveBound :
      EnvironmentBelowFrontier deletedWriteSourceRuntime liveEnv := by
    have extended :
        EnvironmentBelowFrontier deletedWriteSourceRuntime
          (bind [] live .erased) :=
      EnvironmentBelowFrontier.bind
        (runtime := deletedWriteSourceRuntime)
        (binder := live) (value := .erased)
        EnvironmentBelowFrontier.empty erasedBelow
    intro fvarId value found
    apply @extended fvarId value
    simpa [liveEnv] using found
  have objectBound :
      EnvironmentBelowFrontier deletedWriteSourceRuntime
        (bind liveEnv dead (.object (.heap 0))) :=
    EnvironmentBelowFrontier.bind
      (binder := dead) (value := .object (.heap 0))
      liveBound objectBelow
  have usizeBound :
      EnvironmentBelowFrontier deletedWriteSourceRuntime
        (bind (bind liveEnv dead (.object (.heap 0)))
          usizeField (.usize 7)) :=
    EnvironmentBelowFrontier.bind
      (binder := usizeField) (value := .usize 7)
      objectBound usizeBelow
  have scalarBound :
      EnvironmentBelowFrontier deletedWriteSourceRuntime
        (bind
          (bind (bind liveEnv dead (.object (.heap 0)))
            usizeField (.usize 7))
          scalarField (.scalar (.uint8 9))) :=
    EnvironmentBelowFrontier.bind
      (binder := scalarField) (value := .scalar (.uint8 9))
      usizeBound scalarBelow
  intro fvarId value found
  apply @scalarBound fvarId value
  simpa [deletedWriteSourceEnv] using found

/-- The object-write fixture lifts its concrete heap and environment bounds
to the full source machine. -/
theorem deletedObjectSetSourceMachineOwnershipBelowFrontier :
    SourceMachineOwnershipBelowFrontier
      deletedObjectSetSourceState := by
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · exact {
      heap := by
        simpa [deletedObjectSetSourceState] using
          deletedWriteSourceOwnershipBelowFrontier
      env := by
        intro fvarId value found
        apply @deletedWriteSourceEnvironmentBelowFrontier fvarId value
        simpa [deletedObjectSetSourceState] using found
    }
  · trivial

/-- The USize-write suffix has the same runtime, environment, and frames as
the full deleted-write fixture, so only its active control changes. -/
theorem deletedUSizeSetSourceMachineOwnershipBelowFrontier :
    SourceMachineOwnershipBelowFrontier
      deletedUSizeSetSourceState := by
  have bounded :=
    deletedObjectSetSourceMachineOwnershipBelowFrontier.withControlAndJoins
      deletedUSizeSetSourceState.control
      deletedUSizeSetSourceState.joins
  simpa [deletedObjectSetSourceState, deletedUSizeSetSourceState] using bounded

/-- The packed-scalar suffix inherits the same complete source-machine
ownership carrier. -/
theorem deletedScalarSetSourceMachineOwnershipBelowFrontier :
    SourceMachineOwnershipBelowFrontier
      deletedScalarSetSourceState := by
  have bounded :=
    deletedObjectSetSourceMachineOwnershipBelowFrontier.withControlAndJoins
      deletedScalarSetSourceState.control
      deletedScalarSetSourceState.joins
  simpa [deletedObjectSetSourceState, deletedScalarSetSourceState] using bounded

/-- The reset fixture's source object and complete environment lie below the
same single-cell frontier before recursive release begins. -/
theorem deletedResetSourceMachineOwnershipBelowFrontier :
    SourceMachineOwnershipBelowFrontier
      deletedResetSourceState := by
  have erasedBelow :
      HeapLocationsBelowFrontier
        deletedResetSourceRuntime [.erased] := by
    intro location member
    simp at member
  have objectBelow :
      HeapLocationsBelowFrontier deletedResetSourceRuntime
        [.object (.heap 0)] := by
    intro location member
    simp at member
    subst location
    simp [deletedResetSourceRuntime, alloc]
  have liveBound :
      EnvironmentBelowFrontier deletedResetSourceRuntime liveEnv := by
    have extended :
        EnvironmentBelowFrontier deletedResetSourceRuntime
          (bind [] live .erased) :=
      EnvironmentBelowFrontier.bind
        (runtime := deletedResetSourceRuntime)
        (binder := live) (value := .erased)
        EnvironmentBelowFrontier.empty erasedBelow
    intro fvarId value found
    apply @extended fvarId value
    simpa [liveEnv] using found
  have sourceEnvBound :
      EnvironmentBelowFrontier deletedResetSourceRuntime
        (bind liveEnv resetObjectVar (.object (.heap 0))) :=
    EnvironmentBelowFrontier.bind
      (binder := resetObjectVar) (value := .object (.heap 0))
      liveBound objectBelow
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · exact {
      heap := by
        change HeapOwnershipBelowFrontier
          (alloc ({} : RuntimeState) (.ctor deletedResetObject) false).1
        apply HeapOwnershipBelowFrontier.empty.alloc
        intro child member
        simp [deletedResetObject, HeapObject.ownedValues] at member
      env := by
        intro fvarId value found
        apply @sourceEnvBound fvarId value
        simpa [deletedResetSourceState, deletedResetSourceEnv] using found
    }
  · trivial

/-- The ownership-strengthened constructor matcher checks the actual
allocating semantic step: the target stutters while the source binds its
fresh, target-dead heap value. -/
theorem deletedCtorExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals allocatingSourceInnerState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        allocatingTargetInnerState targetAfter ∧
      BinderReadyReachableMachineRelated 3 emptyAddressRenaming
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 3)
        allocatingSourceInnerState.program
        allocatingTargetInnerState.program := by
    simpa [allocatingSourceInnerState, allocatingTargetInnerState] using
      allocatingProgramBinderReadyRelated
  have frames :
      BinderReadyReachableFramesRelated 3 emptyAddressRenaming
        allocatingSourceInnerState.frames
        allocatingTargetInnerState.frames [] [] := by
    exact .nil
  have continuation :
      BinderReadyShadowCodeGraph 3 neutralUsed
        (.return live) (.return live) := by
    apply retainedLargeNatContinuationRun.toBinderReadyShadowCodeGraphAt
    · omega
    · exact UsedSubset.refl neutralUsed
    · apply
        retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
        (index :=
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
            Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
      · apply ScopedCodeWellFormedTree.ret
        native_decide
      · simp [codeBinderIds, BinderNamesUnique]
  have joins :
      BinderReadyShadowJoinEnvRelated 3 neutralUsed
        allocatingSourceInnerState.joins
        allocatingTargetInnerState.joins :=
    BinderReadyShadowJoinEnvRelated.empty 3 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        allocatingSourceInnerState.env
        allocatingTargetInnerState.env := by
    simpa [allocatingSourceInnerState, allocatingTargetInnerState] using
      liveEnvReachableRelated
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        allocatingSourceInnerState.runtime
        allocatingTargetInnerState.runtime
        (envRootsOn neutralUsed allocatingSourceInnerState.env ++ [])
        (envRootsOn neutralUsed allocatingTargetInnerState.env ++ []) := by
    simpa [allocatingSourceInnerState, allocatingTargetInnerState] using
      emptyRuntime_shadowRelated_of_roots
        (envRootsOn_related liveEnvReachableRelated)
  simpa [allocatingSourceInnerState, allocatingTargetInnerState,
    deadCtorDecl, letDecl] using
    (match_deletedCtorStep_binderReady_withOwnership
      (sourceState := allocatingSourceInnerState)
      (targetState := allocatingTargetInnerState)
      (sourceContinuation := .return live)
      (targetContinuation := .return live)
      (fvarId := dead)
      (binderName := dead.name)
      (type := objType)
      (info := oneFieldInfo)
      (arguments := #[.fvar live])
      programs frames continuation joins env (by native_decide)
      runtime deletedCtorReady
      allocatingSourceInnerMachineOwnershipBelowFrontier step)

/-- The ownership-strengthened object-write matcher checks the first
mutation of the deleted-write chain, retaining the entire source environment
and heap while the target remains at its final return. -/
theorem deletedObjectSetExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedObjectSetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        deletedWritesTargetState targetAfter ∧
      BinderReadyReachableMachineRelated 4 emptyAddressRenaming
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 4)
        deletedObjectSetSourceState.program
        deletedWritesTargetState.program := by
    simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramBinderReadyRelated
  have frames :
      BinderReadyReachableFramesRelated 4 emptyAddressRenaming
        deletedObjectSetSourceState.frames
        deletedWritesTargetState.frames [] [] := by
    exact .nil
  have continuation :
      BinderReadyShadowCodeGraph 4 neutralUsed
        (.uset dead 1 usizeField <|
          .sset dead 8 0 scalarField u8Type <| .return live)
        (.return live) := by
    simpa [deletedWritesAfter] using
      (show BinderReadyShadowCodeGraph 4 neutralUsed
          (.uset dead 1 usizeField <|
            .sset dead 8 0 scalarField u8Type <| .return live)
          deletedWritesAfter from
        ⟨3, neutralUsed, by omega, deletedUSizeScalarExactGraph,
          UsedSubset.refl neutralUsed,
          deletedUSizeScalarExactBinderReady⟩)
  have joins :
      BinderReadyShadowJoinEnvRelated 4 neutralUsed
        deletedObjectSetSourceState.joins
        deletedWritesTargetState.joins :=
    BinderReadyShadowJoinEnvRelated.empty 4 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        deletedObjectSetSourceState.env deletedWritesTargetState.env := by
    simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
      deletedWriteEnvReachableRelated
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        deletedObjectSetSourceState.runtime
        deletedWritesTargetState.runtime
        (envRootsOn neutralUsed deletedObjectSetSourceState.env ++ [])
        (envRootsOn neutralUsed deletedWritesTargetState.env ++ []) := by
    simpa [deletedObjectSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated
  simpa [deletedObjectSetSourceState, deletedWritesTargetState,
    deletedWritesBefore, deletedWritesAfter, withCodeControl] using
    (match_deletedObjectSetStep_of_ready_binderReady_withOwnership
      (sourceState := deletedObjectSetSourceState)
      (targetState := deletedWritesTargetState)
      (sourceContinuation := .uset dead 1 usizeField <|
        .sset dead 8 0 scalarField u8Type <| .return live)
      (targetContinuation := .return live)
      (object := dead)
      (index := 0)
      (field := .erased)
      programs frames continuation joins env runtime
      (by simpa using deletedObjectSetReady)
      deletedObjectSetSourceMachineOwnershipBelowFrontier step)

/-- The exact deleted-USize branch performs its source-only unboxed update
while retaining the complete source ownership carrier. -/
theorem deletedUSizeSetExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedUSizeSetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        deletedWritesTargetState targetAfter ∧
      BinderReadyReachableMachineRelated 4 emptyAddressRenaming
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 4)
        deletedUSizeSetSourceState.program
        deletedWritesTargetState.program := by
    simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramBinderReadyRelated
  have frames :
      BinderReadyReachableFramesRelated 4 emptyAddressRenaming
        deletedUSizeSetSourceState.frames
        deletedWritesTargetState.frames [] [] := by
    exact .nil
  have continuation :
      BinderReadyShadowCodeGraph 4 neutralUsed
        (.sset dead 8 0 scalarField u8Type <| .return live)
        (.return live) := by
    simpa [deletedWritesAfter] using
      (show BinderReadyShadowCodeGraph 4 neutralUsed
          (.sset dead 8 0 scalarField u8Type <| .return live)
          deletedWritesAfter from
        ⟨2, neutralUsed, by omega, deletedScalarExactGraph,
          UsedSubset.refl neutralUsed,
          deletedScalarExactBinderReady⟩)
  have joins :
      BinderReadyShadowJoinEnvRelated 4 neutralUsed
        deletedUSizeSetSourceState.joins
        deletedWritesTargetState.joins :=
    BinderReadyShadowJoinEnvRelated.empty 4 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        deletedUSizeSetSourceState.env deletedWritesTargetState.env := by
    simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
      deletedWriteEnvReachableRelated
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        deletedUSizeSetSourceState.runtime
        deletedWritesTargetState.runtime
        (envRootsOn neutralUsed deletedUSizeSetSourceState.env ++ [])
        (envRootsOn neutralUsed deletedWritesTargetState.env ++ []) := by
    simpa [deletedUSizeSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated
  simpa [deletedUSizeSetSourceState, deletedWritesTargetState,
    deletedWritesAfter, withCodeControl] using
    (match_deletedUSizeSetStep_of_ready_binderReady_withOwnership
      (sourceState := deletedUSizeSetSourceState)
      (targetState := deletedWritesTargetState)
      (sourceContinuation :=
        .sset dead 8 0 scalarField u8Type <| .return live)
      (targetContinuation := .return live)
      (object := dead)
      (index := 1)
      (field := usizeField)
      programs frames continuation joins env runtime
      (by simpa using deletedUSizeSetReady)
      deletedUSizeSetSourceMachineOwnershipBelowFrontier step)

/-- The exact deleted-scalar branch performs its source-only packed update
while retaining the complete source ownership carrier. -/
theorem deletedScalarSetExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedScalarSetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        deletedWritesTargetState targetAfter ∧
      BinderReadyReachableMachineRelated 4 emptyAddressRenaming
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 4)
        deletedScalarSetSourceState.program
        deletedWritesTargetState.program := by
    simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
      deletedWritesProgramBinderReadyRelated
  have frames :
      BinderReadyReachableFramesRelated 4 emptyAddressRenaming
        deletedScalarSetSourceState.frames
        deletedWritesTargetState.frames [] [] := by
    exact .nil
  have continuation :
      BinderReadyShadowCodeGraph 4 neutralUsed
        (.return live) (.return live) := by
    apply retainedLargeNatContinuationRun.toBinderReadyShadowCodeGraphAt
    · omega
    · exact UsedSubset.refl neutralUsed
    · apply
        retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
        (index :=
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
            Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
      · apply ScopedCodeWellFormedTree.ret
        native_decide
      · simp [codeBinderIds, BinderNamesUnique]
  have joins :
      BinderReadyShadowJoinEnvRelated 4 neutralUsed
        deletedScalarSetSourceState.joins
        deletedWritesTargetState.joins :=
    BinderReadyShadowJoinEnvRelated.empty 4 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        deletedScalarSetSourceState.env deletedWritesTargetState.env := by
    simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
      deletedWriteEnvReachableRelated
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        deletedScalarSetSourceState.runtime
        deletedWritesTargetState.runtime
        (envRootsOn neutralUsed deletedScalarSetSourceState.env ++ [])
        (envRootsOn neutralUsed deletedWritesTargetState.env ++ []) := by
    simpa [deletedScalarSetSourceState, deletedWritesTargetState] using
      deletedWriteRuntimeRelated
  simpa [deletedScalarSetSourceState, deletedWritesTargetState,
    deletedWritesAfter, withCodeControl] using
    (match_deletedScalarSetStep_of_ready_binderReady_withOwnership
      (sourceState := deletedScalarSetSourceState)
      (targetState := deletedWritesTargetState)
      (sourceContinuation := .return live)
      (targetContinuation := .return live)
      (object := dead)
      (width := 8)
      (offset := 0)
      (field := scalarField)
      (type := u8Type)
      programs frames continuation joins env runtime
      (by simpa using deletedScalarSetReady)
      deletedScalarSetSourceMachineOwnershipBelowFrontier step)

/-- The concrete reset semantic step likewise retains the complete source
carrier across recursive release and dead reuse-token binding. -/
theorem deletedResetExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedResetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        deletedResetTargetState targetAfter ∧
      BinderReadyReachableMachineRelated 2 emptyAddressRenaming
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have programs :
      ProgramRelated (BinderReadyShadowCodeRelated 2)
        deletedResetSourceState.program
        deletedResetTargetState.program := by
    simpa [deletedResetSourceState, deletedResetTargetState] using
      deletedResetProgramBinderReadyRelated
  have frames :
      BinderReadyReachableFramesRelated 2 emptyAddressRenaming
        deletedResetSourceState.frames
        deletedResetTargetState.frames [] [] := by
    exact .nil
  have continuation :
      BinderReadyShadowCodeGraph 2 neutralUsed
        (.return live) (.return live) := by
    apply retainedLargeNatContinuationRun.toBinderReadyShadowCodeGraphAt
    · omega
    · exact UsedSubset.refl neutralUsed
    · apply
        retainedLargeNatContinuationRun.toGraph.binderReady_of_canonical
        (index :=
          Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.pushVar
            Fir.LeanIR.Passes.SimpCaseScopedBridge.ScopeIndex.empty live)
      · apply ScopedCodeWellFormedTree.ret
        native_decide
      · simp [codeBinderIds, BinderNamesUnique]
  have joins :
      BinderReadyShadowJoinEnvRelated 2 neutralUsed
        deletedResetSourceState.joins
        deletedResetTargetState.joins :=
    BinderReadyShadowJoinEnvRelated.empty 2 neutralUsed
  have env :
      EnvRelOn emptyAddressRenaming neutralUsed
        deletedResetSourceState.env deletedResetTargetState.env := by
    simpa [deletedResetSourceState, deletedResetTargetState] using
      deletedResetEnvReachableRelated
  have runtime :
      ShadowRuntimeRel emptyAddressRenaming
        deletedResetSourceState.runtime deletedResetTargetState.runtime
        (envRootsOn neutralUsed deletedResetSourceState.env ++ [])
        (envRootsOn neutralUsed deletedResetTargetState.env ++ []) := by
    simpa [deletedResetSourceState, deletedResetTargetState] using
      deletedResetRuntimeRelated
  simpa [deletedResetSourceState, deletedResetTargetState,
    deletedResetBefore, deletedResetAfter, deadResetDecl, letDecl] using
    (match_deletedResetStep_binderReady_withOwnership
      (sourceState := deletedResetSourceState)
      (targetState := deletedResetTargetState)
      (sourceContinuation := .return live)
      (targetContinuation := .return live)
      (fvarId := dead)
      (binderName := dead.name)
      (type := objType)
      (count := 1)
      (object := resetObjectVar)
      programs frames continuation joins env (by native_decide)
      runtime (by simpa using deletedResetReady)
      deletedResetSourceMachineOwnershipBelowFrontier step)

/-- A concrete join used to exercise ownership through argument evaluation
and `bindParamsOver`, independently of compiler liveness. -/
def ownershipJumpTarget : FVarId := ⟨`ownershipJumpTarget⟩

def ownershipJumpParameter : FVarId := ⟨`ownershipJumpParameter⟩

def ownershipJumpDeclaration : LCNF.FunDecl .impure :=
  .mk ownershipJumpTarget ownershipJumpTarget.name
    #[{
      fvarId := ownershipJumpParameter
      binderName := ownershipJumpParameter.name
      type := objType
      borrow := false
    }]
    objType
    (.return ownershipJumpParameter)

def ownershipJumpState : MachineState :=
  { allocatingSourceInnerState with
    control := .code (.jmp ownershipJumpTarget #[.fvar live])
    joins := [(ownershipJumpTarget, ownershipJumpDeclaration)] }

def ownershipJumpAfterState : MachineState :=
  { ownershipJumpState with
    env := bind liveEnv ownershipJumpParameter .erased
    control := .code (.return ownershipJumpParameter) }

theorem ownershipJumpStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipJumpState := by
  have bounded :=
    allocatingSourceInnerMachineOwnershipBelowFrontier.withControlAndJoins
      ownershipJumpState.control ownershipJumpState.joins
  simpa [allocatingSourceInnerState, ownershipJumpState] using bounded

/-- The fixture takes the successful jump branch, including the concrete
one-argument environment fold. -/
theorem ownershipJumpCoreStep :
    coreStep ownershipJumpState = .next ownershipJumpAfterState := by
  simp [ownershipJumpState, ownershipJumpAfterState,
    ownershipJumpDeclaration, allocatingSourceInnerState,
    coreStep, findJoinPoint?, evalArgs, Array.mapM_eq_mapM_toList,
    List.mapM_cons, evalArg, bindParamsOver, liveEnv, lookup,
    LCNF.FunDecl.params, LCNF.FunDecl.value,
    List.zip, List.zipWith,
    Functor.map, Except.map, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- The unified active-code dispatcher preserves ownership across that
concrete jump rather than relying on a vacuous error branch. -/
theorem ownershipJumpCodeStepPreserves
    (externals : ExternalSpec) :
    SourceMachineOwnershipBelowFrontier ownershipJumpAfterState :=
  ownershipJumpStateBelowFrontier.codeStep
    (Step.internal (externals := externals) ownershipJumpCoreStep)

def ownershipIncrementCell : HeapCell :=
  { object := .ctor deletedResetObject, rc := 2 }

def ownershipIncrementRuntime : RuntimeState :=
  { deletedResetSourceRuntime with heap := [(0, ownershipIncrementCell)] }

def ownershipIncrementState : MachineState :=
  { deletedResetSourceState with
    control := .code
      (.inc resetObjectVar 1 true false (.return live)) }

def ownershipIncrementAfterState : MachineState :=
  { ownershipIncrementState with
    runtime := ownershipIncrementRuntime
    control := .code (.return live) }

theorem ownershipIncrementStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipIncrementState := by
  have bounded :=
    deletedResetSourceMachineOwnershipBelowFrontier.withControlAndJoins
      ownershipIncrementState.control ownershipIncrementState.joins
  simpa [deletedResetSourceState, ownershipIncrementState] using bounded

theorem ownershipIncrementCoreStep :
    coreStep ownershipIncrementState =
      .next ownershipIncrementAfterState := by
  rfl

/-- The ordinary, nonpersistent increment branch really updates `rc` from
one to two and remains inside the ownership carrier. -/
theorem ownershipIncrementCodeStepPreserves
    (externals : ExternalSpec) :
    SourceMachineOwnershipBelowFrontier ownershipIncrementAfterState :=
  ownershipIncrementStateBelowFrontier.codeStep
    (Step.internal (externals := externals) ownershipIncrementCoreStep)

def ownershipDecrementCell : HeapCell :=
  { object := .ctor deletedResetObject, rc := 0, live := false }

def ownershipDecrementRuntime : RuntimeState :=
  { deletedResetSourceRuntime with heap := [(0, ownershipDecrementCell)] }

def ownershipDecrementState : MachineState :=
  { deletedResetSourceState with
    control := .code
      (.dec resetObjectVar 1 true false none (.return live)) }

def ownershipDecrementAfterState : MachineState :=
  { ownershipDecrementState with
    runtime := ownershipDecrementRuntime
    control := .code (.return live) }

theorem ownershipDecrementStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipDecrementState := by
  have bounded :=
    deletedResetSourceMachineOwnershipBelowFrontier.withControlAndJoins
      ownershipDecrementState.control ownershipDecrementState.joins
  simpa [deletedResetSourceState, ownershipDecrementState] using bounded

theorem ownershipDecrementCoreStep :
    coreStep ownershipDecrementState =
      .next ownershipDecrementAfterState := by
  rfl

/-- The ordinary decrement branch takes the recursive-release path, marks
the sole cell dead, and preserves the ownership invariant. -/
theorem ownershipDecrementCodeStepPreserves
    (externals : ExternalSpec) :
    SourceMachineOwnershipBelowFrontier ownershipDecrementAfterState :=
  ownershipDecrementStateBelowFrontier.codeStep
    (Step.internal (externals := externals) ownershipDecrementCoreStep)

def ownershipErasedDeleteState : MachineState :=
  { allocatingSourceInnerState with
    control := .code (.del live (.return live)) }

def ownershipErasedDeleteAfterState : MachineState :=
  { ownershipErasedDeleteState with control := .code (.return live) }

theorem ownershipErasedDeleteStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipErasedDeleteState := by
  have bounded :=
    allocatingSourceInnerMachineOwnershipBelowFrontier.withControlAndJoins
      ownershipErasedDeleteState.control
      ownershipErasedDeleteState.joins
  simpa [allocatingSourceInnerState, ownershipErasedDeleteState] using bounded

theorem ownershipErasedDeleteCoreStep :
    coreStep ownershipErasedDeleteState =
      .next ownershipErasedDeleteAfterState := by
  rfl

/-- The erased-sentinel delete discrepancy boundary is explicitly exercised:
the operation is a runtime no-op and still passes through the generic
ownership dispatcher. -/
theorem ownershipErasedDeleteCodeStepPreserves
    (externals : ExternalSpec) :
    SourceMachineOwnershipBelowFrontier ownershipErasedDeleteAfterState :=
  ownershipErasedDeleteStateBelowFrontier.codeStep
    (Step.internal (externals := externals) ownershipErasedDeleteCoreStep)

/-- The state-level global exact dispatcher now returns ownership together
with its original non-lockstep path and hereditary compiler relation. -/
theorem deletedObjectSetGlobalStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals deletedObjectSetSourceState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        deletedWritesTargetState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 4
        sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter :=
  deletedObjectSetExactMachineReadyAt.related
    |>.matchCodeStep_of_ready_withOwnership
      deletedObjectSetExactMachineReadyAt rfl
      deletedObjectSetSourceMachineOwnershipBelowFrontier step

/-- A one-declaration program for exercising named invocation after active
code has transferred control to the whole-machine dispatcher. -/
def ownershipNamedProgram : ImpureProgram :=
  { decls := #[firstDecl] }

def ownershipNamedPartialState : MachineState :=
  { program := ownershipNamedProgram
    control := .invokeName `first #[.erased] }

def ownershipNamedPartialAfterState : MachineState :=
  { ownershipNamedPartialState with
    runtime :=
      (alloc ownershipNamedPartialState.runtime
        (.closure `first firstDecl.params.size #[.erased])).1
    control :=
      .yielded
        (.object
          (alloc ownershipNamedPartialState.runtime
            (.closure `first firstDecl.params.size #[.erased])).2) }

theorem ownershipNamedPartialStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipNamedPartialState := by
  exact {
    heap := by
      simpa [ownershipNamedPartialState] using
        HeapOwnershipBelowFrontier.empty
    env := by
      intro fvarId value found
      simp [ownershipNamedPartialState, lookup] at found
    frames := trivial
  }

theorem ownershipNamedPartialArgumentsBelowFrontier :
    HeapLocationsBelowFrontier
      ownershipNamedPartialState.runtime #[.erased].toList := by
  intro location member
  simp at member

/-- The concrete under-application branch allocates a closure from the
published named-call argument and advances the source frontier from zero to
one. -/
theorem ownershipNamedPartialCoreStep :
    coreStep ownershipNamedPartialState =
      .next ownershipNamedPartialAfterState := by
  rfl

theorem ownershipNamedPartialStepOwnershipPreserved :
    SourceMachineOwnershipBelowFrontier
      ownershipNamedPartialAfterState :=
  SourceMachineOwnershipBelowFrontier.invokeNameNext
    (name := `first) (arguments := #[.erased])
    ownershipNamedPartialStateBelowFrontier
    ownershipNamedPartialArgumentsBelowFrontier
    (by simpa [ownershipNamedPartialState] using
      ownershipNamedPartialCoreStep)

def ownershipNamedFullState : MachineState :=
  { program := ownershipNamedProgram
    control := .invokeName `first #[.erased, .erased] }

def ownershipNamedFullAfterState : MachineState :=
  { ownershipNamedFullState with
    env := bind (bind [] x .erased) y .erased
    joins := []
    control := .code (.return x) }

theorem ownershipNamedFullStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipNamedFullState := by
  exact {
    heap := by
      simpa [ownershipNamedFullState] using
        HeapOwnershipBelowFrontier.empty
    env := by
      intro fvarId value found
      simp [ownershipNamedFullState, lookup] at found
    frames := trivial
  }

theorem ownershipNamedFullCoreStep :
    coreStep ownershipNamedFullState =
      .next ownershipNamedFullAfterState := by
  rfl

/-- The full-application branch installs both declaration parameters into a
fresh environment without weakening the complete ownership carrier. -/
theorem ownershipNamedFullStepOwnershipPreserved :
    SourceMachineOwnershipBelowFrontier ownershipNamedFullAfterState :=
  SourceMachineOwnershipBelowFrontier.invokeNameNext
    (name := `first) (arguments := #[.erased, .erased])
    ownershipNamedFullStateBelowFrontier
    (by
      intro location member
      simp at member)
    (by simpa [ownershipNamedFullState] using ownershipNamedFullCoreStep)

theorem ownershipNamedProgramBinderReadyRelated :
    ProgramRelated (BinderReadyShadowCodeRelated 2)
      ownershipNamedProgram ownershipNamedProgram := by
  have relation := deletedPapProgramBinderReadyRelated
  unfold ProgramRelated at relation ⊢
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated 2))
    [firstDecl] [firstDecl]
  change ListRel (DeclRelated (BinderReadyShadowCodeRelated 2))
    [firstDecl, fixtureDecl `main deletedPapBefore]
    [firstDecl, fixtureDecl `main deletedPapAfter] at relation
  cases relation with
  | cons head tail =>
      exact .cons head .nil

theorem ownershipNamedFullExactRelated :
    SomeBinderReadyReachableMachineRelated 2
      ownershipNamedFullState ownershipNamedFullState := by
  have arguments :
      ArrayRel (ValueRel emptyAddressRenaming)
        #[.erased, .erased] #[.erased, .erased] := by
    change ListRel (ValueRel emptyAddressRenaming)
      [.erased, .erased] [.erased, .erased]
    exact .cons .erased (.cons .erased .nil)
  refine ⟨emptyAddressRenaming,
    #[.erased, .erased].toList, #[.erased, .erased].toList,
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [ownershipNamedFullState] using
      ownershipNamedProgramBinderReadyRelated
  · simpa [ownershipNamedFullState] using
      (BinderReadyReachableControlRelated.invokeName
        (fuel := 2) `first arguments)
  · simpa [ownershipNamedFullState] using
      emptyRuntime_shadowRelated_of_roots arguments

/-- State-level exact dispatch combines the paired internal transition with
the concrete source ownership theorem at a genuine full named call. -/
theorem ownershipNamedFullGlobalStepOwnershipPreserved :
    ∃ targetAfter,
      coreStep ownershipNamedFullState = .next targetAfter ∧
      SomeBinderReadyReachableMachineRelated 2
        ownershipNamedFullAfterState targetAfter ∧
      SourceMachineOwnershipBelowFrontier
        ownershipNamedFullAfterState :=
  ownershipNamedFullExactRelated.matchInvokeNameNext_withOwnership
    ownershipNamedFullStateBelowFrontier rfl
    ownershipNamedFullCoreStep

def ownershipNamedCacheRuntime : RuntimeState :=
  { globals := [(`ownershipNamedCached, .erased)] }

def ownershipNamedCacheState : MachineState :=
  { program := { decls := #[] }
    runtime := ownershipNamedCacheRuntime
    control := .invokeName `ownershipNamedCached #[] }

def ownershipNamedCacheAfterState : MachineState :=
  { ownershipNamedCacheState with control := .yielded .erased }

theorem ownershipNamedCacheStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipNamedCacheState := by
  exact {
    heap := by
      constructor
      · intro location cell found
        simp [ownershipNamedCacheState, ownershipNamedCacheRuntime,
          findCell?] at found
      · intro parent cell child found member
        simp [ownershipNamedCacheState, ownershipNamedCacheRuntime,
          findCell?] at found
    env := by
      intro fvarId value found
      simp [ownershipNamedCacheState, lookup] at found
    frames := trivial
  }

theorem ownershipNamedCacheCoreStep :
    coreStep ownershipNamedCacheState =
      .next ownershipNamedCacheAfterState := by
  rfl

/-- The nullary cache-hit path changes only control and remains covered by
the same named-invocation dispatcher. -/
theorem ownershipNamedCacheStepOwnershipPreserved :
    SourceMachineOwnershipBelowFrontier ownershipNamedCacheAfterState :=
  SourceMachineOwnershipBelowFrontier.invokeNameNext
    (name := `ownershipNamedCached) (arguments := #[])
    ownershipNamedCacheStateBelowFrontier
    (by
      intro location member
      simp at member)
    (by simpa [ownershipNamedCacheState] using
      ownershipNamedCacheCoreStep)

/-- A live closure with one fixed argument; applying one more argument enters
the two-parameter `first` declaration. -/
def ownershipValueFullObject : HeapObject :=
  .closure `first firstDecl.params.size #[.erased]

def ownershipValueFullRuntime : RuntimeState :=
  (alloc ({} : RuntimeState) ownershipValueFullObject).1

def ownershipValueFullState : MachineState :=
  { program := ownershipNamedProgram
    runtime := ownershipValueFullRuntime
    control :=
      .invokeValue (.object (.heap 0)) #[.erased] }

def ownershipValueFullAfterState : MachineState :=
  { ownershipValueFullState with
    env := bind (bind [] x .erased) y .erased
    joins := []
    control := .code (.return x) }

theorem ownershipValueFullStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipValueFullState := by
  have fixedBelow :
      HeapLocationsBelowFrontier
        ({} : RuntimeState) #[.erased].toList := by
    intro location member
    simp at member
  exact {
    heap := by
      simpa [ownershipValueFullState, ownershipValueFullRuntime,
        ownershipValueFullObject] using
        (HeapOwnershipBelowFrontier.empty.allocClosure
          #[.erased] fixedBelow `first firstDecl.params.size)
    env := by
      intro fvarId value found
      simp [ownershipValueFullState, lookup] at found
    frames := trivial
  }

theorem ownershipValueFullCoreStep :
    coreStep ownershipValueFullState =
      .next ownershipValueFullAfterState := by
  rfl

/-- Closure application combines the heap-owned fixed argument and the
dynamic control argument before full declaration binding. -/
theorem ownershipValueFullStepOwnershipPreserved :
    SourceMachineOwnershipBelowFrontier ownershipValueFullAfterState :=
  SourceMachineOwnershipBelowFrontier.invokeValueNext
    (function := .object (.heap 0)) (arguments := #[.erased])
    ownershipValueFullStateBelowFrontier
    (by
      intro location member
      simp at member)
    (by simpa [ownershipValueFullState] using
      ownershipValueFullCoreStep)

/-- A closure with no fixed arguments remains under-applied after one
dynamic argument, forcing closure invocation to allocate a second closure. -/
def ownershipValuePartialObject : HeapObject :=
  .closure `first firstDecl.params.size #[]

def ownershipValuePartialRuntime : RuntimeState :=
  (alloc ({} : RuntimeState) ownershipValuePartialObject).1

def ownershipValuePartialState : MachineState :=
  { program := ownershipNamedProgram
    runtime := ownershipValuePartialRuntime
    control :=
      .invokeValue (.object (.heap 0)) #[.erased] }

def ownershipValuePartialAfterState : MachineState :=
  { ownershipValuePartialState with
    runtime :=
      (alloc ownershipValuePartialState.runtime
        (.closure `first firstDecl.params.size #[.erased])).1
    control :=
      .yielded
        (.object
          (alloc ownershipValuePartialState.runtime
            (.closure `first firstDecl.params.size #[.erased])).2) }

theorem ownershipValuePartialStateBelowFrontier :
    SourceMachineOwnershipBelowFrontier ownershipValuePartialState := by
  have fixedBelow :
      HeapLocationsBelowFrontier
        ({} : RuntimeState) #[].toList := by
    intro location member
    simp at member
  exact {
    heap := by
      simpa [ownershipValuePartialState, ownershipValuePartialRuntime,
        ownershipValuePartialObject] using
        (HeapOwnershipBelowFrontier.empty.allocClosure
          #[] fixedBelow `first firstDecl.params.size)
    env := by
      intro fvarId value found
      simp [ownershipValuePartialState, lookup] at found
    frames := trivial
  }

theorem ownershipValuePartialCoreStep :
    coreStep ownershipValuePartialState =
      .next ownershipValuePartialAfterState := by
  rfl

/-- The re-partial-application branch preserves the original closure cell,
allocates its successor at location one, and keeps both below the new
frontier. -/
theorem ownershipValuePartialStepOwnershipPreserved :
    SourceMachineOwnershipBelowFrontier
      ownershipValuePartialAfterState :=
  SourceMachineOwnershipBelowFrontier.invokeValueNext
    (function := .object (.heap 0)) (arguments := #[.erased])
    ownershipValuePartialStateBelowFrontier
    (by
      intro location member
      simp at member)
    (by simpa [ownershipValuePartialState] using
      ownershipValuePartialCoreStep)

theorem ownershipValueFullExactRelated :
    SomeBinderReadyReachableMachineRelated 2
      ownershipValueFullState ownershipValueFullState := by
  have fixed :
      ArrayRel (ValueRel emptyAddressRenaming)
        #[.erased] #[.erased] := by
    change ListRel (ValueRel emptyAddressRenaming)
      [.erased] [.erased]
    exact .cons .erased .nil
  let base : LedgerShadowRuntimeRel emptyAddressRenaming
      ({} : RuntimeState) ({} : RuntimeState)
      [.erased] [.erased] := {
    runtime := emptyRuntime_shadowRelated_of_roots
      (ListRel.cons ValueRel.erased ListRel.nil)
    ledger := TargetAllocationLedger.empty emptyAddressRenaming
  }
  have objects :
      HeapObjectRel emptyAddressRenaming
        ownershipValueFullObject ownershipValueFullObject := by
    exact HeapObjectRel.closure fixed
  let paired := base.allocBoth
    objects
    (by
      intro value member
      apply extra_subset_runtimeRoots
      simpa [ownershipValueFullObject, HeapObject.ownedValues] using member)
    (by
      intro value member
      apply extra_subset_runtimeRoots
      simpa [ownershipValueFullObject, HeapObject.ownedValues] using member)
    false
  have dynamic :
      ArrayRel (ValueRel paired.larger)
        #[.erased] #[.erased] := by
    change ListRel (ValueRel paired.larger)
      [.erased] [.erased]
    exact .cons .erased .nil
  refine ⟨paired.larger,
    [.object (.heap 0), .erased],
    [.object (.heap 0), .erased],
    [], [], ?_, ?_, .nil, ?_⟩
  · simpa [ownershipValueFullState] using
      ownershipNamedProgramBinderReadyRelated
  · have function :
        ValueRel paired.larger
          (.object (.heap 0)) (.object (.heap 0)) := by
      simpa [alloc, ownershipValueFullObject] using paired.values
    simpa [ownershipValueFullState] using
      (BinderReadyReachableControlRelated.invokeValue
        (fuel := 2) function dynamic)
  · simpa [ownershipValueFullState, ownershipValueFullRuntime,
      ownershipValueFullObject, alloc] using paired.runtime.runtime

theorem ownershipValueFullExactReady :
    BinderReadyReachableMachineReadyAt 2
      ownershipValueFullState ownershipValueFullState := by
  apply
    ownershipValueFullExactRelated
      |>.binderReadyReachableMachineReadyAt_of_code
  intro sourceCode control
  simp [ownershipValueFullState] at control

/-- The ownership-strengthened global internal dispatcher now covers its
closure/value branch as well as code, yielded, and named controls. -/
theorem ownershipValueFullGlobalStepOwnershipPreserved
    (externals : ExternalSpec) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        ownershipValueFullState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 2
        ownershipValueFullAfterState targetAfter ∧
      SourceMachineOwnershipBelowFrontier
        ownershipValueFullAfterState :=
  ownershipValueFullExactRelated
    |>.matchNextStep_of_ready_withOwnership
      ownershipValueFullExactReady
      ownershipValueFullStateBelowFrontier
      ownershipValueFullCoreStep

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

/-- The retained local-copy fixture has an empty heap and one erased
environment value, hence a complete source ownership carrier. -/
theorem unsafeInnerSourceMachineOwnershipBelowFrontier :
    SourceMachineOwnershipBelowFrontier unsafeInnerState := by
  apply SourceMachineOwnershipBelowFrontier.ofEnvironment
  · exact {
      heap := by
        simpa [unsafeInnerState] using
          HeapOwnershipBelowFrontier.empty
      env := by
        intro fvarId value found
        simp [unsafeInnerState, liveEnv, Impure.bind, lookup] at found
        cases found.2
        intro location member
        simp at member
    }
  · exact trivial

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

/-- The exact retained local-copy edge also preserves complete source
ownership while binding the already-owned environment value. -/
theorem unsafeInnerExactStepOwnershipPreserved
    (externals : ExternalSpec) {sourceAfter : MachineState}
    (step : Step externals unsafeInnerState sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals unsafeInnerState targetAfter ∧
      SomeBinderReadyReachableMachineRelated 3 sourceAfter targetAfter ∧
      SourceMachineOwnershipBelowFrontier sourceAfter := by
  have sourceOwnership :
      SourceMachineOwnershipBelowFrontier sourceAfter :=
    unsafeInnerSourceMachineOwnershipBelowFrontier.retainedFVarLetStep
      (fvarId := dead)
      (binderName := dead.name)
      (type := objType)
      (function := live)
      (arguments := #[])
      (continuation := .return live)
      (after := sourceAfter)
      (by simpa [unsafeInnerState, deadCopyDecl, letDecl] using step)
  rcases unsafeInnerExactStepPreserved externals step with
    ⟨targetAfter, targetPath, afterRelated⟩
  exact ⟨targetAfter, targetPath, afterRelated, sourceOwnership⟩

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

/-- Program-level accepted row from the actual-pass policy matrix. -/
theorem allocatingCheckedProgramRun :
    nullarySafeShadowProgram? 3 allocatingBeforeProgram =
      some allocatingAfterProgram := by
  simp [nullarySafeShadowProgram?, nullarySafeShadowDecls?,
    nullarySafeShadowDecl?, allocatingBeforeProgram,
    allocatingAfterProgram, fixtureDecl, decl,
    allocatingCheckedRun]

/-- The accepted allocation row reaches the strict compiler-facing package
once its independent source ownership invariant is supplied. -/
theorem allocatingCompilerAdmissibleRun
    (externals : ExternalSpec) :
    ElimDeadCompilerAdmissibleRun externals 3
      allocatingBeforeProgram allocatingAfterProgram #[`main] :=
  ElimDeadCompilerAdmissibleRun.ofChecked
    allocatingBeforeProgramElimDeadWellFormed
    allocatingCheckedProgramRun
    (.source
      (allocatingSourceRuntimeOwnershipInitialInvariant externals))

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
  (allocatingCompilerAdmissibleRun externals).loweringCorrect compatible

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

/-- Checked whole-program form of the closed write chain. -/
theorem closedWritesCheckedProgramRun :
    nullarySafeShadowProgram? 8 closedWritesBeforeProgram =
      some closedWritesAfterProgram := by
  simp [nullarySafeShadowProgram?, nullarySafeShadowDecls?,
    nullarySafeShadowDecl?, closedWritesBeforeProgram,
    closedWritesAfterProgram, fixtureDecl, decl,
    closedWritesCheckedRun]

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
  have ledger :
      TargetAllocationLedger rho target.runtime.nextLocation := by
    rw [targetEmpty]
    exact TargetAllocationLedger.empty rho
  have binding :
      SourceOnlyHeapBinding ledger
        (closedWritesSourceObjectSetState arguments).env dead 0 := {
    read := by
      simp [closedWritesSourceObjectSetState, deletedWriteSourceEnv,
        lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
    sourceOnly := by
      intro rightLocation bounded
      rw [targetEmpty] at bounded
      exact (Nat.not_lt_zero rightLocation bounded).elim
  }
  apply binding.deletedObjectSetReadyAt_of_effect
      (related := runtime)
  · rfl
  · rfl

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
  have ledger :
      TargetAllocationLedger rho target.runtime.nextLocation := by
    rw [targetEmpty]
    exact TargetAllocationLedger.empty rho
  have binding :
      SourceOnlyHeapBinding ledger
        (closedWritesSourceUSizeSetState arguments).env dead 0 := {
    read := by
      simp [closedWritesSourceUSizeSetState, deletedWriteSourceEnv,
        lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
    sourceOnly := by
      intro rightLocation bounded
      rw [targetEmpty] at bounded
      exact (Nat.not_lt_zero rightLocation bounded).elim
  }
  apply binding.deletedUSizeSetReadyAt_of_effect
      (fieldValue := 7) (related := runtime)
  · simp [closedWritesSourceUSizeSetState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl

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
  have ledger :
      TargetAllocationLedger rho target.runtime.nextLocation := by
    rw [targetEmpty]
    exact TargetAllocationLedger.empty rho
  have binding :
      SourceOnlyHeapBinding ledger
        (closedWritesSourceScalarSetState arguments).env dead 0 := {
    read := by
      simp [closedWritesSourceScalarSetState, deletedWriteSourceEnv,
        lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
    sourceOnly := by
      intro rightLocation bounded
      rw [targetEmpty] at bounded
      exact (Nat.not_lt_zero rightLocation bounded).elim
  }
  apply binding.deletedScalarSetReadyAt_of_effect
      (fieldValue := .uint8 9)
      (width := 8) (offset := 0) (related := runtime)
  · simp [closedWritesSourceScalarSetState, deletedWriteSourceEnv,
      lookupValue, Impure.bind, lookup, dead, usizeField, scalarField]
  · rfl

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

/-- A zero target frontier makes the source allocation at location `0`
absent from every exact target owner ledger. -/
theorem closedWritesSourceOnlyAtZero
    (target : MachineState)
    (ledger :
      TargetAllocationLedger rho target.runtime.nextLocation)
    (targetEmpty : target.runtime.nextLocation = 0) :
    SourceOnlyUnderTargetLedger ledger 0 := by
  intro rightLocation bounded
  rw [targetEmpty] at bounded
  exact (Nat.not_lt_zero rightLocation bounded).elim

/-- Ledger-aligned readiness for the deleted object-field write. The local
heap-shape certificate is combined with the exact owner table carried by the
related machine pair. -/
theorem closedWritesObjectSetPairReady_ledger
    (targetShape : ClosedWritesTargetRuntimeShape target)
    (related : SomeLedgerBinderReadyReachableMachineRelated 8
      (closedWritesSourceObjectSetState arguments) target) :
    LedgerBinderReadyReachableMachineReadyAt 8
      (closedWritesSourceObjectSetState arguments) target := by
  rcases related with
    ⟨rho, ledger, sourceControlRoots, targetControlRoots,
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
        closedWritesObjectSetReady_of_shadowRuntime
          (arguments := arguments) target runtime targetShape.1
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        ledger, programs, ?_, frames, runtime⟩
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

/-- Ledger-aligned readiness for the deleted unboxed-word write. -/
theorem closedWritesUSizeSetPairReady_ledger
    (targetShape : ClosedWritesTargetRuntimeShape target)
    (related : SomeLedgerBinderReadyReachableMachineRelated 8
      (closedWritesSourceUSizeSetState arguments) target) :
    LedgerBinderReadyReachableMachineReadyAt 8
      (closedWritesSourceUSizeSetState arguments) target := by
  rcases related with
    ⟨rho, ledger, sourceControlRoots, targetControlRoots,
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
        closedWritesUSizeSetReady_of_shadowRuntime
          (arguments := arguments) target runtime targetShape.1
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        ledger, programs, ?_, frames, runtime⟩
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

/-- Ledger-aligned readiness for the deleted packed-scalar write. -/
theorem closedWritesScalarSetPairReady_ledger
    (targetShape : ClosedWritesTargetRuntimeShape target)
    (related : SomeLedgerBinderReadyReachableMachineRelated 8
      (closedWritesSourceScalarSetState arguments) target) :
    LedgerBinderReadyReachableMachineReadyAt 8
      (closedWritesSourceScalarSetState arguments) target := by
  rcases related with
    ⟨rho, ledger, sourceControlRoots, targetControlRoots,
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
        closedWritesScalarSetReady_of_shadowRuntime
          (arguments := arguments) target runtime targetShape.1
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        ledger, programs, ?_, frames, runtime⟩
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

/-- Every reachable source state is ready under the exact target ledger
selected by its structural pair. The three write heads consume the ledger
directly; source-only dynamic certificates discharge every other head. -/
theorem closedWritesSourceReachable_pairReady_ledger
    (sourceReachable : ClosedWritesSourceReachable arguments source)
    (targetShape : ClosedWritesTargetRuntimeShape target)
    (related :
      SomeLedgerBinderReadyReachableMachineRelated 8 source target) :
    LedgerBinderReadyReachableMachineReadyAt 8 source target := by
  cases sourceReachable with
  | entry =>
      apply related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesOuterSourceMachineReadyAt arguments)
  | object =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesObjectSourceMachineReadyAt arguments)
  | usize =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesUSizeSourceMachineReadyAt arguments)
  | scalar =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesScalarSourceMachineReadyAt arguments)
  | objectSet =>
      exact closedWritesObjectSetPairReady_ledger targetShape related
  | usizeSet =>
      exact closedWritesUSizeSetPairReady_ledger targetShape related
  | scalarSet =>
      exact closedWritesScalarSetPairReady_ledger targetShape related
  | ret =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (closedWritesReturnSourceMachineReadyAt arguments)
  | yielded =>
      apply related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedWritesSourceYieldedState] at control
  | cached empty =>
      apply related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedWritesSourceCachedState] at control
  | invoking notEmpty =>
      apply related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedWritesSourceInvokingState] at control

theorem closedWritesSourceReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState closedWritesBeforeProgram `main arguments) state) :
    ClosedWritesSourceReachable arguments state := by
  exact path.invariant .entry closedWritesSourceReachable_step

theorem closedWritesTargetReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState closedWritesAfterProgram `main arguments) state) :
    ClosedWritesTargetReachable arguments state := by
  exact path.invariant .entry closedWritesTargetReachable_step

/-- Inductive exact-pair ownership contract for the complete closed fixture.
Related entry arguments may differ, but the target's zero allocation frontier
rules out aliases to the source-only object at every write edge. -/
def closedWritesExactOwnershipContract
    (externals : ExternalSpec) :
    ElimDeadExactOwnershipContract externals 8
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] where
  invariant := fun _ sourceArguments targetArguments source target =>
    ClosedWritesSourceReachable sourceArguments source ∧
      ClosedWritesTargetReachable targetArguments target
  initial := by
    intro entry member sourceArguments targetArguments _argumentsRelated
    have entryEq : entry = `main := by
      simpa using member
    subst entry
    exact ⟨.entry, .entry⟩
  sourcePreserved := by
    rintro entry sourceArguments targetArguments
      sourceBefore sourceAfter targetState
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨closedWritesSourceReachable_step sourceReachable step,
      targetReachable⟩
  targetPreserved := by
    rintro entry sourceArguments targetArguments
      sourceState targetBefore targetAfter
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨sourceReachable,
      closedWritesTargetReachable_step targetReachable step⟩
  ready := by
    rintro entry sourceArguments targetArguments source target
      ⟨sourceReachable, targetReachable⟩ related
    exact closedWritesSourceReachable_pairReady sourceReachable
      (closedWritesTargetReachable_runtimeShape targetReachable)
      related

/-- The complete write fixture also checks the source-owned exact interface.
Its existing readiness proof is ownership-independent, so the generic
migration embeds it directly; later clients may use the supplied carrier. -/
def closedWritesSourceOwnedExactContract
    (externals : ExternalSpec) :
    ElimDeadSourceOwnedExactContract externals 8
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] :=
  (closedWritesExactOwnershipContract externals).sourceOwned

/-- Ledger-exact entry contract for the complete write fixture. This is the
concrete client of the allocation-history-aware checked-pass endpoint. -/
def closedWritesLedgerExactOwnershipContract
    (externals : ExternalSpec) :
    ElimDeadLedgerExactOwnershipContract externals 8
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] where
  invariant := fun _ sourceArguments targetArguments source target =>
    ClosedWritesSourceReachable sourceArguments source ∧
      ClosedWritesTargetReachable targetArguments target
  initial := by
    intro entry member sourceArguments targetArguments _argumentsRelated
    have entryEq : entry = `main := by
      simpa using member
    subst entry
    exact ⟨.entry, .entry⟩
  sourcePreserved := by
    rintro entry sourceArguments targetArguments
      sourceBefore sourceAfter targetState
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨closedWritesSourceReachable_step sourceReachable step,
      targetReachable⟩
  targetPreserved := by
    rintro entry sourceArguments targetArguments
      sourceState targetBefore targetAfter
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨sourceReachable,
      closedWritesTargetReachable_step targetReachable step⟩
  ready := by
    rintro entry sourceArguments targetArguments source target
      ⟨sourceReachable, targetReachable⟩ related
    exact closedWritesSourceReachable_pairReady_ledger sourceReachable
      (closedWritesTargetReachable_runtimeShape targetReachable)
      related

/-- The exact contract supplies the hereditary invariant consumed by the
lower-level semantic endpoint. -/
theorem closedWritesExactRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    ReachableInitialInvariantOn
      (BinderReadyExactRuntimeOwnershipInvariant externals 8)
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] :=
  (closedWritesExactOwnershipContract externals).initialInvariant

/-- The checked pass result, compiler well-formedness, and inductive exact
ownership contract form the strict compiler-facing package. -/
theorem closedWritesCompilerAdmissibleRun
    (externals : ExternalSpec) :
    ElimDeadCompilerAdmissibleRun externals 8
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] :=
  ElimDeadCompilerAdmissibleRun.ofCheckedOwnership
    closedWritesBeforeProgramElimDeadWellFormed
    closedWritesCheckedProgramRun
    (.ofExact (closedWritesExactOwnershipContract externals))

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
  (closedWritesCompilerAdmissibleRun externals).loweringCorrect compatible

/-- The same checked write program reaches whole-program correctness through
the current-state source-owned exact simulation. This exercises source and
target invariant transport together with separately maintained ownership. -/
theorem closedWritesProgramLoweringCorrect_sourceOwnedExact
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 8)
    (sourceCompatible :
      SourceExternalSpecOwnershipCompatible externals) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] :=
  nullarySafeShadowProgram_loweringCorrect_sourceOwnedExact
    closedWritesBeforeProgramElimDeadWellFormed
    closedWritesCheckedProgramRun
    (closedWritesSourceOwnedExactContract externals)
    compatible sourceCompatible

/-- Direct checked-pass correctness for the write fixture through the unified
ledger dispatcher. Unlike the legacy endpoint above, allocation-capable
foreign responses retain their exact target owner history. -/
theorem closedWritesProgramLoweringCorrect_ledgerExact
    (externals : ExternalSpec)
    (compatible :
      LedgerBinderReadyReachableExternalSpecCompatible externals 8) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      closedWritesBeforeProgram closedWritesAfterProgram #[`main] :=
  nullarySafeShadowProgram_loweringCorrect_ledgerExactOwnership
    closedWritesBeforeProgramElimDeadWellFormed
    closedWritesCheckedProgramRun
    (closedWritesLedgerExactOwnershipContract externals)
    compatible

/-- Concrete source states for the closed failed-token reuse fixture.  The
tagged live value makes `reset` return `reuseToken none`; evaluating the
subsequent deleted reuse allocates one fresh source-only constructor. -/
def closedReuseLiveEnv : Env :=
  bind [] live (.object (.tagged 0))

def closedReuseTokenEnv : Env :=
  bind closedReuseLiveEnv reuseTokenVar (.reuseToken none)

def closedReuseArgEnv : Env :=
  bind closedReuseTokenEnv reuseArgVar .erased

def closedReuseAfterLiveCode : LCNF.Code .impure :=
  .let closedReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedReuseAfterResetCode : LCNF.Code .impure :=
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedReuseAfterArgCode : LCNF.Code .impure :=
  .let deadReuseDecl <| .return live

def closedReuseAllocatedObject : ConstructorObject :=
  { tag := oneFieldInfo.cidx
    objectFields := #[.erased]
    usizeFields := #[]
    scalarFields := [] }

def closedReuseAllocation : RuntimeState × ObjectRef :=
  alloc ({} : RuntimeState) (.ctor closedReuseAllocatedObject)

def closedReuseSourceOuterState (arguments : Array Value) : MachineState :=
  { program := closedReuseBeforeProgram
    control := .code closedReuseBefore
    frames := neutralEntryFrames arguments }

def closedReuseSourceResetState (arguments : Array Value) : MachineState :=
  { program := closedReuseBeforeProgram
    control := .code closedReuseAfterLiveCode
    env := closedReuseLiveEnv
    frames := neutralEntryFrames arguments }

def closedReuseSourceArgState (arguments : Array Value) : MachineState :=
  { program := closedReuseBeforeProgram
    control := .code closedReuseAfterResetCode
    env := closedReuseTokenEnv
    frames := neutralEntryFrames arguments }

def closedReuseSourceReuseState (arguments : Array Value) : MachineState :=
  { program := closedReuseBeforeProgram
    control := .code closedReuseAfterArgCode
    env := closedReuseArgEnv
    frames := neutralEntryFrames arguments }

def closedReuseSourceReturnState (arguments : Array Value) : MachineState :=
  { program := closedReuseBeforeProgram
    control := .code (.return live)
    env := bind closedReuseArgEnv dead
      (.object closedReuseAllocation.2)
    runtime := closedReuseAllocation.1
    frames := neutralEntryFrames arguments }

def closedReuseSourceYieldedState (arguments : Array Value) : MachineState :=
  { program := closedReuseBeforeProgram
    control := .yielded (.object (.tagged 0))
    env := bind closedReuseArgEnv dead
      (.object closedReuseAllocation.2)
    runtime := closedReuseAllocation.1
    frames := neutralEntryFrames arguments }

def closedReuseSourceCachedState : MachineState :=
  { program := closedReuseBeforeProgram
    control := .yielded (.object (.tagged 0))
    env := bind closedReuseArgEnv dead
      (.object closedReuseAllocation.2)
    runtime := closedReuseAllocation.1.setGlobal `main
      (.object (.tagged 0)) }

def closedReuseSourceInvokingState
    (arguments : Array Value) : MachineState :=
  { program := closedReuseBeforeProgram
    control := .invokeValue (.object (.tagged 0)) arguments
    env := bind closedReuseArgEnv dead
      (.object closedReuseAllocation.2)
    runtime := closedReuseAllocation.1 }

theorem closedReuseSourceEntryStep (arguments : Array Value) :
    coreStep (initialState closedReuseBeforeProgram `main arguments) =
      .next (closedReuseSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, closedReuseBeforeProgram,
      Program.findDecl?, invokeDecl, closedReuseSourceOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem closedReuseSourceOuterStep (arguments : Array Value) :
    coreStep (closedReuseSourceOuterState arguments) =
      .next (closedReuseSourceResetState arguments) := by
  rfl

theorem closedReuseSourceResetStep (arguments : Array Value) :
    coreStep (closedReuseSourceResetState arguments) =
      .next (closedReuseSourceArgState arguments) := by
  rfl

theorem closedReuseSourceArgStep (arguments : Array Value) :
    coreStep (closedReuseSourceArgState arguments) =
      .next (closedReuseSourceReuseState arguments) := by
  rfl

theorem closedReuseSourceReuseStep (arguments : Array Value) :
    coreStep (closedReuseSourceReuseState arguments) =
      .next (closedReuseSourceReturnState arguments) := by
  have evaluated :
      evalLetValue (closedReuseSourceReuseState arguments)
          deadReuseDecl =
        .ok (closedReuseAllocation.1,
          .value (.object closedReuseAllocation.2)) := by
    simp [evalLetValue, closedReuseSourceReuseState,
      closedReuseAfterArgCode, deadReuseDecl, letDecl,
      closedReuseArgEnv, closedReuseTokenEnv, closedReuseLiveEnv,
      lookupValue, evalArgs, evalArg, Impure.bind, lookup,
      reuseTokenVar, reuseArgVar, reuse, allocCtor, oneFieldInfo,
      closedReuseAllocation,
      closedReuseAllocatedObject, Functor.map, Except.map,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  change coreStep {
      closedReuseSourceReuseState arguments with
      control := .code (.let deadReuseDecl (.return live)) } =
    .next (closedReuseSourceReturnState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedReuseSourceReturnStep (arguments : Array Value) :
    coreStep (closedReuseSourceReturnState arguments) =
      .next (closedReuseSourceYieldedState arguments) := by
  rfl

theorem closedReuseSourceYieldedStepEmpty :
    coreStep (closedReuseSourceYieldedState #[]) =
      .next closedReuseSourceCachedState := by
  rfl

theorem closedReuseSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (closedReuseSourceYieldedState arguments) =
      .next (closedReuseSourceInvokingState arguments) := by
  simp [coreStep, closedReuseSourceYieldedState, neutralEntryFrames,
    notEmpty, closedReuseSourceInvokingState]

/-- Complete finite-state characterization of source executions for the
closed failed-token reuse fixture. -/
inductive ClosedReuseSourceReachable (arguments : Array Value) :
    MachineState → Prop where
  | entry :
      ClosedReuseSourceReachable arguments
        (initialState closedReuseBeforeProgram `main arguments)
  | outer :
      ClosedReuseSourceReachable arguments
        (closedReuseSourceOuterState arguments)
  | reset :
      ClosedReuseSourceReachable arguments
        (closedReuseSourceResetState arguments)
  | argument :
      ClosedReuseSourceReachable arguments
        (closedReuseSourceArgState arguments)
  | reuse :
      ClosedReuseSourceReachable arguments
        (closedReuseSourceReuseState arguments)
  | ret :
      ClosedReuseSourceReachable arguments
        (closedReuseSourceReturnState arguments)
  | yielded :
      ClosedReuseSourceReachable arguments
        (closedReuseSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      ClosedReuseSourceReachable arguments
        closedReuseSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      ClosedReuseSourceReachable arguments
        (closedReuseSourceInvokingState arguments)

theorem closedReuseSourceReachable_step
    (reachable : ClosedReuseSourceReachable arguments before)
    (step : Step externals before after) :
    ClosedReuseSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (closedReuseSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (closedReuseSourceOuterStep arguments) .reset step
  | reset =>
      exact predicate_of_step_next
        (closedReuseSourceResetStep arguments) .argument step
  | argument =>
      exact predicate_of_step_next
        (closedReuseSourceArgStep arguments) .reuse step
  | reuse =>
      exact predicate_of_step_next
        (closedReuseSourceReuseStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (closedReuseSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next
          closedReuseSourceYieldedStepEmpty (.cached rfl) step
      · exact predicate_of_step_next
          (closedReuseSourceYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [closedReuseSourceCachedState, coreStep] at transition
      | external transition response =>
          simp [closedReuseSourceCachedState, coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [closedReuseSourceInvokingState, coreStep, invokeClosure,
            fail] at transition
      | external transition response =>
          simp [closedReuseSourceInvokingState, coreStep, invokeClosure,
            fail] at transition

/-- The retained small-Nat literal is safe under every exact traversal
residual; the literal helper covers both immediate and allocating cases. -/
theorem closedReuseBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 5 state sourceFrameRoots
      closedReuseBefore := by
  unfold closedReuseBefore closedReuseLiveDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_literal

/-- Resetting the tagged live value is runtime-neutral and deterministically
produces a failed reuse token. -/
theorem closedReuseResetSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 5
      (closedReuseSourceResetState arguments) sourceFrameRoots
      closedReuseAfterLiveCode := by
  unfold closedReuseAfterLiveCode closedReuseTokenDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · refine ⟨.reuseToken none, ?_⟩
    simp [evalLetValue, closedReuseSourceResetState,
      closedReuseLiveEnv, lookupValue, Impure.bind, lookup,
      live, reset, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro roots
    trivial

/-- The erased constructor argument is itself a runtime-neutral deleted let. -/
theorem closedReuseArgSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 5
      (closedReuseSourceArgState arguments) sourceFrameRoots
      closedReuseAfterResetCode := by
  unfold closedReuseAfterResetCode closedReuseArgDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

theorem closedReuseDeletedReuseReadyAt
    (arguments : Array Value) (roots : List Value) :
    DeletedReuseReadyAt (closedReuseSourceReuseState arguments)
      roots reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] := by
  apply DeletedReuseReadyAt.none_of_effect
      (values := #[.erased]) (updateHeader := true)
  · simp [closedReuseSourceReuseState, closedReuseArgEnv,
      closedReuseTokenEnv, closedReuseLiveEnv,
      lookupValue, Impure.bind, lookup, reuseTokenVar, reuseArgVar]
  · simp [closedReuseSourceReuseState, closedReuseArgEnv,
      closedReuseTokenEnv, closedReuseLiveEnv,
      evalArgs, evalArg, Impure.bind, lookup,
      reuseTokenVar, reuseArgVar]
    rfl
  · rfl

/-- Retaining this reuse needs no concrete-token ownership proof because its
token lookup is definitionally `none`. -/
theorem closedReuseRetainedReuseReadyAt
    (arguments : Array Value) (roots : List Value) :
    RetainedLetReadyAt (closedReuseSourceReuseState arguments)
      roots deadReuseDecl.value := by
  intro location tokenRead
  simp [closedReuseSourceReuseState, closedReuseArgEnv,
    closedReuseTokenEnv, closedReuseLiveEnv, lookupValue,
    Impure.bind, lookup, reuseTokenVar, reuseArgVar] at tokenRead

/-- Failed-token reuse supports the stronger source-only contract: allocation
freshness preserves arbitrary active and saved-frame roots. -/
theorem closedReuseReuseSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 5
      (closedReuseSourceReuseState arguments) sourceFrameRoots
      closedReuseAfterArgCode := by
  unfold closedReuseAfterArgCode deadReuseDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_ready
  · intro roots
    exact .reuse dead dead.name objType reuseTokenVar oneFieldInfo true
      #[.fvar reuseArgVar]
      (closedReuseDeletedReuseReadyAt
        (arguments := arguments) roots)
  · intro roots
    exact closedReuseRetainedReuseReadyAt
      (arguments := arguments) roots

theorem closedReuseReturnSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 5 state sourceFrameRoots
      (.return live) := by
  intro used remaining final targetCode bounded exact subset static
  simp [ExactShadowCodeRuntimeReadyAt]

theorem closedReuseSourceReachable_ready
    (state : MachineState)
    (reachable : ClosedReuseSourceReachable arguments state) :
    SourceRuntimeOwnershipMachineReadyAt 5 state := by
  cases reachable with
  | entry =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedReuseBefore :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedReuseBeforeSourceRuntimeReadyAt
        (closedReuseSourceOuterState arguments) sourceFrameRoots
        bounded exact subset static
  | reset =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedReuseAfterLiveCode :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedReuseResetSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | argument =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedReuseAfterResetCode :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedReuseArgSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | reuse =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedReuseAfterArgCode :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedReuseReuseSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | ret =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = .return live :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedReuseReturnSourceRuntimeReadyAt
        (closedReuseSourceReturnState arguments) sourceFrameRoots
        bounded exact subset static
  | yielded =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedReuseSourceYieldedState] at control
  | cached empty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedReuseSourceCachedState] at control
  | invoking notEmpty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedReuseSourceInvokingState] at control

/-- Every source state of the closed failed-token fixture satisfies the
strong source-only runtime/ownership contract. -/
theorem closedReuseSourceRuntimeOwnershipMachineInvariant
    (externals : ExternalSpec) (arguments : Array Value) :
    SourceRuntimeOwnershipMachineInvariant externals 5
      (initialState closedReuseBeforeProgram `main arguments) :=
  SourceRuntimeOwnershipMachineInvariant.of_inductive
    (ClosedReuseSourceReachable arguments)
    .entry closedReuseSourceReachable_step
    closedReuseSourceReachable_ready

theorem closedReuseSourceRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    SourceRuntimeOwnershipInitialInvariantOn externals 5
      closedReuseBeforeProgram #[`main] := by
  intro entry member arguments
  have entryEq : entry = `main := by
    simpa using member
  subst entry
  exact
    closedReuseSourceRuntimeOwnershipMachineInvariant externals arguments

theorem closedReuseBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed closedReuseBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique, closedReuseBeforeProgram,
          fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [closedReuseBeforeProgram] at member
      subst declaration
      exact .letE (.letE (.letE (.letE .ret)))
    · intro declaration member
      simp [closedReuseBeforeProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩
        (.letE ⟨.object, trivial⟩
          (.letE ⟨.object, trivial⟩
            (.letE ⟨.object, trivial⟩ .ret)))
  · intro declaration member
    simp [closedReuseBeforeProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl,
      closedReuseBefore, closedReuseLiveDecl, closedReuseTokenDecl,
      closedReuseArgDecl, deadReuseDecl, letDecl, codeBinderIds,
      BinderNamesUnique, ImpureHygiene.paramIds,
      live, reuseTokenVar, reuseArgVar, dead]

theorem closedReuseShadowProgramRun :
    shadowProgram? 5 closedReuseBeforeProgram =
      some closedReuseAfterProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    closedReuseBeforeProgram, closedReuseAfterProgram,
    fixtureDecl, decl, closedReuseShadowRun]

/-- Whole-program correctness for the closed failed-token reset/reuse chain.
The source allocates an unreachable constructor during the deleted reuse;
the target omits the reset/token/argument/reuse suffix and returns the same
tagged value. -/
theorem closedReuseProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 5) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      closedReuseBeforeProgram closedReuseAfterProgram #[`main] :=
  shadowProgram_loweringCorrect_sourceMachineInvariant
    closedReuseBeforeProgramElimDeadWellFormed
    closedReuseShadowProgramRun compatible
    (closedReuseSourceRuntimeOwnershipInitialInvariant externals)

/-- Concrete states for the closed concrete-token branch.  The source-only
constructor lives at location zero, reset converts it into a token, and reuse
overwrites the same unreachable cell. -/
def closedConcreteReuseObjectEnv : Env :=
  bind closedReuseLiveEnv resetObjectVar (.object (.heap 0))

def closedConcreteReuseResetObject : ConstructorObject :=
  { closedReuseAllocatedObject with
    objectFields := #[.object (.tagged 0)] }

def closedConcreteReuseResetCell : HeapCell :=
  { object := .ctor closedConcreteReuseResetObject }

def closedConcreteReuseResetRuntime : RuntimeState :=
  { closedReuseAllocation.1 with
    heap := [(0, closedConcreteReuseResetCell)] }

def closedConcreteReuseTokenEnv : Env :=
  bind closedConcreteReuseObjectEnv reuseTokenVar
    (.reuseToken (some 0))

def closedConcreteReuseArgEnv : Env :=
  bind closedConcreteReuseTokenEnv reuseArgVar .erased

def closedConcreteReuseAfterLiveCode : LCNF.Code .impure :=
  .let closedConcreteReuseObjectDecl <|
  .let closedConcreteReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedConcreteReuseAfterObjectCode : LCNF.Code .impure :=
  .let closedConcreteReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedConcreteReuseAfterResetCode : LCNF.Code .impure :=
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedConcreteReuseAfterArgCode : LCNF.Code .impure :=
  .let deadReuseDecl <| .return live

def closedConcreteReuseSourceOuterState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .code closedConcreteReuseBefore
    frames := neutralEntryFrames arguments }

def closedConcreteReuseSourceObjectState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .code closedConcreteReuseAfterLiveCode
    env := closedReuseLiveEnv
    frames := neutralEntryFrames arguments }

def closedConcreteReuseSourceResetState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .code closedConcreteReuseAfterObjectCode
    env := closedConcreteReuseObjectEnv
    runtime := closedReuseAllocation.1
    frames := neutralEntryFrames arguments }

def closedConcreteReuseSourceArgState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .code closedConcreteReuseAfterResetCode
    env := closedConcreteReuseTokenEnv
    runtime := closedConcreteReuseResetRuntime
    frames := neutralEntryFrames arguments }

def closedConcreteReuseSourceReuseState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .code closedConcreteReuseAfterArgCode
    env := closedConcreteReuseArgEnv
    runtime := closedConcreteReuseResetRuntime
    frames := neutralEntryFrames arguments }

def closedConcreteReuseSourceReturnState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .code (.return live)
    env := bind closedConcreteReuseArgEnv dead (.object (.heap 0))
    runtime := closedReuseAllocation.1
    frames := neutralEntryFrames arguments }

def closedConcreteReuseSourceYieldedState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .yielded (.object (.tagged 0))
    env := bind closedConcreteReuseArgEnv dead (.object (.heap 0))
    runtime := closedReuseAllocation.1
    frames := neutralEntryFrames arguments }

def closedConcreteReuseSourceCachedState : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .yielded (.object (.tagged 0))
    env := bind closedConcreteReuseArgEnv dead (.object (.heap 0))
    runtime := closedReuseAllocation.1.setGlobal `main
      (.object (.tagged 0)) }

def closedConcreteReuseSourceInvokingState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseBeforeProgram
    control := .invokeValue (.object (.tagged 0)) arguments
    env := bind closedConcreteReuseArgEnv dead (.object (.heap 0))
    runtime := closedReuseAllocation.1 }

theorem closedConcreteReuseSourceEntryStep
    (arguments : Array Value) :
    coreStep
        (initialState closedConcreteReuseBeforeProgram `main arguments) =
      .next (closedConcreteReuseSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, closedConcreteReuseBeforeProgram,
      Program.findDecl?, invokeDecl, closedConcreteReuseSourceOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem closedConcreteReuseSourceOuterStep
    (arguments : Array Value) :
    coreStep (closedConcreteReuseSourceOuterState arguments) =
      .next (closedConcreteReuseSourceObjectState arguments) := by
  rfl

theorem closedConcreteReuseSourceObjectStep
    (arguments : Array Value) :
    coreStep (closedConcreteReuseSourceObjectState arguments) =
      .next (closedConcreteReuseSourceResetState arguments) := by
  have evaluated :
      evalLetValue (closedConcreteReuseSourceObjectState arguments)
          closedConcreteReuseObjectDecl =
        .ok (closedReuseAllocation.1,
          .value (.object (.heap 0))) := by
    simp [evalLetValue, closedConcreteReuseSourceObjectState,
      closedConcreteReuseAfterLiveCode,
      closedConcreteReuseObjectDecl, letDecl, evalArgs, evalArg,
      allocCtor, alloc, oneFieldInfo, closedReuseAllocation,
      closedReuseAllocatedObject, Functor.map, Except.map,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  change coreStep {
      closedConcreteReuseSourceObjectState arguments with
      control := .code
        (.let closedConcreteReuseObjectDecl
          closedConcreteReuseAfterObjectCode) } =
    .next (closedConcreteReuseSourceResetState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedConcreteReuseSourceResetStep
    (arguments : Array Value) :
    coreStep (closedConcreteReuseSourceResetState arguments) =
      .next (closedConcreteReuseSourceArgState arguments) := by
  rfl

theorem closedConcreteReuseSourceArgStep
    (arguments : Array Value) :
    coreStep (closedConcreteReuseSourceArgState arguments) =
      .next (closedConcreteReuseSourceReuseState arguments) := by
  rfl

theorem closedConcreteReuseSourceReuseStep
    (arguments : Array Value) :
    coreStep (closedConcreteReuseSourceReuseState arguments) =
      .next (closedConcreteReuseSourceReturnState arguments) := by
  have evaluated :
      evalLetValue (closedConcreteReuseSourceReuseState arguments)
          deadReuseDecl =
        .ok (closedReuseAllocation.1,
          .value (.object (.heap 0))) := by
    simp [evalLetValue, closedConcreteReuseSourceReuseState,
      closedConcreteReuseAfterArgCode, deadReuseDecl, letDecl,
      closedConcreteReuseArgEnv, closedConcreteReuseTokenEnv,
      closedConcreteReuseObjectEnv, closedReuseLiveEnv,
      closedConcreteReuseResetRuntime, closedConcreteReuseResetCell,
      closedConcreteReuseResetObject, lookupValue, evalArgs, evalArg,
      Impure.bind, lookup, reuseTokenVar, reuseArgVar, reuse,
      getLiveCell, setCell, findCell?, replaceCell, alloc,
      oneFieldInfo,
      closedReuseAllocation, closedReuseAllocatedObject,
      Functor.map, Except.map, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  change coreStep {
      closedConcreteReuseSourceReuseState arguments with
      control := .code (.let deadReuseDecl (.return live)) } =
    .next (closedConcreteReuseSourceReturnState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedConcreteReuseSourceReturnStep
    (arguments : Array Value) :
    coreStep (closedConcreteReuseSourceReturnState arguments) =
      .next (closedConcreteReuseSourceYieldedState arguments) := by
  rfl

theorem closedConcreteReuseSourceYieldedStepEmpty :
    coreStep (closedConcreteReuseSourceYieldedState #[]) =
      .next closedConcreteReuseSourceCachedState := by
  rfl

theorem closedConcreteReuseSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (closedConcreteReuseSourceYieldedState arguments) =
      .next (closedConcreteReuseSourceInvokingState arguments) := by
  simp [coreStep, closedConcreteReuseSourceYieldedState,
    neutralEntryFrames, notEmpty,
    closedConcreteReuseSourceInvokingState]

/-- Complete source execution graph for the concrete-token branch. -/
inductive ClosedConcreteReuseSourceReachable
    (arguments : Array Value) : MachineState → Prop where
  | entry :
      ClosedConcreteReuseSourceReachable arguments
        (initialState closedConcreteReuseBeforeProgram `main arguments)
  | outer :
      ClosedConcreteReuseSourceReachable arguments
        (closedConcreteReuseSourceOuterState arguments)
  | object :
      ClosedConcreteReuseSourceReachable arguments
        (closedConcreteReuseSourceObjectState arguments)
  | reset :
      ClosedConcreteReuseSourceReachable arguments
        (closedConcreteReuseSourceResetState arguments)
  | argument :
      ClosedConcreteReuseSourceReachable arguments
        (closedConcreteReuseSourceArgState arguments)
  | reuse :
      ClosedConcreteReuseSourceReachable arguments
        (closedConcreteReuseSourceReuseState arguments)
  | ret :
      ClosedConcreteReuseSourceReachable arguments
        (closedConcreteReuseSourceReturnState arguments)
  | yielded :
      ClosedConcreteReuseSourceReachable arguments
        (closedConcreteReuseSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      ClosedConcreteReuseSourceReachable arguments
        closedConcreteReuseSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      ClosedConcreteReuseSourceReachable arguments
        (closedConcreteReuseSourceInvokingState arguments)

theorem closedConcreteReuseSourceReachable_step
    (reachable :
      ClosedConcreteReuseSourceReachable arguments before)
    (step : Step externals before after) :
    ClosedConcreteReuseSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (closedConcreteReuseSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (closedConcreteReuseSourceOuterStep arguments) .object step
  | object =>
      exact predicate_of_step_next
        (closedConcreteReuseSourceObjectStep arguments) .reset step
  | reset =>
      exact predicate_of_step_next
        (closedConcreteReuseSourceResetStep arguments) .argument step
  | argument =>
      exact predicate_of_step_next
        (closedConcreteReuseSourceArgStep arguments) .reuse step
  | reuse =>
      exact predicate_of_step_next
        (closedConcreteReuseSourceReuseStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (closedConcreteReuseSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next
          closedConcreteReuseSourceYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (closedConcreteReuseSourceYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [closedConcreteReuseSourceCachedState,
            coreStep] at transition
      | external transition response =>
          simp [closedConcreteReuseSourceCachedState,
            coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [closedConcreteReuseSourceInvokingState,
            coreStep, invokeClosure, fail] at transition
      | external transition response =>
          simp [closedConcreteReuseSourceInvokingState,
            coreStep, invokeClosure, fail] at transition

def closedConcreteReuseTargetOuterState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseAfterProgram
    control := .code closedConcreteReuseAfter
    frames := neutralEntryFrames arguments }

def closedConcreteReuseTargetReturnState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseAfterProgram
    control := .code (.return live)
    env := closedReuseLiveEnv
    frames := neutralEntryFrames arguments }

def closedConcreteReuseTargetYieldedState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseAfterProgram
    control := .yielded (.object (.tagged 0))
    env := closedReuseLiveEnv
    frames := neutralEntryFrames arguments }

def closedConcreteReuseTargetCachedState : MachineState :=
  { program := closedConcreteReuseAfterProgram
    control := .yielded (.object (.tagged 0))
    env := closedReuseLiveEnv
    runtime := ({} : RuntimeState).setGlobal `main
      (.object (.tagged 0)) }

def closedConcreteReuseTargetInvokingState
    (arguments : Array Value) : MachineState :=
  { program := closedConcreteReuseAfterProgram
    control := .invokeValue (.object (.tagged 0)) arguments
    env := closedReuseLiveEnv }

theorem closedConcreteReuseTargetEntryStep
    (arguments : Array Value) :
    coreStep
        (initialState closedConcreteReuseAfterProgram `main arguments) =
      .next (closedConcreteReuseTargetOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, closedConcreteReuseAfterProgram,
      Program.findDecl?, invokeDecl, closedConcreteReuseTargetOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem closedConcreteReuseTargetOuterStep
    (arguments : Array Value) :
    coreStep (closedConcreteReuseTargetOuterState arguments) =
      .next (closedConcreteReuseTargetReturnState arguments) := by
  rfl

theorem closedConcreteReuseTargetReturnStep
    (arguments : Array Value) :
    coreStep (closedConcreteReuseTargetReturnState arguments) =
      .next (closedConcreteReuseTargetYieldedState arguments) := by
  rfl

theorem closedConcreteReuseTargetYieldedStepEmpty :
    coreStep (closedConcreteReuseTargetYieldedState #[]) =
      .next closedConcreteReuseTargetCachedState := by
  rfl

theorem closedConcreteReuseTargetYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (closedConcreteReuseTargetYieldedState arguments) =
      .next (closedConcreteReuseTargetInvokingState arguments) := by
  simp [coreStep, closedConcreteReuseTargetYieldedState,
    neutralEntryFrames, notEmpty,
    closedConcreteReuseTargetInvokingState]

inductive ClosedConcreteReuseTargetReachable
    (arguments : Array Value) : MachineState → Prop where
  | entry :
      ClosedConcreteReuseTargetReachable arguments
        (initialState closedConcreteReuseAfterProgram `main arguments)
  | outer :
      ClosedConcreteReuseTargetReachable arguments
        (closedConcreteReuseTargetOuterState arguments)
  | ret :
      ClosedConcreteReuseTargetReachable arguments
        (closedConcreteReuseTargetReturnState arguments)
  | yielded :
      ClosedConcreteReuseTargetReachable arguments
        (closedConcreteReuseTargetYieldedState arguments)
  | cached (empty : arguments = #[]) :
      ClosedConcreteReuseTargetReachable arguments
        closedConcreteReuseTargetCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      ClosedConcreteReuseTargetReachable arguments
        (closedConcreteReuseTargetInvokingState arguments)

theorem closedConcreteReuseTargetReachable_step
    (reachable :
      ClosedConcreteReuseTargetReachable arguments before)
    (step : Step externals before after) :
    ClosedConcreteReuseTargetReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (closedConcreteReuseTargetEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (closedConcreteReuseTargetOuterStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (closedConcreteReuseTargetReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next
          closedConcreteReuseTargetYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (closedConcreteReuseTargetYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [closedConcreteReuseTargetCachedState,
            coreStep] at transition
      | external transition response =>
          simp [closedConcreteReuseTargetCachedState,
            coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [closedConcreteReuseTargetInvokingState,
            coreStep, invokeClosure, fail] at transition
      | external transition response =>
          simp [closedConcreteReuseTargetInvokingState,
            coreStep, invokeClosure, fail] at transition

/-- Every target state has an empty allocation frontier and no active copy of
the concrete `reuse` declaration. -/
def ClosedConcreteReuseTargetRuntimeShape
    (state : MachineState) : Prop :=
  state.runtime.nextLocation = 0 ∧
    ∀ code, state.control = .code code →
      ∀ continuation, code ≠ .let deadReuseDecl continuation

theorem closedConcreteReuseTargetReachable_runtimeShape
    (reachable :
      ClosedConcreteReuseTargetReachable arguments state) :
    ClosedConcreteReuseTargetRuntimeShape state := by
  cases reachable <;>
    simp [ClosedConcreteReuseTargetRuntimeShape, initialState,
      closedConcreteReuseTargetOuterState,
      closedConcreteReuseTargetReturnState,
      closedConcreteReuseTargetYieldedState,
      closedConcreteReuseTargetCachedState,
      closedConcreteReuseTargetInvokingState,
      closedConcreteReuseAfter, closedReuseAfter,
      closedReuseLiveDecl, deadReuseDecl, letDecl,
      RuntimeState.setGlobal, RuntimeState.markPersistent]

theorem closedConcreteReuseResetEffect :
    reset closedReuseAllocation.1 1 (.object (.heap 0)) =
      .ok (closedConcreteReuseResetRuntime,
        .reuseToken (some 0)) := by
  rfl

def closedConcreteReuseResetLocalReady :
    DeletedResetLocalReadyAt
      (closedConcreteReuseSourceResetState arguments)
      1 resetObjectVar := by
  apply DeletedResetLocalReadyAt.of_evalLetValue
      (fvarId := reuseTokenVar)
      (binderName := reuseTokenVar.name)
      (type := objType)
      (nextRuntime := closedConcreteReuseResetRuntime)
      (tokenValue := .reuseToken (some 0))
  rfl

/-- The related target's empty allocation frontier excludes the source-only
constructor from every actual control/frame root decomposition.  Resetting
that cell therefore preserves the reachable runtime. -/
theorem closedConcreteReuseResetReady_of_shadowRuntime
    (target : MachineState)
    (runtime :
      ShadowRuntimeRel rho
        (closedConcreteReuseSourceResetState arguments).runtime
        target.runtime sourceRoots targetRoots)
    (targetEmpty : target.runtime.nextLocation = 0) :
    DeletedResetReadyAt
      (closedConcreteReuseSourceResetState arguments)
      (runtimeRoots
        (closedConcreteReuseSourceResetState arguments).runtime
        sourceRoots)
      1 resetObjectVar := by
  apply
    DeletedResetLocalReadyAt.deletedReadyAt_of_rightNextLocation_zero
      closedConcreteReuseResetLocalReady runtime targetEmpty
      rfl rfl rfl rfl
  intro location bounded
  change 1 ≤ location at bounded
  have notZero : (0 : Nat) ≠ location :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) bounded)
  change findCell? closedConcreteReuseResetRuntime.heap location = none
  simp [closedConcreteReuseResetRuntime, findCell?, notZero]

/-- Source-owned reset readiness. The maintained machine carrier proves that
the successful reset result has no cells at or beyond its fresh frontier, so
the proof no longer inspects the concrete post-reset heap. -/
theorem closedConcreteReuseResetReady_of_sourceOwnership
    (target : MachineState)
    (runtime :
      ShadowRuntimeRel rho
        (closedConcreteReuseSourceResetState arguments).runtime
        target.runtime sourceRoots targetRoots)
    (targetEmpty : target.runtime.nextLocation = 0)
    (ownership :
      SourceMachineOwnershipBelowFrontier
        (closedConcreteReuseSourceResetState arguments)) :
    DeletedResetReadyAt
      (closedConcreteReuseSourceResetState arguments)
      (runtimeRoots
        (closedConcreteReuseSourceResetState arguments).runtime
        sourceRoots)
      1 resetObjectVar := by
  exact
    (closedConcreteReuseResetLocalReady
      (arguments := arguments))
      |>.deletedReadyAt_of_rightNextLocation_zero_withOwnership
        runtime targetEmpty ownership rfl rfl rfl

/-- The exact pair supplies both the deleted reset certificate and the saved
frame roots selected by the compiler residual. -/
theorem closedConcreteReuseResetPairReady
    (targetShape : ClosedConcreteReuseTargetRuntimeShape target)
    (related : SomeBinderReadyReachableMachineRelated 6
      (closedConcreteReuseSourceResetState arguments) target) :
    BinderReadyReachableMachineReadyAt 6
      (closedConcreteReuseSourceResetState arguments) target := by
  rcases related with
    ⟨rho, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  have sourceControl :
      (closedConcreteReuseSourceResetState arguments).control =
        .code closedConcreteReuseAfterObjectCode := rfl
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rename_i used
      rcases graph with
        ⟨remaining, final, bounded, exact, subset, static⟩
      have resetReady :=
        closedConcreteReuseResetReady_of_shadowRuntime
          target runtime targetShape.1
      have removed :
          DeletedLetReadyAt
            (closedConcreteReuseSourceResetState arguments)
            (runtimeRoots
              (closedConcreteReuseSourceResetState arguments).runtime
              (envRootsOn used
                (closedConcreteReuseSourceResetState arguments).env ++
                sourceFrameRoots))
            closedConcreteReuseTokenDecl := by
        unfold closedConcreteReuseTokenDecl letDecl
        exact .reset reuseTokenVar reuseTokenVar.name objType
          1 resetObjectVar (by simpa using resetReady)
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetControl] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            ExactShadowCodeRuntimeReadyAt.let_of_ready
              removed (by trivial)⟩
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

/-- Exact reset-pair readiness through the current source ownership carrier.
Unlike the legacy fixture proof above, post-reset heap freshness follows from
the operationally maintained ownership invariant. -/
theorem closedConcreteReuseResetPairReady_sourceOwned
    (targetShape : ClosedConcreteReuseTargetRuntimeShape target)
    (ownership :
      SourceMachineOwnershipBelowFrontier
        (closedConcreteReuseSourceResetState arguments))
    (related : SomeBinderReadyReachableMachineRelated 6
      (closedConcreteReuseSourceResetState arguments) target) :
    BinderReadyReachableMachineReadyAt 6
      (closedConcreteReuseSourceResetState arguments) target := by
  rcases related with
    ⟨rho, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  have sourceControl :
      (closedConcreteReuseSourceResetState arguments).control =
        .code closedConcreteReuseAfterObjectCode := rfl
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rename_i used
      rcases graph with
        ⟨remaining, final, bounded, exact, subset, static⟩
      have resetReady :=
        closedConcreteReuseResetReady_of_sourceOwnership
          target runtime targetShape.1 ownership
      have removed :
          DeletedLetReadyAt
            (closedConcreteReuseSourceResetState arguments)
            (runtimeRoots
              (closedConcreteReuseSourceResetState arguments).runtime
              (envRootsOn used
                (closedConcreteReuseSourceResetState arguments).env ++
                sourceFrameRoots))
            closedConcreteReuseTokenDecl := by
        unfold closedConcreteReuseTokenDecl letDecl
        exact .reset reuseTokenVar reuseTokenVar.name objType
          1 resetObjectVar (by simpa using resetReady)
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetControl] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            ExactShadowCodeRuntimeReadyAt.let_of_ready
              removed (by trivial)⟩
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

theorem closedConcreteReuseReady_of_shadowRuntime
    (target : MachineState)
    (runtime :
      ShadowRuntimeRel rho
        (closedConcreteReuseSourceReuseState arguments).runtime
        target.runtime sourceRoots targetRoots)
    (targetEmpty : target.runtime.nextLocation = 0) :
    DeletedReuseReadyAt
      (closedConcreteReuseSourceReuseState arguments)
      (runtimeRoots
        (closedConcreteReuseSourceReuseState arguments).runtime
        sourceRoots)
      reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] := by
  have ledger :
      TargetAllocationLedger rho target.runtime.nextLocation := by
    rw [targetEmpty]
    exact TargetAllocationLedger.empty rho
  have binding :
      SourceOnlyReuseTokenBinding ledger
        (closedConcreteReuseSourceReuseState arguments).env
        reuseTokenVar 0 := {
    read := by
      simp [closedConcreteReuseSourceReuseState,
        closedConcreteReuseArgEnv, closedConcreteReuseTokenEnv,
        closedConcreteReuseObjectEnv, closedReuseLiveEnv,
        lookupValue, Impure.bind, lookup,
        reuseTokenVar, reuseArgVar, resetObjectVar]
    sourceOnly := by
      intro rightLocation bounded
      rw [targetEmpty] at bounded
      exact (Nat.not_lt_zero rightLocation bounded).elim
  }
  apply binding.deletedReuseSomeReadyAt_of_effect
      (values := #[.erased]) (updateHeader := true)
      (related := runtime)
  · simp [closedConcreteReuseSourceReuseState,
      closedConcreteReuseArgEnv, closedConcreteReuseTokenEnv,
      closedConcreteReuseObjectEnv, closedReuseLiveEnv,
      evalArgs, evalArg, Impure.bind, lookup,
      reuseTokenVar, reuseArgVar, resetObjectVar]
    rfl
  · rfl

/-- Exact provenance selects deletion of the concrete reuse because no
reachable target is headed by the same declaration. -/
theorem closedConcreteReusePairReady
    (targetShape : ClosedConcreteReuseTargetRuntimeShape target)
    (related : SomeBinderReadyReachableMachineRelated 6
      (closedConcreteReuseSourceReuseState arguments) target) :
    BinderReadyReachableMachineReadyAt 6
      (closedConcreteReuseSourceReuseState arguments) target := by
  rcases related with
    ⟨rho, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  have sourceControl :
      (closedConcreteReuseSourceReuseState arguments).control =
        .code closedConcreteReuseAfterArgCode := rfl
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rename_i used
      rcases graph with
        ⟨remaining, final, bounded, exact, subset, static⟩
      have decision :
          exact.view.runtimeDecision = .deletedLet :=
        exact.view
          |>.runtimeDecision_eq_deletedLet_of_target_not_same_let
            (targetShape.2 targetCode targetControl)
      have reuseReady :=
        closedConcreteReuseReady_of_shadowRuntime
          target runtime targetShape.1
      have removed :
          DeletedLetReadyAt
            (closedConcreteReuseSourceReuseState arguments)
            (runtimeRoots
              (closedConcreteReuseSourceReuseState arguments).runtime
              (envRootsOn used
                (closedConcreteReuseSourceReuseState arguments).env ++
                sourceFrameRoots))
            deadReuseDecl := by
        unfold deadReuseDecl letDecl
        exact .reuse dead dead.name objType reuseTokenVar
          oneFieldInfo true #[.fvar reuseArgVar]
          (by simpa using reuseReady)
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetControl] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            ExactShadowCodeRuntimeReadyAt.letDeleted
              decision removed⟩
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

theorem closedConcreteReuseBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6 state sourceFrameRoots
      closedConcreteReuseBefore := by
  unfold closedConcreteReuseBefore closedReuseLiveDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_literal

theorem closedConcreteReuseObjectSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6
      (closedConcreteReuseSourceObjectState arguments)
      sourceFrameRoots closedConcreteReuseAfterLiveCode := by
  unfold closedConcreteReuseAfterLiveCode
    closedConcreteReuseObjectDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_constructor
  refine .mk #[.erased] ?_ rfl
  simp [closedConcreteReuseSourceObjectState,
    closedReuseLiveEnv, evalArgs, evalArg]
  rfl

theorem closedConcreteReuseArgSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6
      (closedConcreteReuseSourceArgState arguments)
      sourceFrameRoots closedConcreteReuseAfterResetCode := by
  unfold closedConcreteReuseAfterResetCode closedReuseArgDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

theorem closedConcreteReuseReturnSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6 state sourceFrameRoots
      (.return live) := by
  intro used remaining final targetCode bounded exact subset static
  simp [ExactShadowCodeRuntimeReadyAt]

theorem closedConcreteReuseOuterSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 6
      (closedConcreteReuseSourceOuterState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = closedConcreteReuseBefore :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedConcreteReuseBeforeSourceRuntimeReadyAt
    (closedConcreteReuseSourceOuterState arguments)
    sourceFrameRoots bounded exact subset static

theorem closedConcreteReuseObjectSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 6
      (closedConcreteReuseSourceObjectState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = closedConcreteReuseAfterLiveCode :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedConcreteReuseObjectSourceRuntimeReadyAt
    arguments sourceFrameRoots bounded exact subset static

theorem closedConcreteReuseArgSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 6
      (closedConcreteReuseSourceArgState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = closedConcreteReuseAfterResetCode :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedConcreteReuseArgSourceRuntimeReadyAt
    arguments sourceFrameRoots bounded exact subset static

theorem closedConcreteReuseReturnSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 6
      (closedConcreteReuseSourceReturnState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = .return live :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedConcreteReuseReturnSourceRuntimeReadyAt
    (closedConcreteReuseSourceReturnState arguments)
    sourceFrameRoots bounded exact subset static

/-- Every related reachable source/target pair has the exact dynamic
certificate selected by its compiler residual. -/
theorem closedConcreteReuseSourceReachable_pairReady
    (sourceReachable :
      ClosedConcreteReuseSourceReachable arguments source)
    (targetShape : ClosedConcreteReuseTargetRuntimeShape target)
    (related :
      SomeBinderReadyReachableMachineRelated 6 source target) :
    BinderReadyReachableMachineReadyAt 6 source target := by
  cases sourceReachable with
  | entry =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedConcreteReuseOuterSourceMachineReadyAt arguments)
  | object =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedConcreteReuseObjectSourceMachineReadyAt arguments)
  | reset =>
      exact closedConcreteReuseResetPairReady targetShape related
  | argument =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedConcreteReuseArgSourceMachineReadyAt arguments)
  | reuse =>
      exact closedConcreteReusePairReady targetShape related
  | ret =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedConcreteReuseReturnSourceMachineReadyAt arguments)
  | yielded =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedConcreteReuseSourceYieldedState] at control
  | cached empty =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedConcreteReuseSourceCachedState] at control
  | invoking notEmpty =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedConcreteReuseSourceInvokingState] at control

/-- Source-owned readiness for every state in the concrete-token execution
graph. The reset head consumes the maintained machine ownership carrier;
all other heads retain their existing local exact-readiness proofs. -/
theorem closedConcreteReuseSourceReachable_pairReady_sourceOwned
    (sourceReachable :
      ClosedConcreteReuseSourceReachable arguments source)
    (targetShape : ClosedConcreteReuseTargetRuntimeShape target)
    (ownership : SourceMachineOwnershipBelowFrontier source)
    (related :
      SomeBinderReadyReachableMachineRelated 6 source target) :
    BinderReadyReachableMachineReadyAt 6 source target := by
  cases sourceReachable with
  | entry =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedConcreteReuseOuterSourceMachineReadyAt arguments)
  | object =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedConcreteReuseObjectSourceMachineReadyAt arguments)
  | reset =>
      exact closedConcreteReuseResetPairReady_sourceOwned
        targetShape ownership related
  | argument =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedConcreteReuseArgSourceMachineReadyAt arguments)
  | reuse =>
      exact closedConcreteReusePairReady targetShape related
  | ret =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedConcreteReuseReturnSourceMachineReadyAt arguments)
  | yielded =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedConcreteReuseSourceYieldedState] at control
  | cached empty =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedConcreteReuseSourceCachedState] at control
  | invoking notEmpty =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedConcreteReuseSourceInvokingState] at control

theorem closedConcreteReuseSourceReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState closedConcreteReuseBeforeProgram `main arguments)
      state) :
    ClosedConcreteReuseSourceReachable arguments state := by
  exact path.invariant .entry
    closedConcreteReuseSourceReachable_step

theorem closedConcreteReuseTargetReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState closedConcreteReuseAfterProgram `main arguments)
      state) :
    ClosedConcreteReuseTargetReachable arguments state := by
  exact path.invariant .entry
    closedConcreteReuseTargetReachable_step

/-- Exact ownership contract for the one-cell reset/reuse branch. -/
def closedConcreteReuseExactOwnershipContract
    (externals : ExternalSpec) :
    ElimDeadExactOwnershipContract externals 6
      closedConcreteReuseBeforeProgram
      closedConcreteReuseAfterProgram #[`main] where
  invariant := fun _ sourceArguments targetArguments source target =>
    ClosedConcreteReuseSourceReachable sourceArguments source ∧
      ClosedConcreteReuseTargetReachable targetArguments target
  initial := by
    intro entry member sourceArguments targetArguments _argumentsRelated
    have entryEq : entry = `main := by
      simpa using member
    subst entry
    exact ⟨.entry, .entry⟩
  sourcePreserved := by
    rintro entry sourceArguments targetArguments
      sourceBefore sourceAfter targetState
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨closedConcreteReuseSourceReachable_step
      sourceReachable step, targetReachable⟩
  targetPreserved := by
    rintro entry sourceArguments targetArguments
      sourceState targetBefore targetAfter
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨sourceReachable,
      closedConcreteReuseTargetReachable_step
        targetReachable step⟩
  ready := by
    rintro entry sourceArguments targetArguments source target
      ⟨sourceReachable, targetReachable⟩ related
    exact closedConcreteReuseSourceReachable_pairReady
      sourceReachable
      (closedConcreteReuseTargetReachable_runtimeShape
        targetReachable)
      related

/-- Direct source-owned exact contract for the one-cell reset/reuse branch.
The rectangular execution-graph invariant remains purely static; concrete
source heap/environment/frame ownership is supplied by the operational
simulation exactly when reset readiness needs it. -/
def closedConcreteReuseSourceOwnedExactContract
    (externals : ExternalSpec) :
    ElimDeadSourceOwnedExactContract externals 6
      closedConcreteReuseBeforeProgram
      closedConcreteReuseAfterProgram #[`main] where
  invariant := fun _ sourceArguments targetArguments source target =>
    ClosedConcreteReuseSourceReachable sourceArguments source ∧
      ClosedConcreteReuseTargetReachable targetArguments target
  initial := by
    intro entry member sourceArguments targetArguments _argumentsRelated
    have entryEq : entry = `main := by
      simpa using member
    subst entry
    exact ⟨.entry, .entry⟩
  sourcePreserved := by
    rintro entry sourceArguments targetArguments
      sourceBefore sourceAfter targetState
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨closedConcreteReuseSourceReachable_step
      sourceReachable step, targetReachable⟩
  targetPreserved := by
    rintro entry sourceArguments targetArguments
      sourceState targetBefore targetAfter
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨sourceReachable,
      closedConcreteReuseTargetReachable_step
        targetReachable step⟩
  ready := by
    rintro entry sourceArguments targetArguments source target
      ⟨sourceReachable, targetReachable⟩ ownership related
    exact closedConcreteReuseSourceReachable_pairReady_sourceOwned
      sourceReachable
      (closedConcreteReuseTargetReachable_runtimeShape
        targetReachable)
      ownership related

theorem closedConcreteReuseExactRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    ReachableInitialInvariantOn
      (BinderReadyExactRuntimeOwnershipInvariant externals 6)
      closedConcreteReuseBeforeProgram
      closedConcreteReuseAfterProgram #[`main] :=
  (closedConcreteReuseExactOwnershipContract externals).initialInvariant

theorem closedConcreteReuseBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed
      closedConcreteReuseBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique,
          closedConcreteReuseBeforeProgram, fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [closedConcreteReuseBeforeProgram] at member
      subst declaration
      exact .letE (.letE (.letE (.letE (.letE .ret))))
    · intro declaration member
      simp [closedConcreteReuseBeforeProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩
        (.letE ⟨.object, trivial⟩
          (.letE ⟨.object, trivial⟩
            (.letE ⟨.object, trivial⟩
              (.letE ⟨.object, trivial⟩ .ret))))
  · intro declaration member
    simp [closedConcreteReuseBeforeProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl,
      closedConcreteReuseBefore, closedReuseLiveDecl,
      closedConcreteReuseObjectDecl,
      closedConcreteReuseTokenDecl, closedReuseArgDecl,
      deadReuseDecl, letDecl, codeBinderIds,
      BinderNamesUnique, ImpureHygiene.paramIds,
      live, resetObjectVar, reuseTokenVar, reuseArgVar, dead]

theorem closedConcreteReuseShadowProgramRun :
    shadowProgram? 6 closedConcreteReuseBeforeProgram =
      some closedConcreteReuseAfterProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    closedConcreteReuseBeforeProgram,
    closedConcreteReuseAfterProgram,
    fixtureDecl, decl, closedConcreteReuseShadowRun]

/-- Checked whole-program reset/reuse result. -/
theorem closedConcreteReuseCheckedProgramRun :
    nullarySafeShadowProgram? 6 closedConcreteReuseBeforeProgram =
      some closedConcreteReuseAfterProgram := by
  simp [nullarySafeShadowProgram?, nullarySafeShadowDecls?,
    nullarySafeShadowDecl?, closedConcreteReuseBeforeProgram,
    closedConcreteReuseAfterProgram, fixtureDecl, decl,
    closedConcreteReuseCheckedRun]

/-- Strict compiler package for the one-cell concrete-token branch. -/
theorem closedConcreteReuseCompilerAdmissibleRun
    (externals : ExternalSpec) :
    ElimDeadCompilerAdmissibleRun externals 6
      closedConcreteReuseBeforeProgram
      closedConcreteReuseAfterProgram #[`main] :=
  ElimDeadCompilerAdmissibleRun.ofCheckedOwnership
    closedConcreteReuseBeforeProgramElimDeadWellFormed
    closedConcreteReuseCheckedProgramRun
    (.ofExact
      (closedConcreteReuseExactOwnershipContract externals))

/-- Whole-program semantic correctness for the closed concrete-token branch.
The source allocates, resets, and reuses one compiler-owned cell; the target
omits the entire dead suffix while preserving every observable root. -/
theorem closedConcreteReuseProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 6) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      closedConcreteReuseBeforeProgram
      closedConcreteReuseAfterProgram #[`main] :=
  (closedConcreteReuseCompilerAdmissibleRun
    externals).loweringCorrect compatible

/-- Whole-program correctness for concrete reset/reuse through the direct
source-owned exact interface. The external source-ownership law transports
the same carrier across foreign responses; the local reset edge consumes it
to prove post-reset heap freshness without fixture enumeration. -/
theorem closedConcreteReuseProgramLoweringCorrect_sourceOwnedExact
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 6)
    (sourceCompatible :
      SourceExternalSpecOwnershipCompatible externals) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      closedConcreteReuseBeforeProgram
      closedConcreteReuseAfterProgram #[`main] :=
  nullarySafeShadowProgram_loweringCorrect_sourceOwnedExact
    closedConcreteReuseBeforeProgramElimDeadWellFormed
    closedConcreteReuseCheckedProgramRun
    (closedConcreteReuseSourceOwnedExactContract externals)
    compatible sourceCompatible

/-! ## Closed owned-child reset/reuse correctness -/

def closedOwnedReuseChildEnv : Env :=
  bind closedReuseLiveEnv resetChildVar (.object (.heap 0))

def closedOwnedReuseParentObject : ConstructorObject :=
  { tag := oneFieldInfo.cidx
    objectFields := #[.object (.heap 0)]
    usizeFields := #[]
    scalarFields := [] }

def closedOwnedReuseParentCell : HeapCell :=
  { object := .ctor closedOwnedReuseParentObject }

def closedOwnedReuseParentRuntime : RuntimeState :=
  (alloc closedReuseAllocation.1
    (.ctor closedOwnedReuseParentObject)).1

def closedOwnedReuseObjectEnv : Env :=
  bind closedOwnedReuseChildEnv resetObjectVar (.object (.heap 1))

def closedOwnedReuseClearedParentObject : ConstructorObject :=
  { closedOwnedReuseParentObject with
    objectFields := #[.object (.tagged 0)] }

def closedOwnedReuseClearedParentCell : HeapCell :=
  { object := .ctor closedOwnedReuseClearedParentObject }

def closedOwnedReuseReleasedChildCell : HeapCell :=
  { object := .ctor closedReuseAllocatedObject
    rc := 0
    live := false }

def closedOwnedReuseResetRuntime : RuntimeState :=
  { closedOwnedReuseParentRuntime with
    heap := [
      (1, closedOwnedReuseClearedParentCell),
      (0, closedOwnedReuseReleasedChildCell)] }

def closedOwnedReuseTokenEnv : Env :=
  bind closedOwnedReuseObjectEnv reuseTokenVar
    (.reuseToken (some 1))

def closedOwnedReuseArgEnv : Env :=
  bind closedOwnedReuseTokenEnv reuseArgVar .erased

def closedOwnedReuseFinalRuntime : RuntimeState :=
  { closedOwnedReuseResetRuntime with
    heap := [
      (1, { object := .ctor closedReuseAllocatedObject }),
      (0, closedOwnedReuseReleasedChildCell)] }

def closedOwnedReuseAfterLiveCode : LCNF.Code .impure :=
  .let closedOwnedReuseChildDecl <|
  .let closedOwnedReuseObjectDecl <|
  .let closedOwnedReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedOwnedReuseAfterChildCode : LCNF.Code .impure :=
  .let closedOwnedReuseObjectDecl <|
  .let closedOwnedReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedOwnedReuseAfterObjectCode : LCNF.Code .impure :=
  .let closedOwnedReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedOwnedReuseAfterResetCode : LCNF.Code .impure :=
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def closedOwnedReuseAfterArgCode : LCNF.Code .impure :=
  .let deadReuseDecl <| .return live

def closedOwnedReuseSourceOuterState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .code closedOwnedReuseBefore
    frames := neutralEntryFrames arguments }

def closedOwnedReuseSourceChildState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .code closedOwnedReuseAfterLiveCode
    env := closedReuseLiveEnv
    frames := neutralEntryFrames arguments }

def closedOwnedReuseSourceObjectState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .code closedOwnedReuseAfterChildCode
    env := closedOwnedReuseChildEnv
    runtime := closedReuseAllocation.1
    frames := neutralEntryFrames arguments }

def closedOwnedReuseSourceResetState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .code closedOwnedReuseAfterObjectCode
    env := closedOwnedReuseObjectEnv
    runtime := closedOwnedReuseParentRuntime
    frames := neutralEntryFrames arguments }

def closedOwnedReuseSourceArgState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .code closedOwnedReuseAfterResetCode
    env := closedOwnedReuseTokenEnv
    runtime := closedOwnedReuseResetRuntime
    frames := neutralEntryFrames arguments }

def closedOwnedReuseSourceReuseState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .code closedOwnedReuseAfterArgCode
    env := closedOwnedReuseArgEnv
    runtime := closedOwnedReuseResetRuntime
    frames := neutralEntryFrames arguments }

def closedOwnedReuseSourceReturnState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .code (.return live)
    env := bind closedOwnedReuseArgEnv dead (.object (.heap 1))
    runtime := closedOwnedReuseFinalRuntime
    frames := neutralEntryFrames arguments }

def closedOwnedReuseSourceYieldedState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .yielded (.object (.tagged 0))
    env := bind closedOwnedReuseArgEnv dead (.object (.heap 1))
    runtime := closedOwnedReuseFinalRuntime
    frames := neutralEntryFrames arguments }

def closedOwnedReuseSourceCachedState : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .yielded (.object (.tagged 0))
    env := bind closedOwnedReuseArgEnv dead (.object (.heap 1))
    runtime := closedOwnedReuseFinalRuntime.setGlobal `main
      (.object (.tagged 0)) }

def closedOwnedReuseSourceInvokingState
    (arguments : Array Value) : MachineState :=
  { program := closedOwnedReuseBeforeProgram
    control := .invokeValue (.object (.tagged 0)) arguments
    env := bind closedOwnedReuseArgEnv dead (.object (.heap 1))
    runtime := closedOwnedReuseFinalRuntime }

theorem closedOwnedReuseResetEffect :
    reset closedOwnedReuseParentRuntime 1 (.object (.heap 1)) =
      .ok (closedOwnedReuseResetRuntime,
        .reuseToken (some 1)) := by
  rfl

theorem closedOwnedReuseSourceEntryStep
    (arguments : Array Value) :
    coreStep
        (initialState closedOwnedReuseBeforeProgram `main arguments) =
      .next (closedOwnedReuseSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, closedOwnedReuseBeforeProgram,
      Program.findDecl?, invokeDecl, closedOwnedReuseSourceOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem closedOwnedReuseSourceOuterStep
    (arguments : Array Value) :
    coreStep (closedOwnedReuseSourceOuterState arguments) =
      .next (closedOwnedReuseSourceChildState arguments) := by
  rfl

theorem closedOwnedReuseSourceChildStep
    (arguments : Array Value) :
    coreStep (closedOwnedReuseSourceChildState arguments) =
      .next (closedOwnedReuseSourceObjectState arguments) := by
  have evaluated :
      evalLetValue (closedOwnedReuseSourceChildState arguments)
          closedOwnedReuseChildDecl =
        .ok (closedReuseAllocation.1,
          .value (.object (.heap 0))) := by
    simp [evalLetValue, closedOwnedReuseSourceChildState,
      closedOwnedReuseAfterLiveCode,
      closedOwnedReuseChildDecl, letDecl, evalArgs, evalArg,
      allocCtor, alloc, oneFieldInfo, closedReuseAllocation,
      closedReuseAllocatedObject, Functor.map, Except.map,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  change coreStep {
      closedOwnedReuseSourceChildState arguments with
      control := .code
        (.let closedOwnedReuseChildDecl
          closedOwnedReuseAfterChildCode) } =
    .next (closedOwnedReuseSourceObjectState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedOwnedReuseSourceObjectStep
    (arguments : Array Value) :
    coreStep (closedOwnedReuseSourceObjectState arguments) =
      .next (closedOwnedReuseSourceResetState arguments) := by
  have evaluated :
      evalLetValue (closedOwnedReuseSourceObjectState arguments)
          closedOwnedReuseObjectDecl =
        .ok (closedOwnedReuseParentRuntime,
          .value (.object (.heap 1))) := by
    simp [evalLetValue, closedOwnedReuseSourceObjectState,
      closedOwnedReuseAfterChildCode,
      closedOwnedReuseObjectDecl, letDecl,
      closedOwnedReuseChildEnv, closedReuseLiveEnv,
      evalArgs, evalArg, Impure.bind, lookup,
      resetChildVar, allocCtor, alloc, oneFieldInfo,
      closedOwnedReuseParentRuntime, closedOwnedReuseParentObject,
      closedReuseAllocation, closedReuseAllocatedObject,
      Functor.map, Except.map, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  change coreStep {
      closedOwnedReuseSourceObjectState arguments with
      control := .code
        (.let closedOwnedReuseObjectDecl
          closedOwnedReuseAfterObjectCode) } =
    .next (closedOwnedReuseSourceResetState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedOwnedReuseSourceResetStep
    (arguments : Array Value) :
    coreStep (closedOwnedReuseSourceResetState arguments) =
      .next (closedOwnedReuseSourceArgState arguments) := by
  have evaluated :
      evalLetValue (closedOwnedReuseSourceResetState arguments)
          closedOwnedReuseTokenDecl =
        .ok (closedOwnedReuseResetRuntime,
          .value (.reuseToken (some 1))) := by
    simp only [evalLetValue, closedOwnedReuseTokenDecl, letDecl]
    have objectRead :
        lookupValue
            (closedOwnedReuseSourceResetState arguments).env
            resetObjectVar =
          .ok (.object (.heap 1)) := by
      simp [closedOwnedReuseSourceResetState,
        closedOwnedReuseObjectEnv, closedOwnedReuseChildEnv,
        closedReuseLiveEnv, lookupValue, Impure.bind, lookup,
        resetObjectVar, resetChildVar, live]
    rw [objectRead]
    simp only [Bind.bind, Except.bind]
    simp [closedOwnedReuseSourceResetState,
      closedOwnedReuseResetEffect, Pure.pure, Except.pure]
  change coreStep {
      closedOwnedReuseSourceResetState arguments with
      control := .code
        (.let closedOwnedReuseTokenDecl
          closedOwnedReuseAfterResetCode) } =
    .next (closedOwnedReuseSourceArgState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedOwnedReuseSourceArgStep
    (arguments : Array Value) :
    coreStep (closedOwnedReuseSourceArgState arguments) =
      .next (closedOwnedReuseSourceReuseState arguments) := by
  rfl

theorem closedOwnedReuseSourceReuseStep
    (arguments : Array Value) :
    coreStep (closedOwnedReuseSourceReuseState arguments) =
      .next (closedOwnedReuseSourceReturnState arguments) := by
  have evaluated :
      evalLetValue (closedOwnedReuseSourceReuseState arguments)
          deadReuseDecl =
        .ok (closedOwnedReuseFinalRuntime,
          .value (.object (.heap 1))) := by
    simp [evalLetValue, closedOwnedReuseSourceReuseState,
      closedOwnedReuseAfterArgCode, deadReuseDecl, letDecl,
      closedOwnedReuseArgEnv, closedOwnedReuseTokenEnv,
      closedOwnedReuseObjectEnv, closedOwnedReuseChildEnv,
      closedReuseLiveEnv, closedOwnedReuseResetRuntime,
      closedOwnedReuseClearedParentCell,
      closedOwnedReuseClearedParentObject,
      closedOwnedReuseParentObject,
      closedOwnedReuseReleasedChildCell,
      closedOwnedReuseFinalRuntime,
      lookupValue, evalArgs, evalArg, Impure.bind, lookup,
      reuseTokenVar, reuseArgVar, resetObjectVar, resetChildVar,
      reuse, getLiveCell, setCell, findCell?, replaceCell,
      oneFieldInfo, closedReuseAllocatedObject,
      Functor.map, Except.map, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  change coreStep {
      closedOwnedReuseSourceReuseState arguments with
      control := .code (.let deadReuseDecl (.return live)) } =
    .next (closedOwnedReuseSourceReturnState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedOwnedReuseSourceReturnStep
    (arguments : Array Value) :
    coreStep (closedOwnedReuseSourceReturnState arguments) =
      .next (closedOwnedReuseSourceYieldedState arguments) := by
  rfl

theorem closedOwnedReuseSourceYieldedStepEmpty :
    coreStep (closedOwnedReuseSourceYieldedState #[]) =
      .next closedOwnedReuseSourceCachedState := by
  rfl

theorem closedOwnedReuseSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (closedOwnedReuseSourceYieldedState arguments) =
      .next (closedOwnedReuseSourceInvokingState arguments) := by
  simp [coreStep, closedOwnedReuseSourceYieldedState,
    neutralEntryFrames, notEmpty,
    closedOwnedReuseSourceInvokingState]

/-- Complete source execution graph for the owned-child branch. -/
inductive ClosedOwnedReuseSourceReachable
    (arguments : Array Value) : MachineState → Prop where
  | entry :
      ClosedOwnedReuseSourceReachable arguments
        (initialState closedOwnedReuseBeforeProgram `main arguments)
  | outer :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceOuterState arguments)
  | child :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceChildState arguments)
  | object :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceObjectState arguments)
  | reset :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceResetState arguments)
  | argument :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceArgState arguments)
  | reuse :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceReuseState arguments)
  | ret :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceReturnState arguments)
  | yielded :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      ClosedOwnedReuseSourceReachable arguments
        closedOwnedReuseSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      ClosedOwnedReuseSourceReachable arguments
        (closedOwnedReuseSourceInvokingState arguments)

theorem closedOwnedReuseSourceReachable_step
    (reachable :
      ClosedOwnedReuseSourceReachable arguments before)
    (step : Step externals before after) :
    ClosedOwnedReuseSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (closedOwnedReuseSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (closedOwnedReuseSourceOuterStep arguments) .child step
  | child =>
      exact predicate_of_step_next
        (closedOwnedReuseSourceChildStep arguments) .object step
  | object =>
      exact predicate_of_step_next
        (closedOwnedReuseSourceObjectStep arguments) .reset step
  | reset =>
      exact predicate_of_step_next
        (closedOwnedReuseSourceResetStep arguments) .argument step
  | argument =>
      exact predicate_of_step_next
        (closedOwnedReuseSourceArgStep arguments) .reuse step
  | reuse =>
      exact predicate_of_step_next
        (closedOwnedReuseSourceReuseStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (closedOwnedReuseSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next
          closedOwnedReuseSourceYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (closedOwnedReuseSourceYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [closedOwnedReuseSourceCachedState,
            coreStep] at transition
      | external transition response =>
          simp [closedOwnedReuseSourceCachedState,
            coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [closedOwnedReuseSourceInvokingState,
            coreStep, invokeClosure, fail] at transition
      | external transition response =>
          simp [closedOwnedReuseSourceInvokingState,
            coreStep, invokeClosure, fail] at transition

theorem closedOwnedReuseSourceReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState closedOwnedReuseBeforeProgram `main arguments)
      state) :
    ClosedOwnedReuseSourceReachable arguments state := by
  exact path.invariant .entry closedOwnedReuseSourceReachable_step

/-- The owned-child target is definitionally the already audited one-let
target, so its exact finite graph and empty-frontier shape are reused. -/
theorem closedOwnedReuseTargetReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState closedOwnedReuseAfterProgram `main arguments)
      state) :
    ClosedConcreteReuseTargetReachable arguments state := by
  apply closedConcreteReuseTargetReachable_of_reaches
  simpa [closedOwnedReuseAfterProgram,
    closedConcreteReuseAfterProgram,
    closedOwnedReuseAfter, closedConcreteReuseAfter] using path

/-- Recursive child release changes only source cells that the empty target
frontier proves unreachable.  Both heap rewrites therefore form one
observable runtime frame. -/
def closedOwnedReuseResetLocalReady :
    DeletedResetLocalReadyAt
      (closedOwnedReuseSourceResetState arguments)
      1 resetObjectVar := by
  apply DeletedResetLocalReadyAt.of_evalLetValue
      (fvarId := reuseTokenVar)
      (binderName := reuseTokenVar.name)
      (type := objType)
      (nextRuntime := closedOwnedReuseResetRuntime)
      (tokenValue := .reuseToken (some 1))
  rfl

theorem closedOwnedReuseResetReady_of_shadowRuntime
    (target : MachineState)
    (runtime :
      ShadowRuntimeRel rho
        (closedOwnedReuseSourceResetState arguments).runtime
        target.runtime sourceRoots targetRoots)
    (targetEmpty : target.runtime.nextLocation = 0) :
    DeletedResetReadyAt
      (closedOwnedReuseSourceResetState arguments)
      (runtimeRoots
        (closedOwnedReuseSourceResetState arguments).runtime
        sourceRoots)
      1 resetObjectVar := by
  apply
    DeletedResetLocalReadyAt.deletedReadyAt_of_rightNextLocation_zero
      closedOwnedReuseResetLocalReady runtime targetEmpty
      rfl rfl rfl rfl
  intro location bounded
  change 2 ≤ location at bounded
  have notZero : (0 : Nat) ≠ location :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) bounded)
  have notOne : (1 : Nat) ≠ location :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) bounded)
  change findCell? closedOwnedReuseResetRuntime.heap location = none
  simp [closedOwnedReuseResetRuntime, findCell?,
    notZero, notOne]

theorem closedOwnedReuseResetPairReady
    (targetShape : ClosedConcreteReuseTargetRuntimeShape target)
    (related : SomeBinderReadyReachableMachineRelated 7
      (closedOwnedReuseSourceResetState arguments) target) :
    BinderReadyReachableMachineReadyAt 7
      (closedOwnedReuseSourceResetState arguments) target := by
  rcases related with
    ⟨rho, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  have sourceControl :
      (closedOwnedReuseSourceResetState arguments).control =
        .code closedOwnedReuseAfterObjectCode := rfl
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rename_i used
      rcases graph with
        ⟨remaining, final, bounded, exact, subset, static⟩
      have resetReady :=
        closedOwnedReuseResetReady_of_shadowRuntime
          target runtime targetShape.1
      have removed :
          DeletedLetReadyAt
            (closedOwnedReuseSourceResetState arguments)
            (runtimeRoots
              (closedOwnedReuseSourceResetState arguments).runtime
              (envRootsOn used
                (closedOwnedReuseSourceResetState arguments).env ++
                sourceFrameRoots))
            closedOwnedReuseTokenDecl := by
        unfold closedOwnedReuseTokenDecl letDecl
        exact .reset reuseTokenVar reuseTokenVar.name objType
          1 resetObjectVar (by simpa using resetReady)
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetControl] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            ExactShadowCodeRuntimeReadyAt.let_of_ready
              removed (by trivial)⟩
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

theorem closedOwnedReuseReady_of_shadowRuntime
    (target : MachineState)
    (runtime :
      ShadowRuntimeRel rho
        (closedOwnedReuseSourceReuseState arguments).runtime
        target.runtime sourceRoots targetRoots)
    (targetEmpty : target.runtime.nextLocation = 0) :
    DeletedReuseReadyAt
      (closedOwnedReuseSourceReuseState arguments)
      (runtimeRoots
        (closedOwnedReuseSourceReuseState arguments).runtime
        sourceRoots)
      reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] := by
  have ledger :
      TargetAllocationLedger rho target.runtime.nextLocation := by
    rw [targetEmpty]
    exact TargetAllocationLedger.empty rho
  have binding :
      SourceOnlyReuseTokenBinding ledger
        (closedOwnedReuseSourceReuseState arguments).env
        reuseTokenVar 1 := {
    read := by
      simp [closedOwnedReuseSourceReuseState,
        closedOwnedReuseArgEnv, closedOwnedReuseTokenEnv,
        closedOwnedReuseObjectEnv, closedOwnedReuseChildEnv,
        closedReuseLiveEnv, lookupValue, Impure.bind, lookup,
        reuseTokenVar, reuseArgVar, resetObjectVar, resetChildVar]
    sourceOnly := by
      intro rightLocation bounded
      rw [targetEmpty] at bounded
      exact (Nat.not_lt_zero rightLocation bounded).elim
  }
  apply binding.deletedReuseSomeReadyAt_of_effect
      (values := #[.erased]) (updateHeader := true)
      (related := runtime)
  · simp [closedOwnedReuseSourceReuseState,
      closedOwnedReuseArgEnv, closedOwnedReuseTokenEnv,
      closedOwnedReuseObjectEnv, closedOwnedReuseChildEnv,
      closedReuseLiveEnv, evalArgs, evalArg, Impure.bind, lookup,
      reuseTokenVar, reuseArgVar, resetObjectVar, resetChildVar]
    rfl
  · rfl

theorem closedOwnedReusePairReady
    (targetShape : ClosedConcreteReuseTargetRuntimeShape target)
    (related : SomeBinderReadyReachableMachineRelated 7
      (closedOwnedReuseSourceReuseState arguments) target) :
    BinderReadyReachableMachineReadyAt 7
      (closedOwnedReuseSourceReuseState arguments) target := by
  rcases related with
    ⟨rho, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  have sourceControl :
      (closedOwnedReuseSourceReuseState arguments).control =
        .code closedOwnedReuseAfterArgCode := rfl
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rename_i used
      rcases graph with
        ⟨remaining, final, bounded, exact, subset, static⟩
      have decision :
          exact.view.runtimeDecision = .deletedLet :=
        exact.view
          |>.runtimeDecision_eq_deletedLet_of_target_not_same_let
            (targetShape.2 targetCode targetControl)
      have reuseReady :=
        closedOwnedReuseReady_of_shadowRuntime
          target runtime targetShape.1
      have removed :
          DeletedLetReadyAt
            (closedOwnedReuseSourceReuseState arguments)
            (runtimeRoots
              (closedOwnedReuseSourceReuseState arguments).runtime
              (envRootsOn used
                (closedOwnedReuseSourceReuseState arguments).env ++
                sourceFrameRoots))
            deadReuseDecl := by
        unfold deadReuseDecl letDecl
        exact .reuse dead dead.name objType reuseTokenVar
          oneFieldInfo true #[.fvar reuseArgVar]
          (by simpa using reuseReady)
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetControl] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            ExactShadowCodeRuntimeReadyAt.letDeleted
              decision removed⟩
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

theorem closedOwnedReuseBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 7 state sourceFrameRoots
      closedOwnedReuseBefore := by
  unfold closedOwnedReuseBefore closedReuseLiveDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_literal

theorem closedOwnedReuseChildSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 7
      (closedOwnedReuseSourceChildState arguments)
      sourceFrameRoots closedOwnedReuseAfterLiveCode := by
  unfold closedOwnedReuseAfterLiveCode
    closedOwnedReuseChildDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_constructor
  refine .mk #[.erased] ?_ rfl
  simp [closedOwnedReuseSourceChildState,
    closedReuseLiveEnv, evalArgs, evalArg]
  rfl

theorem closedOwnedReuseObjectSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 7
      (closedOwnedReuseSourceObjectState arguments)
      sourceFrameRoots closedOwnedReuseAfterChildCode := by
  unfold closedOwnedReuseAfterChildCode
    closedOwnedReuseObjectDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_constructor
  refine .mk #[.object (.heap 0)] ?_ rfl
  simp [closedOwnedReuseSourceObjectState,
    closedOwnedReuseChildEnv, closedReuseLiveEnv,
    evalArgs, evalArg, Impure.bind, lookup,
    resetChildVar, live]
  rfl

theorem closedOwnedReuseArgSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 7
      (closedOwnedReuseSourceArgState arguments)
      sourceFrameRoots closedOwnedReuseAfterResetCode := by
  unfold closedOwnedReuseAfterResetCode
    closedReuseArgDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

theorem closedOwnedReuseReturnSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 7 state sourceFrameRoots
      (.return live) := by
  intro used remaining final targetCode bounded exact subset static
  simp [ExactShadowCodeRuntimeReadyAt]

theorem closedOwnedReuseOuterSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 7
      (closedOwnedReuseSourceOuterState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = closedOwnedReuseBefore :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedOwnedReuseBeforeSourceRuntimeReadyAt
    (closedOwnedReuseSourceOuterState arguments)
    sourceFrameRoots bounded exact subset static

theorem closedOwnedReuseChildSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 7
      (closedOwnedReuseSourceChildState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = closedOwnedReuseAfterLiveCode :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedOwnedReuseChildSourceRuntimeReadyAt
    arguments sourceFrameRoots bounded exact subset static

theorem closedOwnedReuseObjectSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 7
      (closedOwnedReuseSourceObjectState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = closedOwnedReuseAfterChildCode :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedOwnedReuseObjectSourceRuntimeReadyAt
    arguments sourceFrameRoots bounded exact subset static

theorem closedOwnedReuseArgSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 7
      (closedOwnedReuseSourceArgState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = closedOwnedReuseAfterResetCode :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedOwnedReuseArgSourceRuntimeReadyAt
    arguments sourceFrameRoots bounded exact subset static

theorem closedOwnedReuseReturnSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 7
      (closedOwnedReuseSourceReturnState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = .return live :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact closedOwnedReuseReturnSourceRuntimeReadyAt
    (closedOwnedReuseSourceReturnState arguments)
    sourceFrameRoots bounded exact subset static

/-- Every reachable related pair carries the dynamic certificate selected by
the exact owned-child compiler residual. -/
theorem closedOwnedReuseSourceReachable_pairReady
    (sourceReachable :
      ClosedOwnedReuseSourceReachable arguments source)
    (targetShape : ClosedConcreteReuseTargetRuntimeShape target)
    (related :
      SomeBinderReadyReachableMachineRelated 7 source target) :
    BinderReadyReachableMachineReadyAt 7 source target := by
  cases sourceReachable with
  | entry =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedOwnedReuseOuterSourceMachineReadyAt arguments)
  | child =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedOwnedReuseChildSourceMachineReadyAt arguments)
  | object =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedOwnedReuseObjectSourceMachineReadyAt arguments)
  | reset =>
      exact closedOwnedReuseResetPairReady targetShape related
  | argument =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedOwnedReuseArgSourceMachineReadyAt arguments)
  | reuse =>
      exact closedOwnedReusePairReady targetShape related
  | ret =>
      exact related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
          (closedOwnedReuseReturnSourceMachineReadyAt arguments)
  | yielded =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedOwnedReuseSourceYieldedState] at control
  | cached empty =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedOwnedReuseSourceCachedState] at control
  | invoking notEmpty =>
      apply related
        |>.binderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedOwnedReuseSourceInvokingState] at control

/-- Exact pair contract for the ownership-sensitive reset/reuse fixture.
The source graph tracks recursive child release and token use, while the
target graph supplies the empty-frontier heap shape that proves the concrete
reuse cell unreachable. -/
def closedOwnedReuseExactOwnershipContract
    (externals : ExternalSpec) :
    ElimDeadExactOwnershipContract externals 7
      closedOwnedReuseBeforeProgram
      closedOwnedReuseAfterProgram #[`main] where
  invariant := fun _ sourceArguments targetArguments source target =>
    ClosedOwnedReuseSourceReachable sourceArguments source ∧
      ClosedConcreteReuseTargetReachable targetArguments target
  initial := by
    intro entry member sourceArguments targetArguments argumentsRelated
    have entryEq : entry = `main := by
      simpa using member
    subst entry
    constructor
    · exact .entry
    · simpa [closedOwnedReuseAfterProgram,
        closedConcreteReuseAfterProgram,
        closedOwnedReuseAfter, closedConcreteReuseAfter] using
        (ClosedConcreteReuseTargetReachable.entry
          (arguments := targetArguments))
  sourcePreserved := by
    rintro entry sourceArguments targetArguments
      sourceBefore sourceAfter targetState
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨closedOwnedReuseSourceReachable_step
      sourceReachable step, targetReachable⟩
  targetPreserved := by
    rintro entry sourceArguments targetArguments
      sourceState targetBefore targetAfter
      ⟨sourceReachable, targetReachable⟩ step
    exact ⟨sourceReachable,
      closedConcreteReuseTargetReachable_step targetReachable step⟩
  ready := by
    rintro entry sourceArguments targetArguments source target
      ⟨sourceReachable, targetReachable⟩ related
    exact closedOwnedReuseSourceReachable_pairReady
      sourceReachable
      (closedConcreteReuseTargetReachable_runtimeShape
        targetReachable)
      related

theorem closedOwnedReuseExactRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    ReachableInitialInvariantOn
      (BinderReadyExactRuntimeOwnershipInvariant externals 7)
      closedOwnedReuseBeforeProgram
      closedOwnedReuseAfterProgram #[`main] := by
  exact
    (closedOwnedReuseExactOwnershipContract
      externals).initialInvariant

theorem closedOwnedReuseBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed
      closedOwnedReuseBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique,
          closedOwnedReuseBeforeProgram, fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [closedOwnedReuseBeforeProgram] at member
      subst declaration
      exact .letE
        (.letE (.letE (.letE (.letE (.letE .ret)))))
    · intro declaration member
      simp [closedOwnedReuseBeforeProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩
        (.letE ⟨.object, trivial⟩
          (.letE ⟨.object, trivial⟩
            (.letE ⟨.object, trivial⟩
              (.letE ⟨.object, trivial⟩
                (.letE ⟨.object, trivial⟩ .ret)))))
  · intro declaration member
    simp [closedOwnedReuseBeforeProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl,
      closedOwnedReuseBefore, closedReuseLiveDecl,
      closedOwnedReuseChildDecl, closedOwnedReuseObjectDecl,
      closedOwnedReuseTokenDecl, closedReuseArgDecl,
      deadReuseDecl, letDecl, codeBinderIds,
      BinderNamesUnique, ImpureHygiene.paramIds,
      live, resetChildVar, resetObjectVar,
      reuseTokenVar, reuseArgVar, dead]

theorem closedOwnedReuseShadowProgramRun :
    shadowProgram? 7 closedOwnedReuseBeforeProgram =
      some closedOwnedReuseAfterProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    closedOwnedReuseBeforeProgram,
    closedOwnedReuseAfterProgram,
    fixtureDecl, decl, closedOwnedReuseShadowRun]

/-- Checked whole-program form of recursive child release and reuse. -/
theorem closedOwnedReuseCheckedProgramRun :
    nullarySafeShadowProgram? 7 closedOwnedReuseBeforeProgram =
      some closedOwnedReuseAfterProgram := by
  simp [nullarySafeShadowProgram?, nullarySafeShadowDecls?,
    nullarySafeShadowDecl?, closedOwnedReuseBeforeProgram,
    closedOwnedReuseAfterProgram, fixtureDecl, decl,
    closedOwnedReuseCheckedRun]

/-- Strict compiler package for owned-child reset/reuse. -/
theorem closedOwnedReuseCompilerAdmissibleRun
    (externals : ExternalSpec) :
    ElimDeadCompilerAdmissibleRun externals 7
      closedOwnedReuseBeforeProgram
      closedOwnedReuseAfterProgram #[`main] :=
  ElimDeadCompilerAdmissibleRun.ofCheckedOwnership
    closedOwnedReuseBeforeProgramElimDeadWellFormed
    closedOwnedReuseCheckedProgramRun
    (.ofExact
      (closedOwnedReuseExactOwnershipContract externals))

theorem closedOwnedReuseSemanticallyAdmissibleRun
    (externals : ExternalSpec) :
    ElimDeadSemanticallyAdmissibleRun externals 7
      closedOwnedReuseBeforeProgram
      closedOwnedReuseAfterProgram #[`main] :=
  (closedOwnedReuseCompilerAdmissibleRun
    externals).toSemanticallyAdmissibleRun

/-- Whole-program correctness for deleted reset/reuse with a real owned
child.  The source recursively releases the child and overwrites the parent;
the target omits the unreachable object graph and returns the same value. -/
theorem closedOwnedReuseProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 7) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      closedOwnedReuseBeforeProgram
      closedOwnedReuseAfterProgram #[`main] :=
  (closedOwnedReuseCompilerAdmissibleRun
    externals).loweringCorrect compatible

/-! ## Closed partial-application and box allocation correctness -/

def closedPapBoxPapArgEnv : Env :=
  bind closedReuseLiveEnv papArgVar .erased

def closedPapBoxPapRuntime : RuntimeState :=
  (alloc ({} : RuntimeState)
    (.closure `first 2 #[.erased])).1

def closedPapBoxPapEnv : Env :=
  bind closedPapBoxPapArgEnv papGarbageVar
    (.object (.heap 0))

def closedPapBoxInputEnv : Env :=
  bind closedPapBoxPapEnv boxInputVar
    (.scalar (.uint64 18446744073709551615))

def closedPapBoxFinalRuntime : RuntimeState :=
  (alloc closedPapBoxPapRuntime
    (.boxed u64Type
      (.scalar (.uint64 18446744073709551615)))).1

def closedPapBoxFinalEnv : Env :=
  bind closedPapBoxInputEnv boxGarbageVar
    (.object (.heap 1))

def closedPapBoxAfterLiveCode : LCNF.Code .impure :=
  .let closedPapBoxPapArgDecl <|
  .let closedPapBoxPapDecl <|
  .let closedPapBoxInputDecl <|
  .let closedPapBoxBoxDecl <|
  .return live

def closedPapBoxAfterPapArgCode : LCNF.Code .impure :=
  .let closedPapBoxPapDecl <|
  .let closedPapBoxInputDecl <|
  .let closedPapBoxBoxDecl <|
  .return live

def closedPapBoxAfterPapCode : LCNF.Code .impure :=
  .let closedPapBoxInputDecl <|
  .let closedPapBoxBoxDecl <|
  .return live

def closedPapBoxAfterInputCode : LCNF.Code .impure :=
  .let closedPapBoxBoxDecl <| .return live

def closedPapBoxSourceOuterState
    (arguments : Array Value) : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .code closedPapBoxBefore
    frames := neutralEntryFrames arguments }

def closedPapBoxSourcePapArgState
    (arguments : Array Value) : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .code closedPapBoxAfterLiveCode
    env := closedReuseLiveEnv
    frames := neutralEntryFrames arguments }

def closedPapBoxSourcePapState
    (arguments : Array Value) : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .code closedPapBoxAfterPapArgCode
    env := closedPapBoxPapArgEnv
    frames := neutralEntryFrames arguments }

def closedPapBoxSourceInputState
    (arguments : Array Value) : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .code closedPapBoxAfterPapCode
    env := closedPapBoxPapEnv
    runtime := closedPapBoxPapRuntime
    frames := neutralEntryFrames arguments }

def closedPapBoxSourceBoxState
    (arguments : Array Value) : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .code closedPapBoxAfterInputCode
    env := closedPapBoxInputEnv
    runtime := closedPapBoxPapRuntime
    frames := neutralEntryFrames arguments }

def closedPapBoxSourceReturnState
    (arguments : Array Value) : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .code (.return live)
    env := closedPapBoxFinalEnv
    runtime := closedPapBoxFinalRuntime
    frames := neutralEntryFrames arguments }

def closedPapBoxSourceYieldedState
    (arguments : Array Value) : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .yielded (.object (.tagged 0))
    env := closedPapBoxFinalEnv
    runtime := closedPapBoxFinalRuntime
    frames := neutralEntryFrames arguments }

def closedPapBoxSourceCachedState : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .yielded (.object (.tagged 0))
    env := closedPapBoxFinalEnv
    runtime := closedPapBoxFinalRuntime.setGlobal `main
      (.object (.tagged 0)) }

def closedPapBoxSourceInvokingState
    (arguments : Array Value) : MachineState :=
  { program := closedPapBoxBeforeProgram
    control := .invokeValue (.object (.tagged 0)) arguments
    env := closedPapBoxFinalEnv
    runtime := closedPapBoxFinalRuntime }

theorem closedPapBoxSourceEntryStep
    (arguments : Array Value) :
    coreStep
        (initialState closedPapBoxBeforeProgram `main arguments) =
      .next (closedPapBoxSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, closedPapBoxBeforeProgram,
      Program.findDecl?, invokeDecl, closedPapBoxSourceOuterState,
      neutralEntryFrames, firstDecl, fixtureDecl, decl,
      bindParams, findGlobal?]

theorem closedPapBoxSourceOuterStep
    (arguments : Array Value) :
    coreStep (closedPapBoxSourceOuterState arguments) =
      .next (closedPapBoxSourcePapArgState arguments) := by
  rfl

theorem closedPapBoxSourcePapArgStep
    (arguments : Array Value) :
    coreStep (closedPapBoxSourcePapArgState arguments) =
      .next (closedPapBoxSourcePapState arguments) := by
  rfl

theorem closedPapBoxSourcePapStep
    (arguments : Array Value) :
    coreStep (closedPapBoxSourcePapState arguments) =
      .next (closedPapBoxSourceInputState arguments) := by
  have evaluated :
      evalLetValue (closedPapBoxSourcePapState arguments)
          closedPapBoxPapDecl =
        .ok (closedPapBoxPapRuntime,
          .value (.object (.heap 0))) := by
    simp [evalLetValue, closedPapBoxSourcePapState,
      closedPapBoxAfterPapArgCode,
      closedPapBoxPapDecl, letDecl,
      closedPapBoxPapArgEnv, closedReuseLiveEnv,
      closedPapBoxBeforeProgram, firstDecl, fixtureDecl, decl,
      Program.findDecl?, evalArgs, evalArg,
      Impure.bind, lookup, papArgVar,
      closedPapBoxPapRuntime, alloc,
      Functor.map, Except.map, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  change coreStep {
      closedPapBoxSourcePapState arguments with
      control := .code
        (.let closedPapBoxPapDecl
          closedPapBoxAfterPapCode) } =
    .next (closedPapBoxSourceInputState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedPapBoxSourceInputStep
    (arguments : Array Value) :
    coreStep (closedPapBoxSourceInputState arguments) =
      .next (closedPapBoxSourceBoxState arguments) := by
  rfl

theorem closedPapBoxSourceBoxStep
    (arguments : Array Value) :
    coreStep (closedPapBoxSourceBoxState arguments) =
      .next (closedPapBoxSourceReturnState arguments) := by
  have evaluated :
      evalLetValue (closedPapBoxSourceBoxState arguments)
          closedPapBoxBoxDecl =
        .ok (closedPapBoxFinalRuntime,
          .value (.object (.heap 1))) := by
    have large :
        ¬(ScalarValue.uint64 18446744073709551615).toUInt64.toNat ≤
          9223372036854775807 := by
      native_decide
    simp [evalLetValue, closedPapBoxSourceBoxState,
      closedPapBoxAfterInputCode,
      closedPapBoxBoxDecl, letDecl,
      closedPapBoxInputEnv, closedPapBoxPapEnv,
      closedPapBoxPapArgEnv, closedReuseLiveEnv,
      lookupValue, Impure.bind, lookup,
      boxInputVar, papGarbageVar, papArgVar,
      box, maxTaggedPayload, large,
      closedPapBoxFinalRuntime, closedPapBoxPapRuntime, alloc,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  change coreStep {
      closedPapBoxSourceBoxState arguments with
      control := .code
        (.let closedPapBoxBoxDecl (.return live)) } =
    .next (closedPapBoxSourceReturnState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem closedPapBoxSourceReturnStep
    (arguments : Array Value) :
    coreStep (closedPapBoxSourceReturnState arguments) =
      .next (closedPapBoxSourceYieldedState arguments) := by
  rfl

theorem closedPapBoxSourceYieldedStepEmpty :
    coreStep (closedPapBoxSourceYieldedState #[]) =
      .next closedPapBoxSourceCachedState := by
  rfl

theorem closedPapBoxSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (closedPapBoxSourceYieldedState arguments) =
      .next (closedPapBoxSourceInvokingState arguments) := by
  simp [coreStep, closedPapBoxSourceYieldedState,
    neutralEntryFrames, notEmpty,
    closedPapBoxSourceInvokingState]

inductive ClosedPapBoxSourceReachable
    (arguments : Array Value) : MachineState → Prop where
  | entry :
      ClosedPapBoxSourceReachable arguments
        (initialState closedPapBoxBeforeProgram `main arguments)
  | outer :
      ClosedPapBoxSourceReachable arguments
        (closedPapBoxSourceOuterState arguments)
  | papArg :
      ClosedPapBoxSourceReachable arguments
        (closedPapBoxSourcePapArgState arguments)
  | pap :
      ClosedPapBoxSourceReachable arguments
        (closedPapBoxSourcePapState arguments)
  | input :
      ClosedPapBoxSourceReachable arguments
        (closedPapBoxSourceInputState arguments)
  | box :
      ClosedPapBoxSourceReachable arguments
        (closedPapBoxSourceBoxState arguments)
  | ret :
      ClosedPapBoxSourceReachable arguments
        (closedPapBoxSourceReturnState arguments)
  | yielded :
      ClosedPapBoxSourceReachable arguments
        (closedPapBoxSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      ClosedPapBoxSourceReachable arguments
        closedPapBoxSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      ClosedPapBoxSourceReachable arguments
        (closedPapBoxSourceInvokingState arguments)

theorem closedPapBoxSourceReachable_step
    (reachable :
      ClosedPapBoxSourceReachable arguments before)
    (step : Step externals before after) :
    ClosedPapBoxSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (closedPapBoxSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (closedPapBoxSourceOuterStep arguments) .papArg step
  | papArg =>
      exact predicate_of_step_next
        (closedPapBoxSourcePapArgStep arguments) .pap step
  | pap =>
      exact predicate_of_step_next
        (closedPapBoxSourcePapStep arguments) .input step
  | input =>
      exact predicate_of_step_next
        (closedPapBoxSourceInputStep arguments) .box step
  | box =>
      exact predicate_of_step_next
        (closedPapBoxSourceBoxStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (closedPapBoxSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next
          closedPapBoxSourceYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (closedPapBoxSourceYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [closedPapBoxSourceCachedState,
            coreStep] at transition
      | external transition response =>
          simp [closedPapBoxSourceCachedState,
            coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [closedPapBoxSourceInvokingState,
            coreStep, invokeClosure, fail] at transition
      | external transition response =>
          simp [closedPapBoxSourceInvokingState,
            coreStep, invokeClosure, fail] at transition

theorem closedPapBoxBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6 state sourceFrameRoots
      closedPapBoxBefore := by
  unfold closedPapBoxBefore closedReuseLiveDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_literal

theorem closedPapBoxPapArgSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6
      (closedPapBoxSourcePapArgState arguments)
      sourceFrameRoots closedPapBoxAfterLiveCode := by
  unfold closedPapBoxAfterLiveCode
    closedPapBoxPapArgDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

theorem closedPapBoxPapReadyAt
    (arguments : Array Value) :
    DeletedPapReadyAt
      (closedPapBoxSourcePapState arguments)
      `first #[.fvar papArgVar] := by
  refine .mk firstDecl #[.erased] ?_ ?_ ?_
  · simp [closedPapBoxSourcePapState,
      closedPapBoxPapArgEnv, closedReuseLiveEnv,
      evalArgs, evalArg, Impure.bind, lookup,
      papArgVar, live]
    rfl
  · rfl
  · simp [firstDecl, decl]

theorem closedPapBoxPapSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6
      (closedPapBoxSourcePapState arguments)
      sourceFrameRoots closedPapBoxAfterPapArgCode := by
  unfold closedPapBoxAfterPapArgCode
    closedPapBoxPapDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_partialApplication
    (closedPapBoxPapReadyAt arguments)

theorem closedPapBoxInputSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6
      (closedPapBoxSourceInputState arguments)
      sourceFrameRoots closedPapBoxAfterPapCode := by
  unfold closedPapBoxAfterPapCode
    closedPapBoxInputDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_literal

theorem closedPapBoxBoxReadyAt
    (arguments : Array Value) :
    DeletedBoxReadyAt
      (closedPapBoxSourceBoxState arguments)
      boxInputVar := by
  apply DeletedBoxReadyAt.scalar
    (.uint64 18446744073709551615)
  simp [closedPapBoxSourceBoxState,
    closedPapBoxInputEnv, closedPapBoxPapEnv,
    closedPapBoxPapArgEnv, closedReuseLiveEnv,
    lookupValue, Impure.bind, lookup,
    boxInputVar, papGarbageVar, papArgVar, live]

theorem closedPapBoxBoxSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6
      (closedPapBoxSourceBoxState arguments)
      sourceFrameRoots closedPapBoxAfterInputCode := by
  unfold closedPapBoxAfterInputCode
    closedPapBoxBoxDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_box
    (closedPapBoxBoxReadyAt arguments)

theorem closedPapBoxReturnSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6 state sourceFrameRoots
      (.return live) := by
  intro used remaining final targetCode bounded exact subset static
  simp [ExactShadowCodeRuntimeReadyAt]

theorem closedPapBoxSourceReachable_ready
    (state : MachineState)
    (reachable : ClosedPapBoxSourceReachable arguments state) :
    SourceRuntimeOwnershipMachineReadyAt 6 state := by
  cases reachable with
  | entry =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedPapBoxBefore :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedPapBoxBeforeSourceRuntimeReadyAt
        (closedPapBoxSourceOuterState arguments)
        sourceFrameRoots bounded exact subset static
  | papArg =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedPapBoxAfterLiveCode :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedPapBoxPapArgSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | pap =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedPapBoxAfterPapArgCode :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedPapBoxPapSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | input =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedPapBoxAfterPapCode :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedPapBoxInputSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | box =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = closedPapBoxAfterInputCode :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedPapBoxBoxSourceRuntimeReadyAt
        arguments sourceFrameRoots bounded exact subset static
  | ret =>
      intro sourceFrameRoots sourceCode frames control
      have codeEq : sourceCode = .return live :=
        Control.code.inj control.symm
      subst sourceCode
      intro used remaining final targetCode bounded exact subset static
      exact closedPapBoxReturnSourceRuntimeReadyAt
        (closedPapBoxSourceReturnState arguments)
        sourceFrameRoots bounded exact subset static
  | yielded =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedPapBoxSourceYieldedState] at control
  | cached empty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedPapBoxSourceCachedState] at control
  | invoking notEmpty =>
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [closedPapBoxSourceInvokingState] at control

theorem closedPapBoxSourceRuntimeOwnershipMachineInvariant
    (externals : ExternalSpec) (arguments : Array Value) :
    SourceRuntimeOwnershipMachineInvariant externals 6
      (initialState closedPapBoxBeforeProgram `main arguments) :=
  SourceRuntimeOwnershipMachineInvariant.of_inductive
    (ClosedPapBoxSourceReachable arguments)
    .entry closedPapBoxSourceReachable_step
    closedPapBoxSourceReachable_ready

theorem closedPapBoxSourceRuntimeOwnershipInitialInvariant
    (externals : ExternalSpec) :
    SourceRuntimeOwnershipInitialInvariantOn externals 6
      closedPapBoxBeforeProgram #[`main] := by
  intro entry member arguments
  have entryEq : entry = `main := by
    simpa using member
  subst entry
  exact closedPapBoxSourceRuntimeOwnershipMachineInvariant
    externals arguments

theorem closedPapBoxBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed closedPapBoxBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique, closedPapBoxBeforeProgram,
          firstDecl, fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [closedPapBoxBeforeProgram] at member
      rcases member with rfl | rfl
      · exact .ret
      · exact .letE
          (.letE (.letE (.letE (.letE .ret))))
    · intro declaration member
      simp [closedPapBoxBeforeProgram] at member
      rcases member with rfl | rfl
      · exact .ret
      · exact .letE ⟨.object, trivial⟩
          (.letE ⟨.object, trivial⟩
            (.letE ⟨.object, trivial⟩
              (.letE ⟨.uint64, trivial⟩
                (.letE ⟨.object, .uint64⟩ .ret))))
  · intro declaration member
    simp [closedPapBoxBeforeProgram] at member
    rcases member with rfl | rfl
    · simp [DeclCodeBinderNamesUnique, firstDecl, decl,
        param, codeBinderIds, BinderNamesUnique,
        ImpureHygiene.paramIds, x, y]
    · simp [DeclCodeBinderNamesUnique, fixtureDecl, decl,
        closedPapBoxBefore, closedReuseLiveDecl,
        closedPapBoxPapArgDecl, closedPapBoxPapDecl,
        closedPapBoxInputDecl, closedPapBoxBoxDecl,
        letDecl, codeBinderIds, BinderNamesUnique,
        ImpureHygiene.paramIds, live, papArgVar,
        papGarbageVar, boxInputVar, boxGarbageVar]

theorem closedPapBoxShadowProgramRun :
    shadowProgram? 6 closedPapBoxBeforeProgram =
      some closedPapBoxAfterProgram := by
  have firstRun : shadowDecl? 6 firstDecl = some firstDecl := by
    simp [shadowDecl?, firstDecl, decl, shadowCode?]
  have mainRun :
      shadowDecl? 6 (fixtureDecl `main closedPapBoxBefore) =
        some (fixtureDecl `main closedPapBoxAfter) := by
    simp [shadowDecl?, fixtureDecl, decl, closedPapBoxShadowRun]
  simp [shadowProgram?, shadowDecls?,
    closedPapBoxBeforeProgram, closedPapBoxAfterProgram,
    firstRun, mainRun]

theorem closedPapBoxSemanticallyAdmissibleRun
    (externals : ExternalSpec) :
    ElimDeadSemanticallyAdmissibleRun externals 6
      closedPapBoxBeforeProgram
      closedPapBoxAfterProgram #[`main] := {
  wellFormed := closedPapBoxBeforeProgramElimDeadWellFormed
  transformed := closedPapBoxShadowProgramRun
  runtime := .source
    (closedPapBoxSourceRuntimeOwnershipInitialInvariant externals)
}

/-- Whole-program correctness for deleting both a heap-allocating partial
application and a heap-backed scalar box.  The source performs both
unobservable allocations; the target omits them and returns the same tagged
literal. -/
theorem closedPapBoxProgramLoweringCorrect
    (externals : ExternalSpec)
    (compatible :
      BinderReadyReachableExternalSpecCompatible externals 6) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      closedPapBoxBeforeProgram closedPapBoxAfterProgram #[`main] :=
  (closedPapBoxSemanticallyAdmissibleRun
    externals).loweringCorrect compatible

/-! ## Checked retained-prefix reset/reuse correctness -/

/-- A constructor layout with one owned field plus non-object storage makes
the source-only allocation definitionally equal to the local nonempty-ledger
regression above. -/
def retainedPrefixReuseObjectDecl : LCNF.LetDecl .impure :=
  letDecl resetObjectVar objType (.ctor closedWritesInfo #[.erased])

/-- The retained heap-backed natural allocates first on both sides.  The
constructor/reset/reuse suffix then allocates and mutates only source
location `1`. -/
def retainedPrefixReuseBefore : LCNF.Code .impure :=
  .let retainedLargeNatDecl <|
  .let retainedPrefixReuseObjectDecl <|
  .let closedConcreteReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def retainedPrefixReuseAfter : LCNF.Code .impure :=
  .let retainedLargeNatDecl <| .return live

def retainedPrefixReuseBeforeProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main retainedPrefixReuseBefore] }

def retainedPrefixReuseAfterProgram : ImpureProgram :=
  { decls := #[fixtureDecl `main retainedPrefixReuseAfter] }

theorem retainedPrefixReuseShadowRun :
    shadowCode? 6 {} retainedPrefixReuseBefore =
      some (retainedPrefixReuseAfter, neutralUsed) := by
  simp [retainedPrefixReuseBefore, retainedPrefixReuseAfter,
    retainedLargeNatDecl, retainedPrefixReuseObjectDecl,
    closedConcreteReuseTokenDecl, closedReuseArgDecl, deadReuseDecl,
    letDecl, neutralUsed, shadowCode?, safeToElim, collectLetValue,
    live, resetObjectVar, reuseTokenVar, reuseArgVar, dead]

theorem retainedPrefixReuseCheckedRun :
    nullarySafeShadowCode? 6 {} retainedPrefixReuseBefore =
      some (retainedPrefixReuseAfter, neutralUsed) := by
  have liveMember : live ∈ ({} : UsedLocals).insert live := by
    native_decide
  have objectAbsent :
      resetObjectVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have tokenAbsent :
      reuseTokenVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have argumentAbsent :
      reuseArgVar ∉ ({} : UsedLocals).insert live := by
    native_decide
  have deadAbsent : dead ∉ ({} : UsedLocals).insert live := by
    native_decide
  simp [nullarySafeShadowCode?, retainedPrefixReuseBefore,
    retainedPrefixReuseAfter, retainedLargeNatDecl,
    retainedPrefixReuseObjectDecl, closedConcreteReuseTokenDecl,
    closedReuseArgDecl, deadReuseDecl, letDecl, neutralUsed,
    safeToElim, isNullaryFap, collectLetValue, collectArgs,
    collectArgList, collectArg, liveMember, objectAbsent,
    tokenAbsent, argumentAbsent, deadAbsent]

def retainedPrefixReuseAfterLiveCode : LCNF.Code .impure :=
  .let retainedPrefixReuseObjectDecl <|
  .let closedConcreteReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def retainedPrefixReuseAfterObjectCode : LCNF.Code .impure :=
  .let closedConcreteReuseTokenDecl <|
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def retainedPrefixReuseAfterResetCode : LCNF.Code .impure :=
  .let closedReuseArgDecl <|
  .let deadReuseDecl <|
  .return live

def retainedPrefixReuseAfterArgCode : LCNF.Code .impure :=
  .let deadReuseDecl <| .return live

def retainedPrefixReuseTokenEnv : Env :=
  bind nonemptyLedgerResetEnv reuseTokenVar
    (.reuseToken (some 1))

def retainedPrefixReuseFinalRuntime : RuntimeState :=
  { nonemptyLedgerResetRuntime with
    heap :=
      [(1, { object := .ctor closedReuseAllocatedObject }),
        (0, { object := .natural 9223372036854775808 })] }

def retainedPrefixReuseSourceOuterState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .code retainedPrefixReuseBefore
    frames := neutralEntryFrames arguments }

def retainedPrefixReuseSourceObjectState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .code retainedPrefixReuseAfterLiveCode
    env := nonemptyLedgerRetainedEnv
    runtime := nonemptyLedgerTargetRuntime
    frames := neutralEntryFrames arguments }

def retainedPrefixReuseSourceResetState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .code retainedPrefixReuseAfterObjectCode
    env := nonemptyLedgerResetEnv
    runtime := nonemptyLedgerSourceRuntime
    frames := neutralEntryFrames arguments }

def retainedPrefixReuseSourceArgState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .code retainedPrefixReuseAfterResetCode
    env := retainedPrefixReuseTokenEnv
    runtime := nonemptyLedgerResetRuntime
    frames := neutralEntryFrames arguments }

def retainedPrefixReuseSourceReuseState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .code retainedPrefixReuseAfterArgCode
    env := nonemptyLedgerReuseEnv
    runtime := nonemptyLedgerResetRuntime
    frames := neutralEntryFrames arguments }

def retainedPrefixReuseSourceReturnState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .code (.return live)
    env := bind nonemptyLedgerReuseEnv dead (.object (.heap 1))
    runtime := retainedPrefixReuseFinalRuntime
    frames := neutralEntryFrames arguments }

def retainedPrefixReuseSourceYieldedState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .yielded (.object (.heap 0))
    env := bind nonemptyLedgerReuseEnv dead (.object (.heap 1))
    runtime := retainedPrefixReuseFinalRuntime
    frames := neutralEntryFrames arguments }

def retainedPrefixReuseSourceCachedState : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .yielded (.object (.heap 0))
    env := bind nonemptyLedgerReuseEnv dead (.object (.heap 1))
    runtime := retainedPrefixReuseFinalRuntime.setGlobal `main
      (.object (.heap 0)) }

def retainedPrefixReuseSourceInvokingState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseBeforeProgram
    control := .invokeValue (.object (.heap 0)) arguments
    env := bind nonemptyLedgerReuseEnv dead (.object (.heap 1))
    runtime := retainedPrefixReuseFinalRuntime }

theorem retainedPrefixReuseSourceEntryStep
    (arguments : Array Value) :
    coreStep
        (initialState retainedPrefixReuseBeforeProgram `main arguments) =
      .next (retainedPrefixReuseSourceOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, retainedPrefixReuseBeforeProgram,
      Program.findDecl?, invokeDecl, retainedPrefixReuseSourceOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem retainedPrefixReuseSourceOuterStep
    (arguments : Array Value) :
    coreStep (retainedPrefixReuseSourceOuterState arguments) =
      .next (retainedPrefixReuseSourceObjectState arguments) := by
  rfl

theorem retainedPrefixReuseSourceObjectStep
    (arguments : Array Value) :
    coreStep (retainedPrefixReuseSourceObjectState arguments) =
      .next (retainedPrefixReuseSourceResetState arguments) := by
  have evaluated :
      evalLetValue (retainedPrefixReuseSourceObjectState arguments)
          retainedPrefixReuseObjectDecl =
        .ok (nonemptyLedgerSourceRuntime,
          .value (.object (.heap 1))) := by
    simp [evalLetValue, retainedPrefixReuseSourceObjectState,
      retainedPrefixReuseAfterLiveCode,
      retainedPrefixReuseObjectDecl, letDecl, evalArgs, evalArg,
      allocCtor, alloc, closedWritesInfo, deletedWriteObject,
      nonemptyLedgerSourceRuntime, nonemptyLedgerTargetRuntime,
      nonemptyLedgerPairedRuntime,
      Functor.map, Except.map, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  change coreStep {
      retainedPrefixReuseSourceObjectState arguments with
      control := .code
        (.let retainedPrefixReuseObjectDecl
          retainedPrefixReuseAfterObjectCode) } =
    .next (retainedPrefixReuseSourceResetState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem retainedPrefixReuseSourceResetStep
    (arguments : Array Value) :
    coreStep (retainedPrefixReuseSourceResetState arguments) =
      .next (retainedPrefixReuseSourceArgState arguments) := by
  rfl

theorem retainedPrefixReuseSourceArgStep
    (arguments : Array Value) :
    coreStep (retainedPrefixReuseSourceArgState arguments) =
      .next (retainedPrefixReuseSourceReuseState arguments) := by
  rfl

theorem retainedPrefixReuseSourceReuseStep
    (arguments : Array Value) :
    coreStep (retainedPrefixReuseSourceReuseState arguments) =
      .next (retainedPrefixReuseSourceReturnState arguments) := by
  have evaluated :
      evalLetValue (retainedPrefixReuseSourceReuseState arguments)
          deadReuseDecl =
        .ok (retainedPrefixReuseFinalRuntime,
          .value (.object (.heap 1))) := by
    simp [evalLetValue, retainedPrefixReuseSourceReuseState,
      retainedPrefixReuseAfterArgCode, deadReuseDecl, letDecl,
      nonemptyLedgerReuseEnv, retainedPrefixReuseTokenEnv,
      nonemptyLedgerResetEnv, nonemptyLedgerRetainedEnv,
      nonemptyLedgerResetRuntime, nonemptyLedgerClearedCell,
      nonemptyLedgerClearedObject, lookupValue, evalArgs, evalArg,
      Impure.bind, lookup, reuseTokenVar, reuseArgVar, reuse,
      getLiveCell, setCell, findCell?, replaceCell, alloc,
      oneFieldInfo, retainedPrefixReuseFinalRuntime,
      closedReuseAllocatedObject,
      nonemptyLedgerSourceRuntime, nonemptyLedgerTargetRuntime,
      nonemptyLedgerPairedRuntime, deletedWriteObject,
      Functor.map, Except.map, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  change coreStep {
      retainedPrefixReuseSourceReuseState arguments with
      control := .code (.let deadReuseDecl (.return live)) } =
    .next (retainedPrefixReuseSourceReturnState arguments)
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]
  rfl

theorem retainedPrefixReuseSourceReturnStep
    (arguments : Array Value) :
    coreStep (retainedPrefixReuseSourceReturnState arguments) =
      .next (retainedPrefixReuseSourceYieldedState arguments) := by
  rfl

theorem retainedPrefixReuseSourceYieldedStepEmpty :
    coreStep (retainedPrefixReuseSourceYieldedState #[]) =
      .next retainedPrefixReuseSourceCachedState := by
  rfl

theorem retainedPrefixReuseSourceYieldedStepNonempty
    (notEmpty : arguments ≠ #[]) :
    coreStep (retainedPrefixReuseSourceYieldedState arguments) =
      .next (retainedPrefixReuseSourceInvokingState arguments) := by
  simp [coreStep, retainedPrefixReuseSourceYieldedState,
    neutralEntryFrames, notEmpty,
    retainedPrefixReuseSourceInvokingState]

inductive RetainedPrefixReuseSourceReachable
    (arguments : Array Value) : MachineState → Prop where
  | entry :
      RetainedPrefixReuseSourceReachable arguments
        (initialState retainedPrefixReuseBeforeProgram `main arguments)
  | outer :
      RetainedPrefixReuseSourceReachable arguments
        (retainedPrefixReuseSourceOuterState arguments)
  | object :
      RetainedPrefixReuseSourceReachable arguments
        (retainedPrefixReuseSourceObjectState arguments)
  | reset :
      RetainedPrefixReuseSourceReachable arguments
        (retainedPrefixReuseSourceResetState arguments)
  | argument :
      RetainedPrefixReuseSourceReachable arguments
        (retainedPrefixReuseSourceArgState arguments)
  | reuse :
      RetainedPrefixReuseSourceReachable arguments
        (retainedPrefixReuseSourceReuseState arguments)
  | ret :
      RetainedPrefixReuseSourceReachable arguments
        (retainedPrefixReuseSourceReturnState arguments)
  | yielded :
      RetainedPrefixReuseSourceReachable arguments
        (retainedPrefixReuseSourceYieldedState arguments)
  | cached (empty : arguments = #[]) :
      RetainedPrefixReuseSourceReachable arguments
        retainedPrefixReuseSourceCachedState
  | invoking (notEmpty : arguments ≠ #[]) :
      RetainedPrefixReuseSourceReachable arguments
        (retainedPrefixReuseSourceInvokingState arguments)

theorem retainedPrefixReuseSourceReachable_step
    (reachable :
      RetainedPrefixReuseSourceReachable arguments before)
    (step : Step externals before after) :
    RetainedPrefixReuseSourceReachable arguments after := by
  cases reachable with
  | entry =>
      exact predicate_of_step_next
        (retainedPrefixReuseSourceEntryStep arguments) .outer step
  | outer =>
      exact predicate_of_step_next
        (retainedPrefixReuseSourceOuterStep arguments) .object step
  | object =>
      exact predicate_of_step_next
        (retainedPrefixReuseSourceObjectStep arguments) .reset step
  | reset =>
      exact predicate_of_step_next
        (retainedPrefixReuseSourceResetStep arguments) .argument step
  | argument =>
      exact predicate_of_step_next
        (retainedPrefixReuseSourceArgStep arguments) .reuse step
  | reuse =>
      exact predicate_of_step_next
        (retainedPrefixReuseSourceReuseStep arguments) .ret step
  | ret =>
      exact predicate_of_step_next
        (retainedPrefixReuseSourceReturnStep arguments) .yielded step
  | yielded =>
      by_cases empty : arguments = #[]
      · subst arguments
        exact predicate_of_step_next
          retainedPrefixReuseSourceYieldedStepEmpty
          (.cached rfl) step
      · exact predicate_of_step_next
          (retainedPrefixReuseSourceYieldedStepNonempty empty)
          (.invoking empty) step
  | cached empty =>
      cases step with
      | internal transition =>
          simp [retainedPrefixReuseSourceCachedState,
            coreStep] at transition
      | external transition response =>
          simp [retainedPrefixReuseSourceCachedState,
            coreStep] at transition
  | invoking notEmpty =>
      cases step with
      | internal transition =>
          simp [retainedPrefixReuseSourceInvokingState,
            retainedPrefixReuseFinalRuntime, nonemptyLedgerResetRuntime,
            nonemptyLedgerSourceRuntime, nonemptyLedgerTargetRuntime,
            nonemptyLedgerPairedRuntime, getLiveCell, findCell?,
            coreStep, invokeClosure, fail] at transition
      | external transition response =>
          simp [retainedPrefixReuseSourceInvokingState,
            retainedPrefixReuseFinalRuntime, nonemptyLedgerResetRuntime,
            nonemptyLedgerSourceRuntime, nonemptyLedgerTargetRuntime,
            nonemptyLedgerPairedRuntime, getLiveCell, findCell?,
            coreStep, invokeClosure, fail] at transition

def retainedPrefixReuseTargetOuterState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseAfterProgram
    control := .code retainedPrefixReuseAfter
    frames := neutralEntryFrames arguments }

def retainedPrefixReuseTargetReturnState
    (arguments : Array Value) : MachineState :=
  { program := retainedPrefixReuseAfterProgram
    control := .code (.return live)
    env := nonemptyLedgerRetainedEnv
    runtime := nonemptyLedgerTargetRuntime
    frames := neutralEntryFrames arguments }

theorem retainedPrefixReuseTargetEntryStep
    (arguments : Array Value) :
    coreStep
        (initialState retainedPrefixReuseAfterProgram `main arguments) =
      .next (retainedPrefixReuseTargetOuterState arguments) := by
  by_cases empty : arguments = #[] <;>
    simp_all [initialState, coreStep, retainedPrefixReuseAfterProgram,
      Program.findDecl?, invokeDecl, retainedPrefixReuseTargetOuterState,
      neutralEntryFrames, fixtureDecl, decl, bindParams, findGlobal?]

theorem retainedPrefixReuseTargetOuterStep
    (arguments : Array Value) :
    coreStep (retainedPrefixReuseTargetOuterState arguments) =
      .next (retainedPrefixReuseTargetReturnState arguments) := by
  rfl

/-- Control/frame phases possible after the target's sole retained
allocation.  The heap-object witness is carried only while it is needed to
show that applying the returned natural cannot re-enter executable code;
the cache-terminal phase deliberately drops it. -/
inductive RetainedPrefixReuseTargetAllocatedControl
    (target : MachineState) : Prop where
  | ret (arguments : Array Value)
      (control : target.control = .code (.return live))
      (frames : target.frames = neutralEntryFrames arguments)
      (objectRead :
        (findCell? target.runtime.heap 0).map HeapCell.object =
          some (.natural 9223372036854775808))
  | yielded (arguments : Array Value)
      (control : target.control = .yielded (.object (.heap 0)))
      (frames : target.frames = neutralEntryFrames arguments)
      (objectRead :
        (findCell? target.runtime.heap 0).map HeapCell.object =
          some (.natural 9223372036854775808))
  | cached
      (control : target.control = .yielded (.object (.heap 0)))
      (frames : target.frames = [])
  | invoking (arguments : Array Value)
      (control : target.control =
        .invokeValue (.object (.heap 0)) arguments)
      (frames : target.frames = [])
      (objectRead :
        (findCell? target.runtime.heap 0).map HeapCell.object =
          some (.natural 9223372036854775808))

/-- Static post-allocation facts used by the deleted reset/reuse suffix.
Unlike the former exact-state graph, this records only the retained live
binding, allocation frontier, and the control/frame phase needed to prove
that no later target step allocates. -/
structure RetainedPrefixReuseTargetAllocatedAt
    (target : MachineState) : Prop where
  liveRead :
    lookup target.env live = some (.object (.heap 0))
  frontier : target.runtime.nextLocation = 1
  control : RetainedPrefixReuseTargetAllocatedControl target

/-- Allocation/control phase invariant for the transformed fixture.  Only
entry and the pre-allocation state are concrete; every post-allocation state
is represented by the abstract interface above. -/
inductive RetainedPrefixReuseTargetAllocationControlInvariant :
    MachineState → Prop where
  | entry (arguments : Array Value) :
      RetainedPrefixReuseTargetAllocationControlInvariant
        (initialState retainedPrefixReuseAfterProgram `main arguments)
  | beforeAllocation (arguments : Array Value) :
      RetainedPrefixReuseTargetAllocationControlInvariant
        (retainedPrefixReuseTargetOuterState arguments)
  | allocated (shape : RetainedPrefixReuseTargetAllocatedAt target) :
      RetainedPrefixReuseTargetAllocationControlInvariant target

theorem retainedPrefixReuseTargetReturnAllocatedAt
    (arguments : Array Value) :
    RetainedPrefixReuseTargetAllocatedAt
      (retainedPrefixReuseTargetReturnState arguments) := by
  refine {
    liveRead := ?_
    frontier := ?_
    control := .ret arguments rfl rfl ?_
  }
  · simp [retainedPrefixReuseTargetReturnState,
      nonemptyLedgerRetainedEnv, lookup, live]
  · simp [retainedPrefixReuseTargetReturnState,
      nonemptyLedgerTargetRuntime, nonemptyLedgerPairedRuntime, alloc]
  · simp [retainedPrefixReuseTargetReturnState,
      nonemptyLedgerTargetRuntime, nonemptyLedgerPairedRuntime,
      alloc, findCell?]

/-- The allocation/control invariant is preserved by every semantic target
step.  Post-allocation preservation uses only the abstract fields: return
publishes the retained value, the entry frame either caches or applies it,
and applying the retained natural terminates with a fault rather than
entering new code. -/
theorem retainedPrefixReuseTargetAllocationControlInvariant_step
    (invariant :
      RetainedPrefixReuseTargetAllocationControlInvariant before)
    (step : Step externals before after) :
    RetainedPrefixReuseTargetAllocationControlInvariant after := by
  cases invariant with
  | entry arguments =>
      exact predicate_of_step_next
        (retainedPrefixReuseTargetEntryStep arguments)
        (.beforeAllocation arguments) step
  | beforeAllocation arguments =>
      exact predicate_of_step_next
        (retainedPrefixReuseTargetOuterStep arguments)
        (.allocated
          (retainedPrefixReuseTargetReturnAllocatedAt arguments)) step
  | allocated shape =>
      cases shape.control with
      | ret arguments control frames objectRead =>
          let expected : MachineState := {
            before with control := .yielded (.object (.heap 0)) }
          have transition : coreStep before = .next expected := by
            simp [coreStep, control, lookupValue,
              shape.liveRead, expected]
          apply predicate_of_step_next transition _ step
          apply
            RetainedPrefixReuseTargetAllocationControlInvariant.allocated
          exact {
            liveRead := by simpa [expected] using shape.liveRead
            frontier := by simpa [expected] using shape.frontier
            control := .yielded arguments rfl
              (by simpa [expected] using frames)
              (by simpa [expected] using objectRead)
          }
      | yielded arguments control frames objectRead =>
          by_cases empty : arguments = #[]
          · subst arguments
            let expected : MachineState := {
              before with
                runtime := before.runtime.setGlobal `main
                  (.object (.heap 0))
                frames := []
                control := .yielded (.object (.heap 0)) }
            have transition : coreStep before = .next expected := by
              simp [coreStep, control, frames,
                neutralEntryFrames, expected]
            apply predicate_of_step_next transition _ step
            apply
              RetainedPrefixReuseTargetAllocationControlInvariant.allocated
            exact {
              liveRead := by simpa [expected] using shape.liveRead
              frontier := by
                simpa [expected, RuntimeState.setGlobal] using
                  shape.frontier
              control := .cached rfl rfl
            }
          · let expected : MachineState := {
              before with
                control := .invokeValue (.object (.heap 0)) arguments
                frames := [] }
            have transition : coreStep before = .next expected := by
              simp [coreStep, control, frames,
                neutralEntryFrames, empty, expected]
            apply predicate_of_step_next transition _ step
            apply
              RetainedPrefixReuseTargetAllocationControlInvariant.allocated
            exact {
              liveRead := by simpa [expected] using shape.liveRead
              frontier := by simpa [expected] using shape.frontier
              control := .invoking arguments rfl rfl
                (by simpa [expected] using objectRead)
            }
      | cached control frames =>
          cases step with
          | internal transition =>
              simp [coreStep, control, frames] at transition
          | external transition response =>
              simp [coreStep, control, frames] at transition
      | invoking arguments control frames objectRead =>
          cases found : findCell? before.runtime.heap 0 with
          | none => simp [found] at objectRead
          | some cell =>
              have object :
                  cell.object = .natural 9223372036854775808 := by
                simpa [found] using objectRead
              cases liveEq : cell.live <;> cases step with
              | internal transition =>
                  simp [coreStep, control, invokeClosure, getLiveCell,
                    found, liveEq, object, fail] at transition
              | external transition response =>
                  simp [coreStep, control, invokeClosure, getLiveCell,
                    found, liveEq, object, fail] at transition

/-- A structurally related active source state can meet the target's static
allocation/control invariant only after the retained literal allocation.
This bridges the step-preserved target phase interface to the generic
singleton live-return contract consumed by both ownership-sensitive suffix
edges. -/
theorem retainedPrefixReuseTargetSingletonLiveReturnAt_of_relatedCode
    (sourceControl : source.control = .code sourceCode)
    (sourceLiveRead :
      lookup source.env live = some (.object (.heap 0)))
    (targetInvariant :
      RetainedPrefixReuseTargetAllocationControlInvariant target)
    (related :
      SomeLedgerBinderReadyReachableMachineRelated 6 source target) :
    TargetSingletonLiveReturnAt target live 0 1 := by
  rcases related with
    ⟨rho, ledger, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  rw [sourceControl] at control
  cases targetControl : target.control with
  | code targetCode =>
    rw [targetControl] at control
    cases control with
    | code graph joins env =>
      rename_i used
      have covered : CodeCovered used targetCode :=
        graph.toShadowCodeGraph.covered
      cases targetInvariant with
      | entry =>
          simp [initialState] at targetControl
      | beforeAllocation =>
          have codeEq : targetCode = retainedPrefixReuseAfter :=
            Control.code.inj targetControl.symm
          subst targetCode
          cases covered with
          | letE valueCovered continuationCovered =>
            cases continuationCovered with
            | ret liveMember =>
              obtain ⟨targetValue, targetFound, values⟩ :=
                env.right_lookup_exists
                  (leftValue := .object (.heap 0))
                  liveMember sourceLiveRead
              simp [retainedPrefixReuseTargetOuterState,
                lookup] at targetFound
      | allocated shape =>
          cases shape.control with
          | ret arguments activeControl activeFrames objectRead =>
              exact {
                control := activeControl
                liveRead := shape.liveRead
                frontier := shape.frontier
                rightBounded := by decide
                singleton := by
                  intro location bounded
                  exact Nat.eq_zero_of_le_zero
                    (Nat.le_of_lt_succ bounded)
              }
          | yielded arguments activeControl activeFrames objectRead =>
              rw [targetControl] at activeControl
              cases activeControl
          | cached activeControl activeFrames =>
              rw [targetControl] at activeControl
              cases activeControl
          | invoking arguments activeControl activeFrames objectRead =>
              rw [targetControl] at activeControl
              cases activeControl
  | yielded targetValue =>
      rw [targetControl] at control
      cases control
  | invokeName targetName targetArguments =>
      rw [targetControl] at control
      cases control
  | invokeValue targetFunction targetArguments =>
      rw [targetControl] at control
      cases control

/-- The whole-program reset state has exactly the local heap/environment
shape used by the focused nonempty-ledger regression. -/
def retainedPrefixReuseResetLocalReady
    (arguments : Array Value) :
    DeletedResetLocalReadyAt
      (retainedPrefixReuseSourceResetState arguments)
      1 resetObjectVar := by
  apply DeletedResetLocalReadyAt.of_evalLetValue
      (fvarId := reuseTokenVar)
      (binderName := reuseTokenVar.name)
      (type := objType)
      (nextRuntime := nonemptyLedgerResetRuntime)
      (tokenValue := .reuseToken (some 1))
  rfl

/-- The reset operand is not merely source-only: its complete owned closure
is disjoint from every target-ledger owner. This example is a leaf, so the
hereditary fact follows from the ordinary binding and its empty heap-child
set. -/
theorem retainedPrefixReuseResetClosureBinding
    (arguments : Array Value)
    (ledger : TargetAllocationLedger rho rightFrontier)
    (sourceOnly : SourceOnlyUnderTargetLedger ledger 1) :
    SourceOnlyHeapClosureBinding ledger
      (retainedPrefixReuseSourceResetState arguments).env
      resetObjectVar 1
      (retainedPrefixReuseSourceResetState arguments).runtime.heap := by
  have objectBinding :
      SourceOnlyHeapBinding ledger
        (retainedPrefixReuseSourceResetState arguments).env
        resetObjectVar 1 := {
    read := by
      simp [retainedPrefixReuseSourceResetState,
        nonemptyLedgerResetEnv, nonemptyLedgerRetainedEnv,
        lookupValue, Impure.bind, lookup,
        resetObjectVar, live]
    sourceOnly
  }
  apply objectBinding.closure_of_no_heap_children
      (cell := ({ object := .ctor deletedWriteObject } : HeapCell))
  · rfl
  · intro child member
    simp [HeapObject.ownedValues, deletedWriteObject] at member

/-- The successful reset publishes its source-only object address as the
concrete token capability consumed after the intervening argument binding. -/
theorem retainedPrefixReuseTokenBinding
    (arguments : Array Value)
    (ledger : TargetAllocationLedger rho rightFrontier)
    (sourceOnly : SourceOnlyUnderTargetLedger ledger 1) :
    SourceOnlyReuseTokenBinding ledger
      (retainedPrefixReuseSourceReuseState arguments).env
      reuseTokenVar 1 := by
  have closure :=
    retainedPrefixReuseResetClosureBinding arguments ledger sourceOnly
  have tokenBinding :=
    (retainedPrefixReuseResetLocalReady arguments)
      |>.sourceOnlyReuseTokenBinding
        closure.binding rfl reuseTokenVar
  have tokenEq :
      (retainedPrefixReuseResetLocalReady arguments).token =
        .reuseToken (some 1) := rfl
  rw [tokenEq] at tokenBinding
  have preserved :=
    tokenBinding.bindOther
      (other := reuseArgVar) (by native_decide) .erased
  simpa [retainedPrefixReuseSourceReuseState,
    retainedPrefixReuseSourceResetState,
    nonemptyLedgerReuseEnv, retainedPrefixReuseTokenEnv] using preserved

theorem retainedPrefixReuseResetFresh :
    ∀ location,
      nonemptyLedgerResetRuntime.nextLocation ≤ location →
        findCell? nonemptyLedgerResetRuntime.heap location = none := by
  intro location bounded
  change 2 ≤ location at bounded
  have oneLt : 1 < location :=
    Nat.lt_of_lt_of_le (by decide) bounded
  have zeroLt : 0 < location :=
    Nat.lt_trans (by decide) oneLt
  have notOne : (1 : Nat) ≠ location := Nat.ne_of_lt oneLt
  have notZero : (0 : Nat) ≠ location := Nat.ne_of_lt zeroLt
  simp [nonemptyLedgerResetRuntime, findCell?, notOne, notZero]

/-- Ledger-aligned reset readiness for the checked retained-prefix program.
The only code-related target state is the post-literal return state; its
covered live root fixes the paired address at `0`. -/
theorem retainedPrefixReuseResetPairReady_ledger
    (resetFresh :
      ∀ location,
        nonemptyLedgerResetRuntime.nextLocation ≤ location →
          findCell? nonemptyLedgerResetRuntime.heap location = none)
    (targetInvariant :
      RetainedPrefixReuseTargetAllocationControlInvariant target)
    (related : SomeLedgerBinderReadyReachableMachineRelated 6
      (retainedPrefixReuseSourceResetState sourceArguments) target) :
    LedgerBinderReadyReachableMachineReadyAt 6
      (retainedPrefixReuseSourceResetState sourceArguments) target := by
  have sourceControl :
      (retainedPrefixReuseSourceResetState sourceArguments).control =
        .code retainedPrefixReuseAfterObjectCode := rfl
  have targetShape :
      TargetSingletonLiveReturnAt target live 0 1 :=
    retainedPrefixReuseTargetSingletonLiveReturnAt_of_relatedCode
      sourceControl
      (by
        simp [retainedPrefixReuseSourceResetState,
          nonemptyLedgerResetEnv, nonemptyLedgerRetainedEnv,
          Impure.bind, lookup, live, resetObjectVar])
      targetInvariant related
  rcases related with
    ⟨rho, ledger, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  rw [sourceControl] at control
  rw [targetShape.control] at control
  cases control with
  | code graph joins env =>
    rename_i used
    have covered : CodeCovered used (.return live) :=
      graph.toShadowCodeGraph.covered
    rcases graph with
      ⟨remaining, final, bounded, exact, subset, static⟩
    cases covered with
    | ret liveMember =>
      have mapping : rho.forward 0 = some 0 := by
        apply env.heap_mapping liveMember
        · simp [retainedPrefixReuseSourceResetState,
            nonemptyLedgerResetEnv, nonemptyLedgerRetainedEnv,
            Impure.bind, lookup, live, resetObjectVar]
        · exact targetShape.liveRead
      have sourceOnly :
          SourceOnlyUnderTargetLedger ledger 1 :=
        targetShape.sourceOnly_of_mapping_ne
          mapping (by decide) ledger
      have closure :
          SourceOnlyHeapClosureBinding ledger
            (retainedPrefixReuseSourceResetState sourceArguments).env
            resetObjectVar 1
            (retainedPrefixReuseSourceResetState
              sourceArguments).runtime.heap :=
        retainedPrefixReuseResetClosureBinding
          sourceArguments ledger sourceOnly
      have resetReady :
          DeletedResetReadyAt
            (retainedPrefixReuseSourceResetState sourceArguments)
            (runtimeRoots
              (retainedPrefixReuseSourceResetState sourceArguments).runtime
              (envRootsOn used
                (retainedPrefixReuseSourceResetState sourceArguments).env ++
                sourceFrameRoots))
            1 resetObjectVar := by
        apply
          (retainedPrefixReuseResetLocalReady sourceArguments)
            |>.deletedReadyAt_of_targetAllocationLedger_sourceOnlyClosure
              runtime ledger closure
        · rfl
        · rfl
        · rfl
        · exact resetFresh
      have removed :
          DeletedLetReadyAt
            (retainedPrefixReuseSourceResetState sourceArguments)
            (runtimeRoots
              (retainedPrefixReuseSourceResetState sourceArguments).runtime
              (envRootsOn used
                (retainedPrefixReuseSourceResetState sourceArguments).env ++
                sourceFrameRoots))
            closedConcreteReuseTokenDecl := by
        unfold closedConcreteReuseTokenDecl letDecl
        exact .reset reuseTokenVar reuseTokenVar.name objType
          1 resetObjectVar resetReady
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        ledger, programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetShape.control] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            ExactShadowCodeRuntimeReadyAt.let_of_ready
              removed (by trivial)⟩
          joins env)

/-- Source-owned form of the nonempty-ledger reset proof. The target owner
table still establishes source-only closure provenance, while post-reset
freshness now comes from the maintained source carrier rather than the
fixture's enumerated heap. -/
theorem retainedPrefixReuseResetPairReady_sourceOwnedLedger
    (sourceOwnership :
      SourceMachineOwnershipBelowFrontier
        (retainedPrefixReuseSourceResetState sourceArguments))
    (targetInvariant :
      RetainedPrefixReuseTargetAllocationControlInvariant target)
    (related : SomeLedgerBinderReadyReachableMachineRelated 6
      (retainedPrefixReuseSourceResetState sourceArguments) target) :
    LedgerBinderReadyReachableMachineReadyAt 6
      (retainedPrefixReuseSourceResetState sourceArguments) target := by
  apply retainedPrefixReuseResetPairReady_ledger
  · exact
      (retainedPrefixReuseResetLocalReady sourceArguments)
        |>.afterFresh_of_sourceOwnership sourceOwnership
  · exact targetInvariant
  · exact related

/-- The same carried owner table proves that concrete reuse overwrites only
source location `1`. -/
theorem retainedPrefixReusePairReady_ledger
    (targetInvariant :
      RetainedPrefixReuseTargetAllocationControlInvariant target)
    (related : SomeLedgerBinderReadyReachableMachineRelated 6
      (retainedPrefixReuseSourceReuseState sourceArguments) target) :
    LedgerBinderReadyReachableMachineReadyAt 6
      (retainedPrefixReuseSourceReuseState sourceArguments) target := by
  have sourceControl :
      (retainedPrefixReuseSourceReuseState sourceArguments).control =
        .code retainedPrefixReuseAfterArgCode := rfl
  have targetShape :
      TargetSingletonLiveReturnAt target live 0 1 :=
    retainedPrefixReuseTargetSingletonLiveReturnAt_of_relatedCode
      sourceControl
      (by
        simp [retainedPrefixReuseSourceReuseState,
          nonemptyLedgerReuseEnv, nonemptyLedgerResetEnv,
          nonemptyLedgerRetainedEnv, Impure.bind, lookup,
          live, resetObjectVar, reuseTokenVar, reuseArgVar])
      targetInvariant related
  rcases related with
    ⟨rho, ledger, sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  rw [sourceControl] at control
  rw [targetShape.control] at control
  cases control with
  | code graph joins env =>
    rename_i used
    have covered : CodeCovered used (.return live) :=
      graph.toShadowCodeGraph.covered
    rcases graph with
      ⟨remaining, final, bounded, exact, subset, static⟩
    cases covered with
    | ret liveMember =>
      have mapping : rho.forward 0 = some 0 := by
        apply env.heap_mapping liveMember
        · simp [retainedPrefixReuseSourceReuseState,
            nonemptyLedgerReuseEnv, nonemptyLedgerResetEnv,
            nonemptyLedgerRetainedEnv, Impure.bind, lookup,
            live, resetObjectVar, reuseTokenVar, reuseArgVar]
        · exact targetShape.liveRead
      have sourceOnly : SourceOnlyUnderTargetLedger ledger 1 :=
        targetShape.sourceOnly_of_mapping_ne
          mapping (by decide) ledger
      have reuseReady :
          DeletedReuseReadyAt
            (retainedPrefixReuseSourceReuseState sourceArguments)
            (runtimeRoots
              (retainedPrefixReuseSourceReuseState sourceArguments).runtime
              (envRootsOn used
                (retainedPrefixReuseSourceReuseState sourceArguments).env ++
                sourceFrameRoots))
            reuseTokenVar oneFieldInfo #[.fvar reuseArgVar] := by
        have binding :
            SourceOnlyReuseTokenBinding ledger
              (retainedPrefixReuseSourceReuseState sourceArguments).env
              reuseTokenVar 1 :=
          retainedPrefixReuseTokenBinding
            sourceArguments ledger sourceOnly
        apply binding.deletedReuseSomeReadyAt_of_effect
            (values := #[.erased]) (updateHeader := true)
            (related := runtime)
        · simp [retainedPrefixReuseSourceReuseState,
            nonemptyLedgerReuseEnv, nonemptyLedgerResetEnv,
            nonemptyLedgerRetainedEnv,
            evalArgs, evalArg, Impure.bind, lookup,
            reuseTokenVar, reuseArgVar, resetObjectVar, live]
          rfl
        · rfl
      have decision :
          exact.view.runtimeDecision = .deletedLet :=
        exact.view
          |>.runtimeDecision_eq_deletedLet_of_target_not_same_let
            (by simp)
      have removed :
          DeletedLetReadyAt
            (retainedPrefixReuseSourceReuseState sourceArguments)
            (runtimeRoots
              (retainedPrefixReuseSourceReuseState sourceArguments).runtime
              (envRootsOn used
                (retainedPrefixReuseSourceReuseState sourceArguments).env ++
                sourceFrameRoots))
            deadReuseDecl := by
        unfold deadReuseDecl letDecl
        exact .reuse dead dead.name objType reuseTokenVar
          oneFieldInfo true #[.fvar reuseArgVar] reuseReady
      refine ⟨rho, _, _, sourceFrameRoots, targetFrameRoots,
        ledger, programs, ?_, frames, runtime⟩
      simpa only [sourceControl, targetShape.control] using
        (BinderReadyReachableControlReadyAt.code
          ⟨remaining, final, bounded, exact, subset, static,
            ExactShadowCodeRuntimeReadyAt.letDeleted
              decision removed⟩
          joins env)

theorem retainedPrefixReuseBeforeSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6 state sourceFrameRoots
      retainedPrefixReuseBefore := by
  unfold retainedPrefixReuseBefore retainedLargeNatDecl letDecl
  exact SourceRuntimeOwnershipReadyAt.let_of_literal

theorem retainedPrefixReuseObjectSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6
      (retainedPrefixReuseSourceObjectState arguments)
      sourceFrameRoots retainedPrefixReuseAfterLiveCode := by
  unfold retainedPrefixReuseAfterLiveCode
    retainedPrefixReuseObjectDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_constructor
  refine .mk #[.erased] ?_ rfl
  simp [retainedPrefixReuseSourceObjectState,
    nonemptyLedgerRetainedEnv, evalArgs, evalArg]
  rfl

theorem retainedPrefixReuseArgSourceRuntimeReadyAt
    (arguments : Array Value) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6
      (retainedPrefixReuseSourceArgState arguments)
      sourceFrameRoots retainedPrefixReuseAfterResetCode := by
  unfold retainedPrefixReuseAfterResetCode closedReuseArgDecl letDecl
  apply SourceRuntimeOwnershipReadyAt.let_of_runtimeNeutral
  · exact ⟨.erased, rfl⟩
  · intro roots
    trivial

theorem retainedPrefixReuseReturnSourceRuntimeReadyAt
    (state : MachineState) (sourceFrameRoots : List Value) :
    SourceRuntimeOwnershipReadyAt 6 state sourceFrameRoots
      (.return live) := by
  intro used remaining final targetCode bounded exact subset static
  simp [ExactShadowCodeRuntimeReadyAt]

theorem retainedPrefixReuseOuterSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 6
      (retainedPrefixReuseSourceOuterState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = retainedPrefixReuseBefore :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact retainedPrefixReuseBeforeSourceRuntimeReadyAt
    (retainedPrefixReuseSourceOuterState arguments)
    sourceFrameRoots bounded exact subset static

theorem retainedPrefixReuseObjectSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 6
      (retainedPrefixReuseSourceObjectState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = retainedPrefixReuseAfterLiveCode :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact retainedPrefixReuseObjectSourceRuntimeReadyAt
    arguments sourceFrameRoots bounded exact subset static

theorem retainedPrefixReuseArgSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 6
      (retainedPrefixReuseSourceArgState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = retainedPrefixReuseAfterResetCode :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact retainedPrefixReuseArgSourceRuntimeReadyAt
    arguments sourceFrameRoots bounded exact subset static

theorem retainedPrefixReuseReturnSourceMachineReadyAt
    (arguments : Array Value) :
    SourceRuntimeOwnershipMachineReadyAt 6
      (retainedPrefixReuseSourceReturnState arguments) := by
  intro sourceFrameRoots sourceCode frames control
  have codeEq : sourceCode = .return live :=
    Control.code.inj control.symm
  subst sourceCode
  intro used remaining final targetCode bounded exact subset static
  exact retainedPrefixReuseReturnSourceRuntimeReadyAt
    (retainedPrefixReuseSourceReturnState arguments)
    sourceFrameRoots bounded exact subset static

/-- Every source state in the finite entry graph is ledger-ready. Reset and
reuse use the paired owner proof; the remaining states use hereditary
source-only readiness. -/
theorem retainedPrefixReuseSourceReachable_pairReady_ledger
    (sourceReachable :
      RetainedPrefixReuseSourceReachable sourceArguments source)
    (targetInvariant :
      RetainedPrefixReuseTargetAllocationControlInvariant target)
    (related :
      SomeLedgerBinderReadyReachableMachineRelated 6 source target) :
    LedgerBinderReadyReachableMachineReadyAt 6 source target := by
  cases sourceReachable with
  | entry =>
      apply related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [initialState] at control
  | outer =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (retainedPrefixReuseOuterSourceMachineReadyAt sourceArguments)
  | object =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (retainedPrefixReuseObjectSourceMachineReadyAt sourceArguments)
  | reset =>
      exact retainedPrefixReuseResetPairReady_ledger
        retainedPrefixReuseResetFresh targetInvariant related
  | argument =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (retainedPrefixReuseArgSourceMachineReadyAt sourceArguments)
  | reuse =>
      exact retainedPrefixReusePairReady_ledger targetInvariant related
  | ret =>
      exact
        related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
          (retainedPrefixReuseReturnSourceMachineReadyAt sourceArguments)
  | yielded =>
      apply related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [retainedPrefixReuseSourceYieldedState] at control
  | cached empty =>
      apply related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [retainedPrefixReuseSourceCachedState] at control
  | invoking notEmpty =>
      apply related.ledgerBinderReadyReachableMachineReadyAt_of_sourceMachine
      apply SourceRuntimeOwnershipMachineReadyAt.of_not_code
      intro sourceCode control
      simp [retainedPrefixReuseSourceInvokingState] at control

/-- Combined readiness for every retained-prefix source state. The reset edge
uses source ownership and the nonempty target ledger together; all other
edges reuse the established ledger-exact readiness proofs. -/
theorem retainedPrefixReuseSourceReachable_pairReady_sourceOwnedLedger
    (sourceReachable :
      RetainedPrefixReuseSourceReachable sourceArguments source)
    (targetInvariant :
      RetainedPrefixReuseTargetAllocationControlInvariant target)
    (sourceOwnership :
      SourceMachineOwnershipBelowFrontier source)
    (related :
      SomeLedgerBinderReadyReachableMachineRelated 6 source target) :
    LedgerBinderReadyReachableMachineReadyAt 6 source target := by
  cases sourceReachable with
  | entry =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        .entry targetInvariant related
  | outer =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        .outer targetInvariant related
  | object =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        .object targetInvariant related
  | reset =>
      exact retainedPrefixReuseResetPairReady_sourceOwnedLedger
        sourceOwnership targetInvariant related
  | argument =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        .argument targetInvariant related
  | reuse =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        .reuse targetInvariant related
  | ret =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        .ret targetInvariant related
  | yielded =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        .yielded targetInvariant related
  | cached empty =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        (.cached empty) targetInvariant related
  | invoking notEmpty =>
      exact retainedPrefixReuseSourceReachable_pairReady_ledger
        (.invoking notEmpty) targetInvariant related

theorem retainedPrefixReuseSourceReachable_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState retainedPrefixReuseBeforeProgram `main arguments)
      state) :
    RetainedPrefixReuseSourceReachable arguments state := by
  exact path.invariant .entry
    retainedPrefixReuseSourceReachable_step

theorem retainedPrefixReuseTargetAllocationControlInvariant_of_reaches
    (path : NonLockstep.Reaches externals
      (initialState retainedPrefixReuseAfterProgram `main arguments)
      state) :
    RetainedPrefixReuseTargetAllocationControlInvariant state := by
  exact path.invariant
    (.entry arguments)
    retainedPrefixReuseTargetAllocationControlInvariant_step

/-- Checked whole-program client of the ledger-exact ownership endpoint with
a genuinely nonempty target owner table at reset and reuse. -/
def retainedPrefixReuseLedgerExactOwnershipContract
    (externals : ExternalSpec) :
    ElimDeadLedgerExactOwnershipContract externals 6
      retainedPrefixReuseBeforeProgram
      retainedPrefixReuseAfterProgram #[`main] where
  invariant := fun _ sourceArguments targetArguments source target =>
    RetainedPrefixReuseSourceReachable sourceArguments source ∧
      RetainedPrefixReuseTargetAllocationControlInvariant target
  initial := by
    intro entry member sourceArguments targetArguments _argumentsRelated
    have entryEq : entry = `main := by
      simpa using member
    subst entry
    exact ⟨.entry, .entry targetArguments⟩
  sourcePreserved := by
    rintro entry sourceArguments targetArguments
      sourceBefore sourceAfter targetState
      ⟨sourceReachable, targetInvariant⟩ step
    exact ⟨retainedPrefixReuseSourceReachable_step
      sourceReachable step, targetInvariant⟩
  targetPreserved := by
    rintro entry sourceArguments targetArguments
      sourceState targetBefore targetAfter
      ⟨sourceReachable, targetInvariant⟩ step
    exact ⟨sourceReachable,
      retainedPrefixReuseTargetAllocationControlInvariant_step
        targetInvariant step⟩
  ready := by
    rintro entry sourceArguments targetArguments source target
      ⟨sourceReachable, targetInvariant⟩ related
    exact retainedPrefixReuseSourceReachable_pairReady_ledger
      sourceReachable targetInvariant related

/-- Combined source-owned/ledger-exact contract for the same nonempty-prefix
program.  The source still carries its operational reachability proof, while
the target is tracked only by the step-preserved allocation/control
invariant; reset readiness also consumes the separately maintained source
carrier. -/
def retainedPrefixReuseSourceOwnedLedgerExactContract
    (externals : ExternalSpec) :
    ElimDeadSourceOwnedLedgerExactContract externals 6
      retainedPrefixReuseBeforeProgram
      retainedPrefixReuseAfterProgram #[`main] := by
  let base := retainedPrefixReuseLedgerExactOwnershipContract externals
  refine {
    invariant := base.invariant
    initial := base.initial
    sourcePreserved := base.sourcePreserved
    targetPreserved := base.targetPreserved
    ready := ?_
  }
  rintro entry sourceArguments targetArguments source target
    ⟨sourceReachable, targetInvariant⟩ sourceOwnership related
  exact retainedPrefixReuseSourceReachable_pairReady_sourceOwnedLedger
    sourceReachable targetInvariant sourceOwnership related

theorem retainedPrefixReuseBeforeProgramElimDeadWellFormed :
    ProgramElimDeadWellFormed retainedPrefixReuseBeforeProgram := by
  refine ⟨?_, ?_⟩
  · apply ProgramWellFormed.ofCompilerInvariants
    · apply WellFormedAt.impure
      · simp [Program.NamesUnique,
          retainedPrefixReuseBeforeProgram, fixtureDecl, decl]
      · unfold Program.ImpureHygienic
        native_decide
    · native_decide
    · intro declaration member
      simp [retainedPrefixReuseBeforeProgram] at member
      subst declaration
      exact .letE (.letE (.letE (.letE (.letE .ret))))
    · intro declaration member
      simp [retainedPrefixReuseBeforeProgram] at member
      subst declaration
      exact .letE ⟨.object, trivial⟩
        (.letE ⟨.object, trivial⟩
          (.letE ⟨.object, trivial⟩
            (.letE ⟨.object, trivial⟩
              (.letE ⟨.object, trivial⟩ .ret))))
  · intro declaration member
    simp [retainedPrefixReuseBeforeProgram] at member
    subst declaration
    simp [DeclCodeBinderNamesUnique, fixtureDecl, decl,
      retainedPrefixReuseBefore, retainedLargeNatDecl,
      retainedPrefixReuseObjectDecl,
      closedConcreteReuseTokenDecl, closedReuseArgDecl,
      deadReuseDecl, letDecl, codeBinderIds,
      BinderNamesUnique, ImpureHygiene.paramIds,
      live, resetObjectVar, reuseTokenVar, reuseArgVar, dead]

theorem retainedPrefixReuseShadowProgramRun :
    shadowProgram? 6 retainedPrefixReuseBeforeProgram =
      some retainedPrefixReuseAfterProgram := by
  simp [shadowProgram?, shadowDecls?, shadowDecl?,
    retainedPrefixReuseBeforeProgram,
    retainedPrefixReuseAfterProgram,
    fixtureDecl, decl, retainedPrefixReuseShadowRun]

theorem retainedPrefixReuseCheckedProgramRun :
    nullarySafeShadowProgram? 6 retainedPrefixReuseBeforeProgram =
      some retainedPrefixReuseAfterProgram := by
  simp [nullarySafeShadowProgram?, nullarySafeShadowDecls?,
    nullarySafeShadowDecl?, retainedPrefixReuseBeforeProgram,
    retainedPrefixReuseAfterProgram, fixtureDecl, decl,
    retainedPrefixReuseCheckedRun]

/-- The actual Lean 4.32 pass is checked against the transparent retained
prefix fixture during elaboration, independently of the proof endpoint. -/
elab "#check_retained_prefix_reuse_actual" : command =>
  liftCoreM <|
    checkActualElimDead `elimDeadRetainedPrefixReuse
      retainedPrefixReuseBefore retainedPrefixReuseAfter

#check_retained_prefix_reuse_actual

/-- Direct checked-pass correctness through the unified ledger dispatcher.
At the two ownership-sensitive edges the target ledger is exactly the
nonempty `0 ↦ 0` table created by the retained literal allocation. -/
theorem retainedPrefixReuseProgramLoweringCorrect_ledgerExact
    (externals : ExternalSpec)
    (compatible :
      LedgerBinderReadyReachableExternalSpecCompatible externals 6) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      retainedPrefixReuseBeforeProgram
      retainedPrefixReuseAfterProgram #[`main] :=
  nullarySafeShadowProgram_loweringCorrect_ledgerExactOwnership
    retainedPrefixReuseBeforeProgramElimDeadWellFormed
    retainedPrefixReuseCheckedProgramRun
    (retainedPrefixReuseLedgerExactOwnershipContract externals)
    compatible

/-- Source-owned checked-pass correctness for the genuinely nonempty target
ledger. Reset freshness is supplied by the operational source carrier, while
the target owner table proves the reset/reuse location remains source-only. -/
theorem
    retainedPrefixReuseProgramLoweringCorrect_sourceOwnedLedgerExact
    (externals : ExternalSpec)
    (compatible :
      LedgerBinderReadyReachableExternalSpecCompatible externals 6)
    (sourceCompatible :
      SourceExternalSpecOwnershipCompatible externals) :
    LoweringCorrect
      (Impure.semantics externals) (Impure.semantics externals)
      (reachablePhaseSimulation externals)
      retainedPrefixReuseBeforeProgram
      retainedPrefixReuseAfterProgram #[`main] :=
  nullarySafeShadowProgram_loweringCorrect_sourceOwnedLedgerExact
    retainedPrefixReuseBeforeProgramElimDeadWellFormed
    retainedPrefixReuseCheckedProgramRun
    (retainedPrefixReuseSourceOwnedLedgerExactContract externals)
    compatible sourceCompatible

end Fir.LeanIR.Passes.ElimDeadExamples
