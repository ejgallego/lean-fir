import Fir.Wasm.Concrete.NaturalDispatchCorrectness
import Fir.Wasm.Emit.ResidentBigNumeric
import FirTalos.ConcreteResidentMemory
import FirTalos.Correctness.Adapter
import FirTalos.Correctness.Composition
import FirTalos.Correctness.Locals
import Interpreter.Wasm.Wp.Tactic

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Factored resident primitive proofs

These short Talos programs are the exact adaptations of the scalar fragments
shared by resident Nat helpers.  Their weakest-precondition lemmas form a
stable semantic vocabulary above Talos's individual instruction equations and
below operation-specific helper proofs.
-/

namespace ResidentPrimitives

/-- Generic bridge from exact body adaptation to the body installed in the
target function.  Keeping this below operation-specific resident modules lets
Nat, USize, and BigNumeric expose exact Talos bodies without importing one
another merely for adapter bookkeeping. -/
theorem adaptedFunction_body_of_exact
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {targetFunction : Wasm.Function} {targetBody : Wasm.Program}
    (adapted : FirTalos.function sourceModule sourceFunction =
      .ok targetFunction)
    (bodyAdapted : FirTalos.instructions sourceModule sourceFunction []
      sourceFunction.body = .ok targetBody) :
    targetFunction.body = targetBody ++
      FirTalos.functionTerminal sourceModule sourceFunction := by
  rcases FirTalos.Correctness.function_preserves_body adapted with
    ⟨actualBody, actualAdapted, targetBodyEq⟩
  rw [bodyAdapted] at actualAdapted
  injection actualAdapted with actualBodyEq
  simpa [actualBodyEq] using targetBodyEq

/-- Shared source spelling of the resident multiply-by-eight address
calculation.  Nat writers and BigNumeric readers use the same three i32
doublings and should share its execution proof. -/
def scale8Source (source destination : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet source,
  .localGet source,
  .i32Add,
  .localSet destination,
  .localGet destination,
  .localGet destination,
  .i32Add,
  .localSet destination,
  .localGet destination,
  .localGet destination,
  .i32Add,
  .localSet destination]

/-- Exact Talos spelling of `scale8Source`. -/
def scale8Program (sourceIndex destinationIndex : Nat) : Wasm.Program := [
  .localGet sourceIndex, .localGet sourceIndex, .add,
  .localSet destinationIndex,
  .localGet destinationIndex, .localGet destinationIndex, .add,
  .localSet destinationIndex,
  .localGet destinationIndex, .localGet destinationIndex, .add,
  .localSet destinationIndex]

/-- Machine-word result of the shared three-doubling sequence. -/
def scale8Word (index : UInt32) : UInt32 :=
  let twice := index + index
  let fourTimes := twice + twice
  fourTimes + fourTimes

/-- Three doublings are multiplication by eight in wasm32 modular
arithmetic. -/
theorem scale8Word_eq_mul8 (index : UInt32) :
    scale8Word index = 8 * index := by
  unfold scale8Word
  bv_decide

/-- Reusable execution rule for the resident multiply-by-eight sequence.

The statement exposes only the source local and Talos's three checked local
updates, so readers and writers can compose it without agreeing on a larger
frame layout. -/
theorem wp_scale8Program
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterFirst afterSecond afterThird : Wasm.Locals}
    {sourceIndex destinationIndex : Nat} {index : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (sourceLocal : initial.get sourceIndex = some (.i32 index))
    (firstSet :
      ({ initial with values := .i32 (index + index) :: tail }).set?
          destinationIndex (.i32 (index + index)) = some afterFirst)
    (secondSet :
      ({ afterFirst with values :=
          (.i32 (index + index + (index + index)) :: tail) }).set?
          destinationIndex (.i32 (index + index + (index + index))) =
            some afterSecond)
    (thirdSet :
      ({ afterSecond with values := .i32 (scale8Word index) :: tail }).set?
          destinationIndex (.i32 (scale8Word index)) = some afterThird)
    (continued :
      Wasm.wp module rest Q store { afterThird with values := tail } env) :
    Wasm.wp module (scale8Program sourceIndex destinationIndex ++ rest)
      Q store { initial with values := tail } env := by
  have firstUpdate := FirTalos.Correctness.localUpdate_of_set? firstSet
  have secondUpdate := FirTalos.Correctness.localUpdate_of_set? secondSet
  have sourceAt (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get sourceIndex =
        some (.i32 index) := by
    simpa using sourceLocal
  have firstAt (values : List Wasm.Value) :
      ({ afterFirst with values } : Wasm.Locals).get destinationIndex =
        some (.i32 (index + index)) := by
    simpa using firstUpdate.1
  have secondAt (values : List Wasm.Value) :
      ({ afterSecond with values } : Wasm.Locals).get destinationIndex =
        some (.i32 (index + index + (index + index))) := by
    simpa using secondUpdate.1
  unfold scale8Program
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    sourceAt, Wasm.wp_add_cons, Wasm.wp_localSet_cons, firstSet, firstAt,
    secondSet, secondAt]
  change
    match ({ afterSecond with values :=
        (.i32 (scale8Word index) :: tail) }).set? destinationIndex
          (.i32 (scale8Word index)) with
    | some updated =>
        Wasm.wp module rest Q store { updated with values := tail } env
    | none => Q (.Invalid "localSet index out of bounds")
  rw [thirdSet]
  exact continued

def immediateNaturalPairTest (leftIndex rightIndex : Nat) : Wasm.Program := [
  .localGet leftIndex,
  .const 1,
  .and,
  .localGet rightIndex,
  .const 1,
  .and,
  .and]

def immediateNaturalPayload (index : Nat) : Wasm.Program := [
  .localGet index,
  .const 1,
  .shrU]

def immediateNaturalPairDispatch (leftIndex rightIndex : Nat)
    (immediate fallback : Wasm.Program) : Wasm.Program :=
  immediateNaturalPairTest leftIndex rightIndex ++
    [.iff 0 0 immediate fallback]

def immediateNaturalRemainder (leftIndex rightIndex : Nat) : Wasm.Program :=
  immediateNaturalPayload leftIndex ++ immediateNaturalPayload rightIndex ++
    [.remU]

/-- Talos spelling of an unsigned i32-to-i64 extension followed by an i64-to-i32
wrap.  This program states only the physical bit-preservation fact; every ABI
or object-validity claim stays with the operation-specific refinement theorem
that produced the word. -/
def unsignedI32RoundTrip : Wasm.Program := [
  .extendUI32,
  .wrapI64]

/-- Object-typed symbolic spelling of `unsignedI32RoundTrip`. The intermediate
`uint64` and final `tobject` kinds make the intended ABI transition explicit
without borrowing linear-memory scratch. -/
def typedObjectWordRoundTripSource : List Fir.Wasm.Instruction := [
  .i64ExtendI32U .uint64,
  .i32WrapI64 .tobject]

/-- Exact scalar result of W7's direct two-immediate Nat decision branch. -/
def immediateNaturalDecisionResult
    (kind : Fir.Wasm.Emit.ResidentBigNumeric.DecisionKind)
    (left right : UInt64) : UInt32 :=
  match kind with
  | .eq => if left.toNat = right.toNat then 1 else 0
  | .lt => if left.toNat < right.toNat then 1 else 0
  | .le => if left.toNat ≤ right.toNat then 1 else 0

/-- Talos spelling of the immediate branch shared by `Nat.decEq`, `Nat.decLt`,
and `Nat.decLe`. -/
def immediateNaturalDecision
    (kind : Fir.Wasm.Emit.ResidentBigNumeric.DecisionKind)
    (leftIndex rightIndex : Nat) : Wasm.Program :=
  [.localGet leftIndex, .localGet rightIndex] ++
    match kind with
    | .eq => [.eq]
    | .lt => [.ltU]
    | .le => [.leU]

/-- A terminating defined helper call with one result composes with the
compiler's checked destination write and arbitrary continuation.  This is the
resident analogue of the import-specific `wp_external_ready_let` core, with
no host contract or helper-specific semantics baked into it. -/
theorem wp_definedCallResultSet
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {functionIndex resultIndex : Nat}
    {initial nextStore : Wasm.Store host}
    {locals updated : Wasm.Locals} {arguments tail : List Wasm.Value}
    {physicalResult : Wasm.Value} {rest : Wasm.Program}
    {Q : Wasm.Assertion host}
    (callRun :
      Wasm.TerminatesWith env module functionIndex initial (arguments ++ tail)
        (fun final values =>
          final = nextStore ∧ values = physicalResult :: tail))
    (targetSet :
      locals.set? resultIndex physicalResult = some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module (.call functionIndex :: .localSet resultIndex :: rest) Q
      initial { locals with values := arguments ++ tail } env := by
  apply Wasm.wp_call_tw callRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  exact FirTalos.Correctness.wp_localSet_of_set
    (locals := locals) (updated := updated) targetSet continued

/-- The adapter maps the emitter's shared immediate-payload decoder to the
same Talos program used by the execution lemmas below. -/
theorem instructions_immediateNaturalPayload
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext} {value : Lean.FVarId} {index : Nat}
    (found : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some index) :
    FirTalos.instructions sourceModule sourceFunction labels
      (Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload value) =
        .ok (immediateNaturalPayload index) := by
  simp [Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload,
    immediateNaturalPayload, FirTalos.instructions, FirTalos.instruction,
    found, Bind.bind, Except.bind, pure, Except.pure]

/-- The adapter preserves the exact two-instruction typed object-word round
trip.  This is a shape theorem only: the caller remains responsible for
showing that the input word represents the claimed Lean object. -/
theorem instructions_typedObjectWordRoundTripSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext} :
    FirTalos.instructions sourceModule sourceFunction labels
      typedObjectWordRoundTripSource =
        .ok unsignedI32RoundTrip := by
  simp [typedObjectWordRoundTripSource, unsignedI32RoundTrip,
    FirTalos.instructions, FirTalos.instruction, Bind.bind, Except.bind,
    pure, Except.pure]

/-- Unsigned extension followed by wrapping preserves every physical i32
word, the complete store (and therefore memory), and the caller operand tail.
The theorem deliberately makes no semantic object-validity claim. -/
theorem wp_unsignedI32RoundTrip
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {word : UInt32} {tail : List Wasm.Value} {rest : Wasm.Program}
    (continuation : Wasm.wp module rest Q store
      { locals with values := .i32 word :: tail } env) :
    Wasm.wp module (unsignedI32RoundTrip ++ rest) Q store
      { locals with values := .i32 word :: tail } env := by
  simp only [unsignedI32RoundTrip, List.cons_append, List.nil_append,
    Wasm.wp_extendUI32_cons, UInt64.ofNat_uInt32ToNat,
    Wasm.wp_wrapI64_cons]
  have roundTrip :
      UInt32.ofNat (word.toUInt64.toNat % 2 ^ 32) = word := by
    apply UInt32.toNat_inj.mp
    simp
  rw [roundTrip]
  exact continuation

/-- Successful adaptation of the two operation-specific branches lifts to
successful adaptation of the emitter's common pair dispatcher. -/
theorem instructions_withImmediateNaturalPair
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext} {left right : Lean.FVarId}
    {leftIndex rightIndex : Nat}
    {sourceImmediate sourceFallback : List Fir.Wasm.Instruction}
    {targetImmediate targetFallback : Wasm.Program}
    (leftFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) left =
        some leftIndex)
    (rightFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) right =
        some rightIndex)
    (immediateAdapted :
      FirTalos.instructions sourceModule sourceFunction (none :: labels)
        sourceImmediate =
        .ok targetImmediate)
    (fallbackAdapted :
      FirTalos.instructions sourceModule sourceFunction (none :: labels)
        sourceFallback =
        .ok targetFallback) :
    FirTalos.instructions sourceModule sourceFunction labels
      (Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair left right
        sourceImmediate sourceFallback) =
      .ok (immediateNaturalPairDispatch leftIndex rightIndex
        targetImmediate targetFallback) := by
  simp [Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair,
    Fir.Wasm.Emit.ResidentBigNumeric.bothImmediateNaturals,
    immediateNaturalPairDispatch, immediateNaturalPairTest,
    FirTalos.instructions, FirTalos.instruction, leftFound, rightFound,
    immediateAdapted, fallbackAdapted, Bind.bind, Except.bind, pure,
    Except.pure]

/-- The shared scalar dispatcher leaves the canonical true word on the stack
for a related pair of immediate naturals. -/
theorem wp_immediateNaturalPairTest
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values := .i32 1 :: tail } env) :
    Wasm.wp module (immediateNaturalPairTest leftIndex rightIndex ++ rest) Q
      store { locals with values := tail } env := by
  have leftLocal' : ({ locals with values := tail } : Wasm.Locals).get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)) := by simpa using leftLocal
  have rightLocal' : ({ locals with values :=
      (Wasm.Value.i32 (1 &&& UInt32.ofNat leftWord.value) :: tail) } :
      Wasm.Locals).get rightIndex =
        some (.i32 (UInt32.ofNat rightWord.value)) := by simpa using rightLocal
  simp only [immediateNaturalPairTest, List.cons_append, List.nil_append,
    Wasm.wp_localGet_cons, leftLocal', Wasm.wp_const_cons, Wasm.wp_and_cons,
    rightLocal']
  have selected :
      (1 &&& UInt32.ofNat rightWord.value) &&&
          (1 &&& UInt32.ofNat leftWord.value) = 1 := by
    have reordered :
        (1 &&& UInt32.ofNat rightWord.value) &&&
            (1 &&& UInt32.ofNat leftWord.value) =
          (UInt32.ofNat leftWord.value &&& 1) &&&
            (UInt32.ofNat rightWord.value &&& 1) := by
      bv_decide
    rw [reordered, pair.wasmPairTest_eq_one]
  simpa [selected] using continuation

/-- The shared logical-shift fragment decodes the left immediate payload. -/
theorem wp_immediateNaturalLeftPayload
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values := .i32 (UInt32.ofNat leftPayload.toNat) :: tail } env) :
    Wasm.wp module (immediateNaturalPayload leftIndex ++ rest) Q store
      { locals with values := tail } env := by
  have leftLocal' : ({ locals with values := tail } : Wasm.Locals).get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)) := by simpa using leftLocal
  simp only [immediateNaturalPayload, List.cons_append, List.nil_append,
    Wasm.wp_localGet_cons, leftLocal', Wasm.wp_const_cons, Wasm.wp_shrU_cons]
  simpa [pair.wasmLeftPayload] using continuation

/-- The same shared fragment decodes the right immediate payload. -/
theorem wp_immediateNaturalRightPayload
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values := .i32 (UInt32.ofNat rightPayload.toNat) :: tail } env) :
    Wasm.wp module (immediateNaturalPayload rightIndex ++ rest) Q store
      { locals with values := tail } env := by
  have rightLocal' : ({ locals with values := tail } : Wasm.Locals).get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)) := by simpa using rightLocal
  simp only [immediateNaturalPayload, List.cons_append, List.nil_append,
    Wasm.wp_localGet_cons, rightLocal', Wasm.wp_const_cons, Wasm.wp_shrU_cons]
  simpa [pair.wasmRightPayload] using continuation

/-- The nonzero immediate-remainder kernel executes without trapping and
leaves the exact mathematical remainder on the operand stack. -/
theorem wp_immediateNaturalRemainder
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightNonzero : rightPayload.toNat ≠ 0)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values :=
          (Wasm.Value.i32
            (UInt32.ofNat (leftPayload.toNat % rightPayload.toNat)) :: tail) } env) :
    Wasm.wp module (immediateNaturalRemainder leftIndex rightIndex ++ rest) Q
      store { locals with values := tail } env := by
  unfold immediateNaturalRemainder
  rw [List.append_assoc]
  apply wp_immediateNaturalLeftPayload pair leftLocal
  apply wp_immediateNaturalRightPayload pair rightLocal
  simp only [List.cons_append, List.nil_append, Wasm.wp_remU_cons]
  have rightLt : rightPayload.toNat < UInt32.size := by
    have rightFits := pair.rightFits
    unfold maxImmediatePayload at rightFits
    simp [UInt32.size]
    omega
  have machineRightNonzero : UInt32.ofNat rightPayload.toNat ≠ 0 := by
    intro zero
    have := congrArg UInt32.toNat zero
    simp at this
    have rightLt' : rightPayload.toNat < 4294967296 := by
      simpa [UInt32.size] using rightLt
    rw [Nat.mod_eq_of_lt rightLt'] at this
    exact rightNonzero this
  rw [if_neg machineRightNonzero]
  rw [pair.wasmRemainder]
  exact continuation

/-- All three direct decision instructions implement their Nat relation on a
canonical immediate pair.  The store and caller operand tail are unchanged. -/
theorem wp_immediateNaturalDecision
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {kind : Fir.Wasm.Emit.ResidentBigNumeric.DecisionKind}
    {leftIndex rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values :=
          (.i32 (immediateNaturalDecisionResult kind leftPayload rightPayload) ::
            tail) } env) :
    Wasm.wp module
      (immediateNaturalDecision kind leftIndex rightIndex ++ rest) Q store
      { locals with values := tail } env := by
  have leftLocal' : ({ locals with values := tail } : Wasm.Locals).get
      leftIndex = some (.i32 (UInt32.ofNat leftWord.value)) := by
    simpa using leftLocal
  have rightLocal' : ({ locals with values :=
      (.i32 (UInt32.ofNat leftWord.value) :: tail) } : Wasm.Locals).get
      rightIndex = some (.i32 (UInt32.ofNat rightWord.value)) := by
    simpa using rightLocal
  cases kind <;>
    simp only [immediateNaturalDecision, List.cons_append, List.nil_append,
      Wasm.wp_localGet_cons, leftLocal', rightLocal']
  · rw [Wasm.wp_eq_cons]
    simpa [immediateNaturalDecisionResult, pair.wasmWords_eq_iff] using
      continuation
  · rw [Wasm.wp_ltU_cons]
    simpa [immediateNaturalDecisionResult, pair.wasmWords_lt_iff] using
      continuation
  · rw [Wasm.wp_leU_cons]
    simpa [immediateNaturalDecisionResult, pair.wasmWords_le_iff] using
      continuation

/-- Once the pair test is known true, the generated `if` selects exactly the
immediate body and restores the caller's operand tail at the control boundary.
The proof is independent of the operation performed by that body. -/
theorem wp_immediateNaturalPairDispatch
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {immediate fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (immediateCorrect : Wasm.wp module immediate
      (fun continuation => match continuation with
        | .Fallthrough nextStore nextLocals =>
            Wasm.wp module rest Q nextStore
              { nextLocals with values := tail } env
        | .Break 0 nextStore nextLocals =>
            Wasm.wp module rest Q nextStore
              { nextLocals with values := tail } env
        | .Break (level + 1) nextStore nextLocals =>
            Q (.Break level nextStore nextLocals)
        | other => Q other)
      store { locals with values := tail } env) :
    Wasm.wp module
      (immediateNaturalPairDispatch leftIndex rightIndex immediate fallback ++
        rest) Q store { locals with values := tail } env := by
  unfold immediateNaturalPairDispatch
  rw [List.append_assoc]
  apply wp_immediateNaturalPairTest pair leftLocal rightLocal
  apply Wasm.wp_iff_cons rfl
  convert immediateCorrect using 1
  · simp
  · funext continuation
    cases continuation <;> rfl

/-- Once the physical pair test is known false, the common dispatcher selects
the fallback and restores the caller's operand tail at the control boundary.
The proof is operation-independent and complements
`wp_immediateNaturalPairDispatch`; semantic clients need only establish the
exact zero result of their representation's low-bit test. -/
theorem wp_immediateNaturalPairDispatch_fallback
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex rightIndex : Nat} {leftWord rightWord : Word32}
    {tail : List Wasm.Value} {immediate fallback rest : Wasm.Program}
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (pairTestZero :
      (UInt32.ofNat leftWord.value &&& 1) &&&
          (UInt32.ofNat rightWord.value &&& 1) = 0)
    (fallbackCorrect : Wasm.wp module fallback
      (fun continuation => match continuation with
        | .Fallthrough nextStore nextLocals =>
            Wasm.wp module rest Q nextStore
              { nextLocals with values := tail } env
        | .Break 0 nextStore nextLocals =>
            Wasm.wp module rest Q nextStore
              { nextLocals with values := tail } env
        | .Break (level + 1) nextStore nextLocals =>
            Q (.Break level nextStore nextLocals)
        | other => Q other)
      store { locals with values := tail } env) :
    Wasm.wp module
      (immediateNaturalPairDispatch leftIndex rightIndex immediate fallback ++
        rest) Q store { locals with values := tail } env := by
  have leftLocal' : ({ locals with values := tail } : Wasm.Locals).get
      leftIndex = some (.i32 (UInt32.ofNat leftWord.value)) := by
    simpa using leftLocal
  have rightLocal' : ({ locals with values :=
      (Wasm.Value.i32 (1 &&& UInt32.ofNat leftWord.value) :: tail) } :
      Wasm.Locals).get rightIndex =
        some (.i32 (UInt32.ofNat rightWord.value)) := by
    simpa using rightLocal
  unfold immediateNaturalPairDispatch
  rw [List.append_assoc]
  simp only [immediateNaturalPairTest, List.cons_append, List.nil_append,
    Wasm.wp_localGet_cons, leftLocal', Wasm.wp_const_cons, Wasm.wp_and_cons,
    rightLocal']
  have selected :
      (1 &&& UInt32.ofNat rightWord.value) &&&
          (1 &&& UInt32.ofNat leftWord.value) = 0 := by
    have reordered :
        (1 &&& UInt32.ofNat rightWord.value) &&&
            (1 &&& UInt32.ofNat leftWord.value) =
          (UInt32.ofNat leftWord.value &&& 1) &&&
            (UInt32.ofNat rightWord.value &&& 1) := by
      bv_decide
    rw [reordered, pairTestZero]
  rw [selected]
  apply Wasm.wp_iff_cons (c := (0 : UInt32)) (vs := tail) rfl
  convert fallbackCorrect using 1
  · simp
  · funext continuation
    cases continuation <;> rfl

end ResidentPrimitives

end FirTalos.Concrete
