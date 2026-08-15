import Fir.Wasm.Emit.ResidentNatArithmetic
import FirTalos.ConcreteResidentPrimitives
import FirTalos.Correctness.Adapter
import FirTalos.Correctness.Function
import FirTalos.Correctness.Locals
import Interpreter.Wasm.Wp.Tactic

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident natural-number helper refinement

This file connects the reusable resident instruction proofs to the actual
symbolic helper bodies emitted by FIR.  Syntactic adaptation, scalar
execution, and scratch-memory retyping are kept separate so other resident
numeric helpers can reuse the same proof boundaries.
-/

namespace ResidentNat

/-- Talos control skeleton of `fir_numeric_make_natural`. The three
allocation alternatives stay abstract because the immediate proof never
enters them; the actual emitter-adaptation theorem supplies those bodies. -/
def makeNaturalProgram (lowOverflow highNonzero big : Wasm.Program) :
    Wasm.Program := [
  .localGet 1,
  .const 2147483648,
  .ltU,
  .iff 0 0
    ([.localGet 1,
      .const 0,
      .eq,
      .iff 0 0
        [.localGet 0,
          .const 2147483648,
          .ltU,
          .iff 0 0
            [.localGet 0,
              .localGet 0,
              .add,
              .const 1,
              .add,
              .ret]
            lowOverflow]
        highNonzero])
    big]

/-- For a low word in the immediate range and zero high word, the prefix of
the actual constructor follows only scalar instructions and returns the
canonical tagged representation. Empty alternatives stand for allocation
branches that are unreachable under these premises. -/
theorem wp_makeNaturalImmediateProgram
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α}
    {lowOverflow highNonzero big : Wasm.Program}
    {payload : Nat} (fits : payload ≤ maxImmediatePayload)
    (returned : Q (.Return store [
      .i32 (UInt32.ofNat (Word32.encodeImmediate payload fits).value)])) :
    Wasm.wp module (makeNaturalProgram lowOverflow highNonzero big) Q store
      { params := [.i32 (UInt32.ofNat payload), .i32 0] } env := by
  have payloadLt : payload < 2147483648 := by
    simp [maxImmediatePayload] at fits
    omega
  have payloadLtSize : payload < UInt32.size := by
    simp [UInt32.size]
    omega
  have payloadLt32 : UInt32.ofNat payload < 2147483648 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' payloadLtSize]
    exact payloadLt
  have encodedEq :
      1 + (UInt32.ofNat payload + UInt32.ofNat payload) =
        UInt32.ofNat (payload * 2 + 1) := by
    calc
      _ = UInt32.ofNat payload + UInt32.ofNat payload + 1 := by ac_rfl
      _ = UInt32.ofNat (payload + payload + 1) := by
        rw [UInt32.ofNat_add, UInt32.ofNat_add]
        norm_num
      _ = UInt32.ofNat (payload * 2 + 1) := by congr 1; omega
  unfold makeNaturalProgram
  wp_run
  apply Wasm.wp_iff_cons rfl
  simp
  apply Wasm.wp_iff_cons rfl
  simp
  simp [payloadLt32]
  apply Wasm.wp_iff_cons rfl
  simp
  rw [encodedEq]
  simpa only [Word32.encodeImmediate] using returned

/-- Target function shape obtained after adapting the resident natural
constructor. The allocation bodies are retained verbatim but irrelevant to
the immediate input contract. -/
def makeNaturalTargetFunction
    (lowOverflow highNonzero big : Wasm.Program) : Wasm.Function := {
  params := [.i32, .i32]
  locals := []
  results := [.i32]
  body := makeNaturalProgram lowOverflow highNonzero big }

/-- Fuel-free, store-specific call theorem for the immediate constructor
path. This is the call boundary consumed by arithmetic helpers; unlike a
global `FuncSpec`, it can state that the current store is exactly unchanged. -/
theorem terminatesWith_makeNaturalImmediate
    {host : Type} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {functionIndex : Nat}
    {store : Wasm.Store host}
    {payload : Nat} {tail : List Wasm.Value}
    {lowOverflow highNonzero big : Wasm.Program}
    (fits : payload ≤ maxImmediatePayload)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some (makeNaturalTargetFunction lowOverflow highNonzero big)) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 0, .i32 (UInt32.ofNat payload)] ++ tail)
      (fun final values =>
        final = store ∧
          values =
            .i32 (UInt32.ofNat (Word32.encodeImmediate payload fits).value) ::
              tail) := by
  refine FirTalos.Correctness.terminatesWith_of_wp_body_at
    (env := env) (initial := store)
    (args := [.i32 0, .i32 (UInt32.ofNat payload)] ++ tail)
    (Post := fun final values =>
      final = store ∧
        values =
          .i32 (UInt32.ofNat (Word32.encodeImmediate payload fits).value) ::
            tail)
    notImport found ?_
  apply wp_makeNaturalImmediateProgram fits
  simp [FirTalos.Correctness.FunctionBodyPost, makeNaturalTargetFunction,
    Wasm.Function.numParams]

/-- Talos form of the scratch-slot cast used when a raw `i32` helper result is
returned through the object ABI. -/
def retypeRawObjectResultProgram (raw saved result : Nat) : Wasm.Program := [
  .localSet raw,
  .const 0,
  .load32 0,
  .localSet saved,
  .const 0,
  .localGet raw,
  .store32 0,
  .const 0,
  .load32 0,
  .localSet result,
  .const 0,
  .localGet saved,
  .store32 0,
  .localGet result,
  .ret]

/-- Symbolic-emitter form of the common scratch-slot object retyping ABI.
The names are parameters so proofs can recover the exact private locals of a
public generated function through its public `locals` array. -/
def retypeRawObjectResultSource (raw saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localSet raw,
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet saved,
  .i32Const .uint32 0,
  .localGet raw,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .tobject 0,
  .localSet result,
  .i32Const .uint32 0,
  .localGet saved,
  .i32Store .uint32 0,
  .localGet result,
  .ret]

/-- The adapter preserves the shared scratch-slot object retyping sequence. -/
theorem instructions_retypeRawObjectResultSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {raw saved result : Lean.FVarId}
    {rawIndex savedIndex resultIndex : Nat}
    (rawFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) raw =
        some rawIndex)
    (savedFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) saved =
        some savedIndex)
    (resultFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) result =
        some resultIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (retypeRawObjectResultSource raw saved result) =
        .ok (retypeRawObjectResultProgram rawIndex savedIndex resultIndex) := by
  simp [retypeRawObjectResultSource, retypeRawObjectResultProgram,
    FirTalos.instructions, FirTalos.instruction, rawFound, savedFound,
    resultFound, Bind.bind, Except.bind, pure, Except.pure]

/-- The scratch-slot ABI cast returns the raw word through the object lane and
restores both linear memory and the caller operand tail.  Its hypotheses are
only checked local updates and pairwise-distinct scratch slots, making the
lemma reusable for every resident helper that adopts this cast sequence. -/
theorem wp_retypeRawObjectResultProgram
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α}
    {initial afterRaw afterSaved afterResult : Wasm.Locals}
    {rawIndex savedIndex resultIndex : Nat} {rawValue : UInt32}
    {tail : List Wasm.Value}
    (pagesPositive : 0 < store.mem.pages)
    (rawNeSaved : rawIndex ≠ savedIndex)
    (savedNeResult : savedIndex ≠ resultIndex)
    (rawSet :
      ({ initial with values := .i32 rawValue :: tail }).set?
          rawIndex (.i32 rawValue) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (store.mem.read32 0) :: tail }).set?
          savedIndex (.i32 (store.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 rawValue :: tail }).set?
          resultIndex (.i32 rawValue) = some afterResult)
    (returned : Q (.Return store (.i32 rawValue :: tail))) :
    Wasm.wp module
      (retypeRawObjectResultProgram rawIndex savedIndex resultIndex) Q store
      { initial with values := .i32 rawValue :: tail } env := by
  have scratchInBounds :
      ¬((0 : UInt32).toNat + (0 : UInt32).toNat + 4 >
        store.mem.pages * 65536) := by
    simp
    omega
  have scratchAfterWriteInBounds :
      ¬((0 : UInt32).toNat + (0 : UInt32).toNat + 4 >
        (store.mem.write32 0 rawValue).pages * 65536) := by
    simpa [Wasm.Mem.write32] using scratchInBounds
  have rawUpdate := FirTalos.Correctness.localUpdate_of_set? rawSet
  have savedUpdate := FirTalos.Correctness.localUpdate_of_set? savedSet
  have resultUpdate := FirTalos.Correctness.localUpdate_of_set? resultSet
  have rawGet : afterSaved.get rawIndex = some (.i32 rawValue) := by
    rw [savedUpdate.2 rawNeSaved]
    exact rawUpdate.1
  have savedGet :
      afterResult.get savedIndex = some (.i32 (store.mem.read32 0)) := by
    rw [resultUpdate.2 savedNeResult]
    exact savedUpdate.1
  have resultGet : afterResult.get resultIndex = some (.i32 rawValue) :=
    resultUpdate.1
  have rawGet' :
      ({ afterSaved with values := .i32 0 :: tail }).get rawIndex =
        some (.i32 rawValue) := by simpa using rawGet
  have savedGet' :
      ({ afterResult with values := .i32 0 :: tail }).get savedIndex =
        some (.i32 (store.mem.read32 0)) := by simpa using savedGet
  have resultGet' :
      ({ afterResult with values := tail }).get resultIndex =
        some (.i32 rawValue) := by simpa using resultGet
  unfold retypeRawObjectResultProgram
  simp only [Wasm.wp_localSet_cons, rawSet, Wasm.wp_const_cons,
    Wasm.wp_load32_cons, UInt32.add_zero, scratchInBounds,
    ↓reduceIte, Wasm.wp_localGet_cons,
    savedSet, rawGet', Wasm.wp_store32_cons,
    scratchAfterWriteInBounds, ResidentMemoryRel.read32_write32_self,
    resultSet, savedGet', resultGet',
    Wasm.wp_ret_cons]
  simpa only [ResidentMemoryRel.write32_restore] using returned

/-- Exact target shape of the nonzero immediate branch of `Nat.mod`. -/
def immediateModProgram (makeNaturalIndex : Nat) : Wasm.Program :=
  ResidentPrimitives.immediateNaturalPayload 1 ++ [
    .const 0,
    .eq,
    .iff 0 0
      [.localGet 0, .ret]
      (ResidentPrimitives.immediateNaturalRemainder 0 1 ++ [
        .const 0,
        .call makeNaturalIndex] ++
        retypeRawObjectResultProgram 2 3 4)]

/-- Symbolic source branch corresponding to `immediateModProgram`.  This
public W6-side spelling avoids depending on private generator identifiers: the
actual identifiers are recovered positionally from `modFunction`. -/
def immediateModSource (left right raw saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload right ++ [
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse
      [.localGet left, .ret]
      (Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload left ++
        Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload right ++ [
          .i32RemU,
          .i32Const .uint32 0,
          .call (.declaration
            Fir.Wasm.Emit.ResidentNumeric.makeNaturalName)] ++
        retypeRawObjectResultSource raw saved result)]

/-- The public resident `Nat.mod` function contains exactly the W6-spelled
immediate branch and some checked fallback.  Private generator names do not
cross this theorem boundary. -/
theorem modFunction_immediate_shape :
    ∃ fallback,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
          (immediateModSource
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[2]!.1)
          fallback := by
  refine ⟨_, rfl⟩

/-- The adapter maps the symbolic immediate remainder branch to the exact
Talos program executed below. -/
theorem instructions_immediateModSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {left right raw saved result : Lean.FVarId}
    {leftIndex rightIndex rawIndex savedIndex resultIndex makeNaturalIndex : Nat}
    (leftFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) left =
        some leftIndex)
    (rightFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) right =
        some rightIndex)
    (rawFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) raw =
        some rawIndex)
    (savedFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) saved =
        some savedIndex)
    (resultFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) result =
        some resultIndex)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (immediateModSource left right raw saved result) =
        .ok (ResidentPrimitives.immediateNaturalPayload rightIndex ++ [
          .const 0,
          .eq,
          .iff 0 0
            [.localGet leftIndex, .ret]
            (ResidentPrimitives.immediateNaturalPayload leftIndex ++
              ResidentPrimitives.immediateNaturalPayload rightIndex ++ [
                .remU,
                .const 0,
                .call makeNaturalIndex] ++
              retypeRawObjectResultProgram rawIndex savedIndex resultIndex)]) := by
  simp [immediateModSource,
    Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload,
    ResidentPrimitives.immediateNaturalPayload,
    retypeRawObjectResultSource, retypeRawObjectResultProgram,
    FirTalos.instructions, FirTalos.instruction, leftFound, rightFound,
    rawFound, savedFound, resultFound, makeNaturalFound,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Once the checked fallback adapts, the adapter preserves the complete
public `Nat.mod` body and exposes the exact common dispatcher plus immediate
program consumed by the execution theorems. -/
theorem instructions_modFunctionBody_of_shape
    {sourceModule : Fir.Wasm.Module}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {makeNaturalIndex : Nat}
    (shape :
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
          (immediateModSource
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[2]!.1)
          sourceFallback)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (fallbackAdapted :
      FirTalos.instructions sourceModule
        Fir.Wasm.Emit.ResidentNatArithmetic.modFunction [] sourceFallback =
          .ok targetFallback) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction []
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.body =
        .ok (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateModProgram makeNaturalIndex) targetFallback) := by
  rw [shape]
  apply ResidentPrimitives.instructions_withImmediateNaturalPair
      (leftIndex := 0) (rightIndex := 1)
  · decide
  · decide
  · apply instructions_immediateModSource
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact makeNaturalFound
  · exact fallbackAdapted

/-- Successful adaptation installs exactly the proved dispatcher in the Talos
function body, followed only by the adapter's standard terminal marker. -/
theorem adaptedModFunction_body_of_shape
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {makeNaturalIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction = .ok targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
          (immediateModSource
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[2]!.1)
          sourceFallback)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (fallbackAdapted :
      FirTalos.instructions sourceModule
        Fir.Wasm.Emit.ResidentNatArithmetic.modFunction [] sourceFallback =
          .ok targetFallback) :
    targetFunction.body =
      ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateModProgram makeNaturalIndex) targetFallback ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction := by
  rcases FirTalos.Correctness.function_preserves_body adapted with
    ⟨targetBody, bodyAdapted, targetBodyEq⟩
  have exactBody := instructions_modFunctionBody_of_shape shape
    makeNaturalFound fallbackAdapted
  rw [exactBody] at bodyAdapted
  injection bodyAdapted with targetBodyExact
  simpa [targetBodyExact] using targetBodyEq

/-- The zero-divisor arm of the actual resident remainder skeleton returns
the original canonical left word and does not call the constructor. -/
theorem wp_immediateModProgram_zero
    {host : Type} {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {makeNaturalIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightZero : rightPayload.toNat = 0)
    (leftLocal : locals.get 0 = some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 = some (.i32 (UInt32.ofNat rightWord.value)))
    (returned :
      Q (.Return store (.i32 (UInt32.ofNat leftWord.value) :: tail))) :
    Wasm.wp module (immediateModProgram makeNaturalIndex) Q store
      { locals with values := tail } env := by
  have leftLocal' :
      ({ locals with values := tail }).get 0 =
        some (.i32 (UInt32.ofNat leftWord.value)) := by
    simpa using leftLocal
  unfold immediateModProgram
  rw [List.append_assoc]
  apply ResidentPrimitives.wp_immediateNaturalRightPayload pair rightLocal
  wp_run
  simp [rightZero]
  apply Wasm.wp_iff_cons rfl
  simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simpa only [Wasm.wp_localGet_cons, leftLocal', Wasm.wp_ret_cons] using returned

/-- Canonical physical result of the nonzero two-immediate remainder path. -/
def immediateRemainderWord
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) : UInt32 :=
  UInt32.ofNat
    (Word32.encodeImmediate (leftPayload.toNat % rightPayload.toNat)
      pair.mod_fits).value

/-- The nonzero resident remainder arm composes payload decoding, machine
remainder, the allocation-free constructor theorem, and the generic scratch
cast. It returns the canonical word with the exact initial store. -/
theorem wp_immediateModProgram_nonzero
    {host : Type} {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {afterRaw afterSaved afterResult : Wasm.Locals}
    {makeNaturalIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightNonzero : rightPayload.toNat ≠ 0)
    (pagesPositive : 0 < store.mem.pages)
    (leftLocal : locals.get 0 = some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 = some (.i32 (UInt32.ofNat rightWord.value)))
    (makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        ([.i32 0,
          .i32 (UInt32.ofNat
            (leftPayload.toNat % rightPayload.toNat))] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (immediateRemainderWord pair) :: tail))
    (rawSet :
      ({ locals with values := .i32 (immediateRemainderWord pair) :: tail }).set?
          2 (.i32 (immediateRemainderWord pair)) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (store.mem.read32 0) :: tail }).set?
          3 (.i32 (store.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 (immediateRemainderWord pair) :: tail }).set?
          4 (.i32 (immediateRemainderWord pair)) = some afterResult)
    (returned :
      Q (.Return store (.i32 (immediateRemainderWord pair) :: tail))) :
    Wasm.wp module (immediateModProgram makeNaturalIndex) Q store
      { locals with values := tail } env := by
  have machineNonzero := pair.wasmRightPayload_ne_zero rightNonzero
  have machineNonzero' : rightPayload.toUInt32 ≠ 0 := by
    simpa using machineNonzero
  unfold immediateModProgram
  rw [List.append_assoc]
  apply ResidentPrimitives.wp_immediateNaturalRightPayload pair rightLocal
  wp_run
  simp [machineNonzero']
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  apply ResidentPrimitives.wp_immediateNaturalRemainder pair rightNonzero
    leftLocal rightLocal
  simp only [Wasm.wp_const_cons]
  apply Wasm.wp_call_tw makeNaturalRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  apply wp_retypeRawObjectResultProgram pagesPositive (by decide) (by decide)
    rawSet savedSet resultSet
  simpa using returned

/-- The complete common dispatcher selects the zero-divisor immediate branch;
the checked fallback and the post-dispatch suffix are unreachable because the
branch returns. -/
theorem wp_immediateModDispatch_zero
    {host : Type} {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {makeNaturalIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightZero : rightPayload.toNat = 0)
    (leftLocal : locals.get 0 = some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 = some (.i32 (UInt32.ofNat rightWord.value)))
    (returned :
      Q (.Return store (.i32 (UInt32.ofNat leftWord.value) :: tail))) :
    Wasm.wp module
      (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateModProgram makeNaturalIndex) fallback ++ rest)
      Q store { locals with values := tail } env := by
  apply ResidentPrimitives.wp_immediateNaturalPairDispatch pair leftLocal
    rightLocal
  apply wp_immediateModProgram_zero pair rightZero leftLocal rightLocal
  simpa using returned

/-- The complete common dispatcher selects the nonzero immediate remainder
branch and inherits its exact-store result; neither fallback nor suffix can
run after the explicit return. -/
theorem wp_immediateModDispatch_nonzero
    {host : Type} {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {afterRaw afterSaved afterResult : Wasm.Locals}
    {makeNaturalIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightNonzero : rightPayload.toNat ≠ 0)
    (pagesPositive : 0 < store.mem.pages)
    (leftLocal : locals.get 0 = some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 = some (.i32 (UInt32.ofNat rightWord.value)))
    (makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        ([.i32 0,
          .i32 (UInt32.ofNat
            (leftPayload.toNat % rightPayload.toNat))] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (immediateRemainderWord pair) :: tail))
    (rawSet :
      ({ locals with values := .i32 (immediateRemainderWord pair) :: tail }).set?
          2 (.i32 (immediateRemainderWord pair)) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (store.mem.read32 0) :: tail }).set?
          3 (.i32 (store.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 (immediateRemainderWord pair) :: tail }).set?
          4 (.i32 (immediateRemainderWord pair)) = some afterResult)
    (returned :
      Q (.Return store (.i32 (immediateRemainderWord pair) :: tail))) :
    Wasm.wp module
      (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateModProgram makeNaturalIndex) fallback ++ rest)
      Q store { locals with values := tail } env := by
  apply ResidentPrimitives.wp_immediateNaturalPairDispatch pair leftLocal
    rightLocal
  apply wp_immediateModProgram_nonzero pair rightNonzero pagesPositive
    leftLocal rightLocal makeNaturalRun rawSet savedSet resultSet
  simpa using returned

/-- The zero-divisor immediate path of the actual adapted resident `Nat.mod`
function is a fuel-free defined call.  This packages the shared dispatcher
proof at the precise Wasm call boundary consumed by resident replacement. -/
theorem terminatesWith_modFunctionImmediate_zero
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex makeNaturalIndex : Nat}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {store : Wasm.Store host}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction = .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
          (immediateModSource
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[2]!.1)
          sourceFallback)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (fallbackAdapted :
      FirTalos.instructions sourceModule
        Fir.Wasm.Emit.ResidentNatArithmetic.modFunction [] sourceFallback =
          .ok targetFallback)
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightZero : rightPayload.toNat = 0) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat rightWord.value),
        .i32 (UInt32.ofNat leftWord.value)] ++ tail)
      (fun final values =>
        final = store ∧
          values = .i32 (UInt32.ofNat leftWord.value) :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedModFunction_body_of_shape adapted shape
    makeNaturalFound fallbackAdapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let entry := targetFunction.toLocals
    (([Wasm.Value.i32 (UInt32.ofNat rightWord.value),
      Wasm.Value.i32 (UInt32.ofNat leftWord.value)] ++ tail).take
        targetFunction.numParams).reverse
  have leftLocal : entry.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  have rightLocal : entry.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction
          ([.i32 (UInt32.ofNat rightWord.value),
            .i32 (UInt32.ofNat leftWord.value)] ++ tail)
          (fun final values =>
            final = store ∧
              values = .i32 (UInt32.ofNat leftWord.value) :: tail)
          (.Return store [.i32 (UInt32.ofNat leftWord.value)]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
      paramsEq, resultsEq,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  simpa [entry, Wasm.Function.toLocals] using
    (wp_immediateModDispatch_zero
      (module := module) (env := env) (store := store) (locals := entry)
      (makeNaturalIndex := makeNaturalIndex) (fallback := targetFallback)
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentNatArithmetic.modFunction)
      (tail := []) pair rightZero leftLocal rightLocal returned)

/-- The nonzero two-immediate path of the actual adapted resident `Nat.mod`
function is a fuel-free defined call.  The nested constructor call and all
three scratch-local writes are discharged through their shared primitive
contracts; the arbitrary-precision fallback remains unreachable and opaque. -/
theorem terminatesWith_modFunctionImmediate_nonzero
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex makeNaturalIndex : Nat}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback lowOverflow highNonzero big : Wasm.Program}
    {store : Wasm.Store host}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction = .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
          (immediateModSource
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.locals[2]!.1)
          sourceFallback)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (fallbackAdapted :
      FirTalos.instructions sourceModule
        Fir.Wasm.Emit.ResidentNatArithmetic.modFunction [] sourceFallback =
          .ok targetFallback)
    (makeNaturalNotImport : module.imports[makeNaturalIndex]? = none)
    (makeNaturalTargetFound :
      module.funcs[makeNaturalIndex - module.imports.length]? =
        some (makeNaturalTargetFunction lowOverflow highNonzero big))
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightNonzero : rightPayload.toNat ≠ 0)
    (pagesPositive : 0 < store.mem.pages) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat rightWord.value),
        .i32 (UInt32.ofNat leftWord.value)] ++ tail)
      (fun final values =>
        final = store ∧
          values = .i32 (immediateRemainderWord pair) :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedModFunction_body_of_shape adapted shape
    makeNaturalFound fallbackAdapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let entry := targetFunction.toLocals
    (([Wasm.Value.i32 (UInt32.ofNat rightWord.value),
      Wasm.Value.i32 (UInt32.ofNat leftWord.value)] ++ tail).take
        targetFunction.numParams).reverse
  have leftLocal : entry.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  have rightLocal : entry.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  have makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        [.i32 0,
          .i32 (UInt32.ofNat
            (leftPayload.toNat % rightPayload.toNat))]
        (fun final values =>
          final = store ∧
            values = .i32 (immediateRemainderWord pair) :: []) := by
    simpa [immediateRemainderWord] using
      (terminatesWith_makeNaturalImmediate
        (module := module) (env := env) (store := store) (tail := [])
        pair.mod_fits makeNaturalNotImport makeNaturalTargetFound)
  have rawValid :
      ({ entry with values := [.i32 (immediateRemainderWord pair)] }).validIndex
        2 := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      localsEq, Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  obtain ⟨afterRaw, rawSet⟩ :=
    FirTalos.Correctness.locals_set?_exists rawValid
  have rawLengths := FirTalos.Correctness.locals_lengths_of_set? rawSet
  have savedValid :
      ({ afterRaw with values := [.i32 (store.mem.read32 0)] }).validIndex 3 := by
    simp only [Wasm.Locals.validIndex]
    simp [rawLengths.1, rawLengths.2, entry, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, localsEq,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  obtain ⟨afterSaved, savedSet⟩ :=
    FirTalos.Correctness.locals_set?_exists savedValid
  have savedLengths := FirTalos.Correctness.locals_lengths_of_set? savedSet
  have resultValid :
      ({ afterSaved with values := [.i32 (immediateRemainderWord pair)]
        }).validIndex 4 := by
    simp only [Wasm.Locals.validIndex]
    simp [savedLengths.1, savedLengths.2, rawLengths.1, rawLengths.2,
      entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      localsEq, Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  obtain ⟨afterResult, resultSet⟩ :=
    FirTalos.Correctness.locals_set?_exists resultValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction
          ([.i32 (UInt32.ofNat rightWord.value),
            .i32 (UInt32.ofNat leftWord.value)] ++ tail)
          (fun final values =>
            final = store ∧
              values = .i32 (immediateRemainderWord pair) :: tail)
          (.Return store [.i32 (immediateRemainderWord pair)]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
      paramsEq, resultsEq,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction]
  simpa [entry, Wasm.Function.toLocals] using
    (wp_immediateModDispatch_nonzero
      (module := module) (env := env) (store := store) (locals := entry)
      (makeNaturalIndex := makeNaturalIndex) (fallback := targetFallback)
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentNatArithmetic.modFunction)
      (tail := []) pair rightNonzero pagesPositive leftLocal rightLocal
      makeNaturalRun rawSet savedSet resultSet returned)

/-- The public resident `Nat.mod` body is structurally the shared pair
dispatcher. This theorem deliberately exposes only the two branch lists; the
checked arbitrary-precision implementation remains opaque. -/
theorem modFunction_body_shape :
    ∃ immediate fallback,
      Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.modFunction.params[1]!.1
          immediate fallback := by
  refine ⟨_, _, rfl⟩

end ResidentNat

end FirTalos.Concrete
