import Fir.Wasm.Emit.ResidentUSize
import FirTalos.ConcreteResidentNat

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident Nat-to-USize refinement

This module verifies the optimized `USize.ofNat` and `USize.ofNatLT`
helpers.  Their shared dispatcher decodes canonical tagged naturals directly;
all other representations retain the checked arbitrary-precision path.  The
immediate arm returns directly without touching locals or memory; only the
checked arm crosses the scratch-memory retyping boundary.
-/

namespace ResidentUSize

/-- The two public helpers share one body but differ in their erased source
argument. -/
inductive NatConversionKind where
  | plain
  | withProof
  deriving DecidableEq

def conversionFunction : NatConversionKind → Fir.Wasm.Function
  | .plain => Fir.Wasm.Emit.ResidentUSize.ofNatFunction
  | .withProof => Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction

def rawIndex : NatConversionKind → Nat
  | .plain => 1
  | .withProof => 2

def savedIndex (kind : NatConversionKind) : Nat := rawIndex kind + 1

def resultIndex (kind : NatConversionKind) : Nat := rawIndex kind + 2

/-- W6 spelling of W7's direct canonical-tag decode. -/
def immediateSource (value : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet value,
  .i32Const .uint32 1,
  .i32ShrU,
  .i64ExtendI32U .usize,
  .ret]

/-- The checked path deliberately validates before reading limb zero.  This
ordering is part of the failure contract for malformed representations. -/
def checkedSource (value raw : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet value,
  .call (.declaration
    Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalName),
  .localGet value,
  .i32Const .uint32 0,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalHighName),
  .i64ExtendI32U .uint64,
  .i64Const .uint64 32,
  .i64Shl,
  .localGet value,
  .i32Const .uint32 0,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalLowName),
  .i64ExtendI32U .uint64,
  .i64Or,
  .localSet raw]

/-- W6 spelling of the common `UInt64`-to-`USize` scratch cast. -/
def retypeSource (raw saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localSet raw,
  .i32Const .uint32 0,
  .i64Load .uint64 0,
  .localSet saved,
  .i32Const .uint32 0,
  .localGet raw,
  .i64Store .uint64 0,
  .i32Const .uint32 0,
  .i64Load .usize 0,
  .localSet result,
  .i32Const .uint32 0,
  .localGet saved,
  .i64Store .uint64 0,
  .localGet result,
  .ret]

def immediateProgram (value : Nat) : Wasm.Program := [
  .localGet value,
  .const 1,
  .shrU,
  .extendUI32,
  .ret]

def checkedProgram (validate high low value raw : Nat) : Wasm.Program := [
  .localGet value,
  .call validate,
  .localGet value,
  .const 0,
  .call high,
  .extendUI32,
  .constI64 32,
  .shlI64,
  .localGet value,
  .const 0,
  .call low,
  .extendUI32,
  .orI64,
  .localSet raw]

def retypeProgram (raw saved result : Nat) : Wasm.Program := [
  .localSet raw,
  .const 0,
  .load64 0,
  .localSet saved,
  .const 0,
  .localGet raw,
  .store64 0,
  .const 0,
  .load64 0,
  .localSet result,
  .const 0,
  .localGet saved,
  .store64 0,
  .localGet result,
  .ret]

/-- Target body skeleton. `fallback` is the exact adapted checked
arbitrary-precision arm; keeping it opaque makes the immediate theorem
independent of its implementation while preserving it byte for byte. -/
def conversionProgram (kind : NatConversionKind) (fallback : Wasm.Program) :
    Wasm.Program := [
  .localGet 0,
  .const 1,
  .and,
  .iff 0 0 (immediateProgram 0)
    (fallback ++ [.localGet (rawIndex kind)] ++
      retypeProgram (rawIndex kind) (savedIndex kind) (resultIndex kind))]

/-- The public emitter bodies expose the direct-return immediate arm and keep
the scratch cast inside the checked fallback.  The checked arm is existential
because private helper locals are intentionally not part of the proof API. -/
theorem conversionFunction_shape (kind : NatConversionKind) :
    ∃ fallback,
      (conversionFunction kind).body = [
        .localGet (conversionFunction kind).params[0]!.1,
        .i32Const .uint32 1,
        .i32And,
        .ifElse
          (immediateSource (conversionFunction kind).params[0]!.1)
          (fallback ++ [
            .localGet (conversionFunction kind).locals[0]!.1] ++
            retypeSource
              (conversionFunction kind).locals[0]!.1
              (conversionFunction kind).locals[1]!.1
              (conversionFunction kind).locals[2]!.1)] := by
  cases kind <;> refine ⟨_, rfl⟩

/-- Exact public shape, including the validation and generic limb accessor
calls used by the non-immediate arm. -/
theorem conversionFunction_shape_exact (kind : NatConversionKind) :
    (conversionFunction kind).body = [
      .localGet (conversionFunction kind).params[0]!.1,
      .i32Const .uint32 1,
      .i32And,
      .ifElse
        (immediateSource (conversionFunction kind).params[0]!.1)
        (checkedSource
            (conversionFunction kind).params[0]!.1
            (conversionFunction kind).locals[0]!.1 ++ [
          .localGet (conversionFunction kind).locals[0]!.1] ++
          retypeSource
            (conversionFunction kind).locals[0]!.1
            (conversionFunction kind).locals[1]!.1
            (conversionFunction kind).locals[2]!.1)] := by
  cases kind <;> rfl

theorem conversionFunction_locals_size (kind : NatConversionKind) :
    (conversionFunction kind).locals.size = 3 := by
  cases kind <;> rfl

/-- The adapter preserves the direct tagged decode exactly. -/
theorem instructions_immediateSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {value : Lean.FVarId}
    {valueIndex : Nat}
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some valueIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (immediateSource value) = .ok (immediateProgram valueIndex) := by
  simp [immediateSource, immediateProgram, FirTalos.instructions,
    FirTalos.instruction, valueFound, Bind.bind, Except.bind,
    pure, Except.pure]

/-- Exact adaptation of the checked arm.  The three resolved indices are
explicit so later execution proofs can attach stable contracts to precisely
the functions installed by the linker. -/
theorem instructions_checkedSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {value raw : Lean.FVarId}
    {valueIndex rawIndex validateIndex highIndex lowIndex : Nat}
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some valueIndex)
    (rawFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) raw =
        some rawIndex)
    (validateFound : FirTalos.callIndex? sourceModule (.declaration
      Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalName) =
        some validateIndex)
    (highFound : FirTalos.callIndex? sourceModule (.declaration
      Fir.Wasm.Emit.ResidentBigNumeric.naturalHighName) = some highIndex)
    (lowFound : FirTalos.callIndex? sourceModule (.declaration
      Fir.Wasm.Emit.ResidentBigNumeric.naturalLowName) = some lowIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (checkedSource value raw) =
        .ok (checkedProgram validateIndex highIndex lowIndex valueIndex
          rawIndex) := by
  simp [checkedSource, checkedProgram, FirTalos.instructions,
    FirTalos.instruction, valueFound, rawFound, validateFound, highFound,
    lowFound, Bind.bind, Except.bind, pure, Except.pure]

/-- The adapter preserves all operations in the 64-bit scratch cast. -/
theorem instructions_retypeSource
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
      (retypeSource raw saved result) =
        .ok (retypeProgram rawIndex savedIndex resultIndex) := by
  simp [retypeSource, retypeProgram, FirTalos.instructions,
    FirTalos.instruction, rawFound, savedFound, resultFound, Bind.bind,
    Except.bind, pure, Except.pure]

/-- Adapting either complete helper preserves the optimized skeleton and the
entire checked fallback. -/
theorem instructions_conversionFunctionBody_of_shape
    {sourceModule : Fir.Wasm.Module} {kind : NatConversionKind}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program}
    (shape :
      (conversionFunction kind).body = [
        .localGet (conversionFunction kind).params[0]!.1,
        .i32Const .uint32 1,
        .i32And,
        .ifElse
          (immediateSource (conversionFunction kind).params[0]!.1)
          (sourceFallback ++ [
            .localGet (conversionFunction kind).locals[0]!.1] ++
            retypeSource
              (conversionFunction kind).locals[0]!.1
              (conversionFunction kind).locals[1]!.1
              (conversionFunction kind).locals[2]!.1)])
    (fallbackAdapted : FirTalos.instructions sourceModule
      (conversionFunction kind) [] sourceFallback = .ok targetFallback) :
    FirTalos.instructions sourceModule (conversionFunction kind) []
      (conversionFunction kind).body =
        .ok (conversionProgram kind targetFallback) := by
  rw [shape]
  have valueFound : FirTalos.findFVar?
      ((conversionFunction kind).params.toList ++
        (conversionFunction kind).locals.toList)
      (conversionFunction kind).params[0]!.1 = some 0 := by
    cases kind <;> decide
  have rawFound : FirTalos.findFVar?
      ((conversionFunction kind).params.toList ++
        (conversionFunction kind).locals.toList)
      (conversionFunction kind).locals[0]!.1 = some (rawIndex kind) := by
    cases kind <;> decide
  have savedFound : FirTalos.findFVar?
      ((conversionFunction kind).params.toList ++
        (conversionFunction kind).locals.toList)
      (conversionFunction kind).locals[1]!.1 = some (savedIndex kind) := by
    cases kind <;> decide
  have resultFound : FirTalos.findFVar?
      ((conversionFunction kind).params.toList ++
        (conversionFunction kind).locals.toList)
      (conversionFunction kind).locals[2]!.1 = some (resultIndex kind) := by
    cases kind <;> decide
  have immediateAdapted := instructions_immediateSource
    (sourceModule := sourceModule) (labels := []) valueFound
  have retypeAdapted := instructions_retypeSource
    (sourceModule := sourceModule) (labels := []) rawFound savedFound resultFound
  have checkedAdapted : FirTalos.instructions sourceModule
      (conversionFunction kind) []
      (sourceFallback ++ [
        .localGet (conversionFunction kind).locals[0]!.1] ++
        retypeSource
          (conversionFunction kind).locals[0]!.1
          (conversionFunction kind).locals[1]!.1
          (conversionFunction kind).locals[2]!.1) =
        .ok (targetFallback ++ [.localGet (rawIndex kind)] ++
          retypeProgram (rawIndex kind) (savedIndex kind)
            (resultIndex kind)) := by
    rw [FirTalos.Correctness.instructions_append,
      FirTalos.Correctness.instructions_append, fallbackAdapted]
    simp [FirTalos.instructions, FirTalos.instruction, rawFound,
      retypeAdapted, Bind.bind, Except.bind, pure, Except.pure]
  have checkedAdapted' : FirTalos.instructions sourceModule
      (conversionFunction kind) []
      (sourceFallback ++
        .localGet (conversionFunction kind).locals[0]!.1 ::
          retypeSource
            (conversionFunction kind).locals[0]!.1
            (conversionFunction kind).locals[1]!.1
            (conversionFunction kind).locals[2]!.1) =
        .ok (targetFallback ++ .localGet (rawIndex kind) ::
          retypeProgram (rawIndex kind) (savedIndex kind)
            (resultIndex kind)) := by
    simpa [List.append_assoc] using checkedAdapted
  cases kind <;>
    simp [conversionProgram, rawIndex, savedIndex, resultIndex,
      FirTalos.instructions, FirTalos.instruction, valueFound,
      immediateAdapted, checkedAdapted', Bind.bind,
      Except.bind, pure, Except.pure]

theorem adaptedConversionFunction_body_of_shape
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {kind : NatConversionKind} {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program}
    (adapted : FirTalos.function sourceModule (conversionFunction kind) =
      .ok targetFunction)
    (shape :
      (conversionFunction kind).body = [
        .localGet (conversionFunction kind).params[0]!.1,
        .i32Const .uint32 1,
        .i32And,
        .ifElse
          (immediateSource (conversionFunction kind).params[0]!.1)
          (sourceFallback ++ [
            .localGet (conversionFunction kind).locals[0]!.1] ++
            retypeSource
              (conversionFunction kind).locals[0]!.1
              (conversionFunction kind).locals[1]!.1
              (conversionFunction kind).locals[2]!.1)])
    (fallbackAdapted : FirTalos.instructions sourceModule
      (conversionFunction kind) [] sourceFallback = .ok targetFallback) :
    targetFunction.body = conversionProgram kind targetFallback ++
      FirTalos.functionTerminal sourceModule (conversionFunction kind) := by
  exact ResidentNat.adaptedFunction_body_of_exact adapted
    (instructions_conversionFunctionBody_of_shape shape fallbackAdapted)

/-- Extending the decoded immediate payload to `i64` is exact. -/
theorem immediateRaw_eq_payload (payload : UInt64)
    (fits : payload.toNat ≤ maxImmediatePayload) :
    UInt64.ofNat
      (UInt32.ofNat (Word32.encodeImmediate payload.toNat fits).value >>> 1).toNat =
      payload := by
  rw [Word32.encodeImmediate_shr_one]
  have payloadLt : payload.toNat < UInt32.size := by
    unfold maxImmediatePayload at fits
    simp [UInt32.size]
    omega
  rw [UInt32.toNat_ofNat_of_lt' payloadLt]
  simp

/-- Stable proof boundary for the checked natural accessors.  Validation must
terminate first without changing the store.  The two zero-index accessor
calls then expose words whose recombination is exactly the natural modulo
`2^64`, expressed by `UInt64.ofNat`.  Implementations may use a promoted tag
or any number of heap limbs; clients do not depend on that layout choice. -/
structure CheckedNaturalCalls {host : Type}
    (env : Wasm.HostEnv host) (module : Wasm.Module)
    (validateIndex highIndex lowIndex : Nat) (store : Wasm.Store host)
    (word : UInt32) (natural : Nat) (highWord lowWord : UInt32) : Prop where
  validate : ∀ tail,
    Wasm.TerminatesWith env module validateIndex store
      (.i32 word :: tail)
      (fun final values => final = store ∧ values = tail)
  high : ∀ tail,
    Wasm.TerminatesWith env module highIndex store
      ([.i32 0, .i32 word] ++ tail)
      (fun final values => final = store ∧ values = .i32 highWord :: tail)
  low : ∀ tail,
    Wasm.TerminatesWith env module lowIndex store
      ([.i32 0, .i32 word] ++ tail)
      (fun final values => final = store ∧ values = .i32 lowWord :: tail)
  modulo :
    (UInt64.ofNat highWord.toNat <<< 32) |||
      UInt64.ofNat lowWord.toNat = UInt64.ofNat natural

/-- The checked sequence composes the validator and accessors into one exact
low-64 result.  Since the validator is the first call, malformed inputs keep
the generated helper's original trap/failure behavior; this theorem only
asserts termination when a valid `CheckedNaturalCalls` witness is available. -/
theorem wp_checkedProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals afterRaw : Wasm.Locals}
    {validateIndex highIndex lowIndex valueIndex rawIndex : Nat}
    {word : UInt32} {natural : Nat} {highWord lowWord : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (calls : CheckedNaturalCalls env module validateIndex highIndex lowIndex
      store word natural highWord lowWord)
    (valueLocal : locals.get valueIndex = some (.i32 word))
    (rawSet :
      ({ locals with values := .i64 (UInt64.ofNat natural) :: tail }).set?
        rawIndex (.i64 (UInt64.ofNat natural)) = some afterRaw)
    (continued : Wasm.wp module rest Q store
      { afterRaw with values := tail } env) :
    Wasm.wp module
      (checkedProgram validateIndex highIndex lowIndex valueIndex rawIndex ++
        rest)
      Q store { locals with values := tail } env := by
  have valueLocalWith (values : List Wasm.Value) :
      ({ locals with values := values } : Wasm.Locals).get valueIndex =
        some (.i32 word) := by
    simpa using valueLocal
  unfold checkedProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocalWith]
  apply Wasm.wp_call_tw (calls.validate tail)
  intro final values validated
  rcases validated with ⟨rfl, valuesEq⟩
  rw [valuesEq]
  simp only [Wasm.wp_localGet_cons, valueLocalWith, Wasm.wp_const_cons]
  apply Wasm.wp_call_tw (calls.high tail)
  intro final values highRead
  rcases highRead with ⟨rfl, valuesEq⟩
  rw [valuesEq]
  simp only [Wasm.wp_extendUI32_cons, Wasm.wp_constI64_cons,
    Wasm.wp_shlI64_cons]
  have shift32 : (32 % 64 : UInt64) = 32 := by decide
  rw [shift32]
  simp only [Wasm.wp_localGet_cons, valueLocalWith, Wasm.wp_const_cons]
  apply Wasm.wp_call_tw
    (calls.low (.i64 (UInt64.ofNat highWord.toNat <<< 32) :: tail))
  intro final values lowRead
  rcases lowRead with ⟨rfl, valuesEq⟩
  rw [valuesEq]
  simp only [Wasm.wp_extendUI32_cons, Wasm.wp_orI64_cons]
  rw [calls.modulo]
  simp only [Wasm.wp_localSet_cons, rawSet]
  simpa using continued

/-- The 64-bit scratch cast returns the raw USize word, preserves the caller
operand tail, and restores the complete store. -/
theorem wp_retypeProgram
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α}
    {initial afterRaw afterSaved afterResult : Wasm.Locals}
    {rawIndex savedIndex resultIndex : Nat} {rawValue : UInt64}
    {tail : List Wasm.Value}
    (pagesPositive : 0 < store.mem.pages)
    (rawNeSaved : rawIndex ≠ savedIndex)
    (savedNeResult : savedIndex ≠ resultIndex)
    (rawSet :
      ({ initial with values := .i64 rawValue :: tail }).set?
          rawIndex (.i64 rawValue) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i64 (store.mem.read64 0) :: tail }).set?
          savedIndex (.i64 (store.mem.read64 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i64 rawValue :: tail }).set?
          resultIndex (.i64 rawValue) = some afterResult)
    (returned : Q (.Return store (.i64 rawValue :: tail))) :
    Wasm.wp module (retypeProgram rawIndex savedIndex resultIndex) Q store
      { initial with values := .i64 rawValue :: tail } env := by
  have scratchInBounds :
      ¬((0 : UInt32).toNat + (0 : UInt32).toNat + 8 >
        store.mem.pages * 65536) := by
    simp
    omega
  have scratchAfterWriteInBounds :
      ¬((0 : UInt32).toNat + (0 : UInt32).toNat + 8 >
        (store.mem.write64 0 rawValue).pages * 65536) := by
    simpa [Wasm.Mem.write64] using scratchInBounds
  have rawUpdate := FirTalos.Correctness.localUpdate_of_set? rawSet
  have savedUpdate := FirTalos.Correctness.localUpdate_of_set? savedSet
  have resultUpdate := FirTalos.Correctness.localUpdate_of_set? resultSet
  have rawGet : afterSaved.get rawIndex = some (.i64 rawValue) := by
    rw [savedUpdate.2 rawNeSaved]
    exact rawUpdate.1
  have savedGet :
      afterResult.get savedIndex = some (.i64 (store.mem.read64 0)) := by
    rw [resultUpdate.2 savedNeResult]
    exact savedUpdate.1
  have resultGet : afterResult.get resultIndex = some (.i64 rawValue) :=
    resultUpdate.1
  have rawGet' :
      ({ afterSaved with values := .i32 0 :: tail }).get rawIndex =
        some (.i64 rawValue) := by simpa using rawGet
  have savedGet' :
      ({ afterResult with values := .i32 0 :: tail }).get savedIndex =
        some (.i64 (store.mem.read64 0)) := by simpa using savedGet
  have resultGet' :
      ({ afterResult with values := tail }).get resultIndex =
        some (.i64 rawValue) := by simpa using resultGet
  unfold retypeProgram
  simp only [Wasm.wp_localSet_cons, rawSet, Wasm.wp_const_cons,
    Wasm.wp_load64_cons, UInt32.add_zero, scratchInBounds, ↓reduceIte,
    Wasm.wp_localGet_cons, savedSet, rawGet', Wasm.wp_store64_cons,
    scratchAfterWriteInBounds, ResidentMemoryRel.read64_write64_self,
    resultSet, savedGet', resultGet', Wasm.wp_ret_cons]
  simpa only [ResidentMemoryRel.write64_restore] using returned

/-- The optimized arm decodes one canonical immediate word and returns the
exact `UInt64` payload directly.  Its postcondition contains the original
store and locals, making the absence of memory, allocation, ownership, and
scratch-local effects explicit. -/
theorem wp_immediateProgram
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α}
    {locals : Wasm.Locals} {valueIndex : Nat}
    {payload : UInt64} {tail : List Wasm.Value}
    (fits : payload.toNat ≤ maxImmediatePayload)
    (valueLocal : locals.get valueIndex = some (.i32 (UInt32.ofNat
      (Word32.encodeImmediate payload.toNat fits).value)))
    (returned : Q (.Return store (.i64 payload :: tail))) :
    Wasm.wp module (immediateProgram valueIndex) Q store
      { locals with values := tail } env := by
  have valueLocal' :
      ({ locals with values := tail } : Wasm.Locals).get valueIndex =
        some (.i32 (UInt32.ofNat
          (Word32.encodeImmediate payload.toNat fits).value)) := by
    simpa using valueLocal
  unfold immediateProgram
  simp only [Wasm.wp_localGet_cons, valueLocal', Wasm.wp_const_cons,
    Wasm.wp_shrU_cons, Wasm.wp_extendUI32_cons]
  have shiftOne : (1 % 32 : UInt32) = 1 := by decide
  rw [shiftOne]
  rw [immediateRaw_eq_payload payload fits]
  simpa only [Wasm.wp_ret_cons] using returned

/-- The immediate dispatcher of either conversion helper returns the exact
USize payload and leaves the checked fallback unreachable.  It requires no
memory-bound premise and preserves the store exactly because it performs no
memory, allocation, ownership, or scratch-local operation. -/
theorem wp_conversionProgramImmediate
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α}
    {locals : Wasm.Locals}
    {kind : NatConversionKind} {payload : UInt64}
    {tail : List Wasm.Value} {fallback rest : Wasm.Program}
    (fits : payload.toNat ≤ maxImmediatePayload)
    (valueLocal : locals.get 0 = some (.i32 (UInt32.ofNat
      (Word32.encodeImmediate payload.toNat fits).value)))
    (returned : Q (.Return store (.i64 payload :: tail))) :
    Wasm.wp module (conversionProgram kind fallback ++ rest) Q store
      { locals with values := tail } env := by
  have valueLocal' :
      ({ locals with values := tail } : Wasm.Locals).get 0 =
        some (.i32 (UInt32.ofNat
          (Word32.encodeImmediate payload.toNat fits).value)) := by
    simpa using valueLocal
  have selected :
      1 &&& UInt32.ofNat
        (Word32.encodeImmediate payload.toNat fits).value = 1 := by
    rw [show 1 &&& UInt32.ofNat
      (Word32.encodeImmediate payload.toNat fits).value =
        UInt32.ofNat
          (Word32.encodeImmediate payload.toNat fits).value &&& 1 by
      bv_decide]
    exact Word32.encodeImmediate_and_one payload.toNat fits
  unfold conversionProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_and_cons, selected]
  apply Wasm.wp_iff_cons rfl
  exact wp_immediateProgram fits valueLocal returned

/-- The complementary dispatcher branch validates a non-immediate natural,
reads its low limb through the stable accessor contract, and returns the
natural modulo `2^64` through the same restoring scratch cast. -/
theorem wp_conversionProgramChecked
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals afterBranch afterRaw afterSaved afterResult : Wasm.Locals}
    {kind : NatConversionKind}
    {validateIndex highIndex lowIndex : Nat}
    {word highWord lowWord : UInt32} {natural : Nat}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (calls : CheckedNaturalCalls env module validateIndex highIndex lowIndex
      store word natural highWord lowWord)
    (notImmediate : 1 &&& word = 0)
    (pagesPositive : 0 < store.mem.pages)
    (valueLocal : locals.get 0 = some (.i32 word))
    (branchSet :
      ({ locals with values := .i64 (UInt64.ofNat natural) :: tail }).set?
        (rawIndex kind) (.i64 (UInt64.ofNat natural)) = some afterBranch)
    (rawSet :
      ({ afterBranch with values := .i64 (UInt64.ofNat natural) :: tail }).set?
        (rawIndex kind) (.i64 (UInt64.ofNat natural)) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i64 (store.mem.read64 0) :: tail }).set?
        (savedIndex kind) (.i64 (store.mem.read64 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i64 (UInt64.ofNat natural) :: tail }).set?
        (resultIndex kind) (.i64 (UInt64.ofNat natural)) = some afterResult)
    (returned : Q (.Return store (.i64 (UInt64.ofNat natural) :: tail))) :
    Wasm.wp module
      (conversionProgram kind
        (checkedProgram validateIndex highIndex lowIndex 0 (rawIndex kind)) ++
        rest)
      Q store { locals with values := tail } env := by
  have valueLocal' :
      ({ locals with values := tail } : Wasm.Locals).get 0 =
        some (.i32 word) := by
    simpa using valueLocal
  unfold conversionProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_and_cons, notImmediate]
  apply Wasm.wp_iff_cons (c := (0 : UInt32)) (vs := tail) rfl
  simp only [if_neg (by simp : ¬ ((0 : UInt32) ≠ 0))]
  apply wp_checkedProgram calls valueLocal branchSet
  have branchUpdate := FirTalos.Correctness.localUpdate_of_set? branchSet
  have rawGet : afterBranch.get (rawIndex kind) =
      some (.i64 (UInt64.ofNat natural)) := branchUpdate.1
  have rawGet' :
      ({ afterBranch with values := tail } : Wasm.Locals).get
        (rawIndex kind) = some (.i64 (UInt64.ofNat natural)) := by
    simpa using rawGet
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, rawGet']
  have casted := wp_retypeProgram
    (module := module) (env := env) (Q := Q) pagesPositive
    (by cases kind <;> decide) (by cases kind <;> decide)
    rawSet savedSet resultSet returned
  simpa [retypeProgram] using casted

/-- Physical call arguments in Talos operand-stack order.  `ofNatLT` carries
one compiler-generated erased argument above the natural word. -/
def callArguments (kind : NatConversionKind) (word : UInt32) :
    List Wasm.Value :=
  match kind with
  | .plain => [.i32 word]
  | .withProof => [.i32 0, .i32 word]

/-- The immediate path of both actual adapted helpers is a fuel-free defined
call.  It returns the exact source payload as a USize word, with the store and
caller operand tail unchanged. -/
theorem terminatesWith_conversionFunctionImmediate_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {kind : NatConversionKind} {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {store : Wasm.Store host}
    {payload : UInt64} {tail : List Wasm.Value}
    (fits : payload.toNat ≤ maxImmediatePayload)
    (adapted : FirTalos.function sourceModule (conversionFunction kind) =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape :
      (conversionFunction kind).body = [
        .localGet (conversionFunction kind).params[0]!.1,
        .i32Const .uint32 1,
        .i32And,
        .ifElse
          (immediateSource (conversionFunction kind).params[0]!.1)
          (sourceFallback ++ [
            .localGet (conversionFunction kind).locals[0]!.1] ++
            retypeSource
              (conversionFunction kind).locals[0]!.1
              (conversionFunction kind).locals[1]!.1
              (conversionFunction kind).locals[2]!.1)])
    (fallbackAdapted : FirTalos.instructions sourceModule
      (conversionFunction kind) [] sourceFallback = .ok targetFallback) :
    Wasm.TerminatesWith env module functionIndex store
      (callArguments kind (UInt32.ofNat
        (Word32.encodeImmediate payload.toNat fits).value) ++ tail)
      (fun final values =>
        final = store ∧ values = .i64 payload :: tail) := by
  have signature := FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedConversionFunction_body_of_shape adapted shape
    fallbackAdapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let word := UInt32.ofNat
    (Word32.encodeImmediate payload.toNat fits).value
  let arguments := callArguments kind word ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    cases kind <;>
      simp [entry, arguments, word, callArguments, Wasm.Function.toLocals,
        Wasm.Function.numParams, paramsEq, conversionFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction]
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i64 payload :: tail)
        (.Return store [.i64 payload]) := by
    cases kind <;>
      simp [FirTalos.Correctness.FunctionBodyPost, arguments, callArguments,
        Wasm.Function.numParams, paramsEq, resultsEq, conversionFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction]
  simpa [entry, arguments, word, Wasm.Function.toLocals] using
    (wp_conversionProgramImmediate
      (module := module) (env := env) (store := store) (locals := entry)
      (fallback := targetFallback)
      (rest := FirTalos.functionTerminal sourceModule (conversionFunction kind))
      (tail := []) fits valueLocal returned)

/-- The promoted-tag and arbitrary-limb path of both actual adapted helpers
is a fuel-free defined call whenever the installed validator/accessors satisfy
`CheckedNaturalCalls`.  The result is the source Nat modulo `2^64`; validation
order, signatures, store, and caller tail are all preserved. -/
theorem terminatesWith_conversionFunctionChecked_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {kind : NatConversionKind} {store : Wasm.Store host}
    {validateIndex highIndex lowIndex : Nat}
    {word highWord lowWord : UInt32} {natural : Nat}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule (conversionFunction kind) =
      .ok targetFunction)
    (validateFound : FirTalos.callIndex? sourceModule (.declaration
      Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalName) =
        some validateIndex)
    (highFound : FirTalos.callIndex? sourceModule (.declaration
      Fir.Wasm.Emit.ResidentBigNumeric.naturalHighName) = some highIndex)
    (lowFound : FirTalos.callIndex? sourceModule (.declaration
      Fir.Wasm.Emit.ResidentBigNumeric.naturalLowName) = some lowIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (calls : CheckedNaturalCalls env module validateIndex highIndex lowIndex
      store word natural highWord lowWord)
    (notImmediate : 1 &&& word = 0)
    (pagesPositive : 0 < store.mem.pages) :
    Wasm.TerminatesWith env module functionIndex store
      (callArguments kind word ++ tail)
      (fun final values =>
        final = store ∧ values = .i64 (UInt64.ofNat natural) :: tail) := by
  have valueFound : FirTalos.findFVar?
      ((conversionFunction kind).params.toList ++
        (conversionFunction kind).locals.toList)
      (conversionFunction kind).params[0]!.1 = some 0 := by
    cases kind <;> decide
  have rawFound : FirTalos.findFVar?
      ((conversionFunction kind).params.toList ++
        (conversionFunction kind).locals.toList)
      (conversionFunction kind).locals[0]!.1 = some (rawIndex kind) := by
    cases kind <;> decide
  have fallbackAdapted : FirTalos.instructions sourceModule
      (conversionFunction kind) []
      (checkedSource
        (conversionFunction kind).params[0]!.1
        (conversionFunction kind).locals[0]!.1) =
        .ok (checkedProgram validateIndex highIndex lowIndex 0
          (rawIndex kind)) :=
    instructions_checkedSource valueFound rawFound validateFound highFound
      lowFound
  have signature := FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedConversionFunction_body_of_shape adapted
    (conversionFunction_shape_exact kind) fallbackAdapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := callArguments kind word ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    cases kind <;>
      simp [entry, arguments, callArguments, Wasm.Function.toLocals,
        Wasm.Function.numParams, paramsEq, conversionFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction]
  have targetLocalsLength : targetFunction.locals.length = 3 := by
    rw [localsEq, List.length_map, Array.length_toList,
      conversionFunction_locals_size]
  have branchValid :
      ({ entry with values := [.i64 (UInt64.ofNat natural)] }).validIndex
        (rawIndex kind) := by
    cases kind <;>
      simp [entry, arguments, callArguments, Wasm.Function.toLocals,
        Wasm.Function.numParams, paramsEq, targetLocalsLength, rawIndex,
        conversionFunction, Fir.Wasm.Emit.ResidentUSize.ofNatFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction]
  obtain ⟨afterBranch, branchSet⟩ :=
    FirTalos.Correctness.locals_set?_exists branchValid
  have branchLengths := FirTalos.Correctness.locals_lengths_of_set? branchSet
  have rawValid :
      ({ afterBranch with values := [.i64 (UInt64.ofNat natural)] }).validIndex
        (rawIndex kind) := by
    simp only [Wasm.Locals.validIndex]
    cases kind <;>
      simp [branchLengths.1, branchLengths.2, entry, arguments, callArguments,
        Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
        targetLocalsLength, rawIndex, conversionFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction]
  obtain ⟨afterRaw, rawSet⟩ :=
    FirTalos.Correctness.locals_set?_exists rawValid
  have rawLengths := FirTalos.Correctness.locals_lengths_of_set? rawSet
  have savedValid :
      ({ afterRaw with values := [.i64 (store.mem.read64 0)] }).validIndex
        (savedIndex kind) := by
    simp only [Wasm.Locals.validIndex]
    cases kind <;>
      simp [rawLengths.1, rawLengths.2, branchLengths.1, branchLengths.2,
        entry, arguments, callArguments, Wasm.Function.toLocals,
        Wasm.Function.numParams, paramsEq, targetLocalsLength, rawIndex,
        savedIndex, conversionFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction]
  obtain ⟨afterSaved, savedSet⟩ :=
    FirTalos.Correctness.locals_set?_exists savedValid
  have savedLengths := FirTalos.Correctness.locals_lengths_of_set? savedSet
  have resultValid :
      ({ afterSaved with values := [.i64 (UInt64.ofNat natural)] }).validIndex
        (resultIndex kind) := by
    simp only [Wasm.Locals.validIndex]
    cases kind <;>
      simp [savedLengths.1, savedLengths.2, rawLengths.1, rawLengths.2,
        branchLengths.1, branchLengths.2, entry, arguments, callArguments,
        Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
        targetLocalsLength, rawIndex, resultIndex, conversionFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction]
  obtain ⟨afterResult, resultSet⟩ :=
    FirTalos.Correctness.locals_set?_exists resultValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i64 (UInt64.ofNat natural) :: tail)
        (.Return store [.i64 (UInt64.ofNat natural)]) := by
    cases kind <;>
      simp [FirTalos.Correctness.FunctionBodyPost, arguments, callArguments,
        Wasm.Function.numParams, paramsEq, resultsEq, conversionFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatFunction,
        Fir.Wasm.Emit.ResidentUSize.ofNatLTFunction]
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_conversionProgramChecked
      (module := module) (env := env) (store := store) (locals := entry)
      (kind := kind) (rest := FirTalos.functionTerminal sourceModule
        (conversionFunction kind))
      (tail := []) calls notImmediate pagesPositive valueLocal branchSet
      rawSet savedSet resultSet returned)

/-- The exact physical result also satisfies W6's source-level USize value
relation. -/
theorem immediateResult_related (witness : RefinementWitness)
    (payload : UInt64) :
    ValueRel witness .usize (.word64 payload) (.usize payload) :=
  .usize

/-- Heap-classified words select the checked arm in the exact Wasm low-bit
test used by the generated helpers. -/
theorem checkedWord_selected (word : Word32)
    (heap : word.classify = .heap) :
    1 &&& UInt32.ofNat word.value = 0 := by
  have even := word.lowBit_zero_of_classify_heap heap
  apply UInt32.toNat_inj.mp
  simp [even, UInt32.toNat_ofNat_of_lt'
    (by simpa [wordModulus] using word.isLt)]

/-- Any related non-immediate `tobject`—an ordinary heap natural or a
promoted tagged natural—satisfies the checked-branch machine test. -/
theorem ObjectReferenceRel.checkedWord_selected
    {witness : RefinementWitness} {word : Word32}
    {reference : Fir.LeanIR.Impure.ObjectRef}
    (valid : witness.WellFormed)
    (related : ObjectReferenceRel witness word reference)
    (notOdd : word.value % 2 ≠ 1) :
    1 &&& UInt32.ofNat word.value = 0 :=
  ResidentUSize.checkedWord_selected word
    (related.classify_eq_heap_of_lowBit_ne_one valid notOdd)

/-- The checked modulo result is the exact W6 USize relation. -/
theorem checkedResult_related (witness : RefinementWitness) (natural : Nat) :
    ValueRel witness .usize (.word64 (UInt64.ofNat natural))
      (.usize (UInt64.ofNat natural)) :=
  .usize

end ResidentUSize

end FirTalos.Concrete
