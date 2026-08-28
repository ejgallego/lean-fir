import Fir.Wasm.Emit.ResidentFixedWidth
import FirTalos.ConcreteResidentNat

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident fixed-width-to-Nat refinement

This module verifies the direct natural-boxing core shared by the resident
`UInt8.toNat`, `UInt8.toBitVec`, and `UInt16.toNat` helpers, together with the
two-arm `UInt32.toNat` dispatcher.  The common theorem is phrased over the
physical `UInt32` input and the exact immediate-Nat range; declaration names
enter only at the later source-shape attachment boundary.
-/

namespace ResidentFixedWidthNat

/-- The typed facade preserves the i32 word before returning it. -/
def typedReturnProgram : Wasm.Program :=
  ResidentPrimitives.unsignedI32RoundTrip ++ [.ret]

/-- Direct canonical immediate-Nat construction from one physical i32 lane. -/
def immediateProgram (valueIndex : Nat) : Wasm.Program := [
  .localGet valueIndex,
  .const 1,
  .shl,
  .const 1,
  .or] ++ typedReturnProgram

/-- UInt32 uses the direct arm below `2^31` and delegates every high-bit value
to the existing arbitrary-precision constructor with high word zero. -/
def uint32ToNatProgram (makeNaturalIndex : Nat) : Wasm.Program := [
  .localGet 0,
  .const 2147483648,
  .ltU,
  .iff 0 0
    (immediateProgram 0)
    ([.localGet 0, .const 0, .call makeNaturalIndex] ++ typedReturnProgram)]

/-- Symbolic spelling of the typed result facade shared by every direct arm. -/
def typedReturnSource (result : Fir.Wasm.AbiKind) :
    List Fir.Wasm.Instruction := [
  .i64ExtendI32U .uint64,
  .i32WrapI64 result,
  .ret]

/-- Declaration-independent source spelling of bounded natural boxing. -/
def immediateSource (value : Lean.FVarId) (result : Fir.Wasm.AbiKind) :
    List Fir.Wasm.Instruction := [
  .localGet value,
  .i32Const .uint32 1,
  .i32Shl,
  .i32Const .uint32 1,
  .i32Or] ++ typedReturnSource result

/-- Declaration-independent source spelling of the UInt32 split. -/
def uint32ToNatSource (value : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet value,
  .i32Const .uint32 2147483648,
  .i32LtU,
  .ifElse
    (immediateSource value .tobject)
    ([.localGet value,
      .i32Const .uint32 0,
      .call (.declaration
        Fir.Wasm.Emit.ResidentNumeric.makeNaturalName)] ++
      typedReturnSource .tobject)]

/-- One adapter lemma covers every bounded production alias. -/
theorem instructions_immediateSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext} {value : Lean.FVarId} {result : Fir.Wasm.AbiKind}
    {valueIndex : Nat}
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some valueIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (immediateSource value result) = .ok (immediateProgram valueIndex) := by
  simp [immediateSource, typedReturnSource, immediateProgram,
    typedReturnProgram, ResidentPrimitives.unsignedI32RoundTrip,
    FirTalos.instructions, FirTalos.instruction, valueFound, Bind.bind,
    Except.bind, pure, Except.pure]

/-- Successful function adaptation lifts the common source-shape equation to
the exact installed Talos body. -/
theorem adaptedImmediate_body_of_shape
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {targetFunction : Wasm.Function} {result : Fir.Wasm.AbiKind}
    (adapted : FirTalos.function sourceModule sourceFunction =
      .ok targetFunction)
    (shape : sourceFunction.body =
      immediateSource sourceFunction.params[0]!.1 result)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList)
        sourceFunction.params[0]!.1 = some 0) :
    targetFunction.body = immediateProgram 0 ++
      FirTalos.functionTerminal sourceModule sourceFunction := by
  apply ResidentNat.adaptedFunction_body_of_exact adapted
  rw [shape]
  exact instructions_immediateSource valueFound

/-- The adapter preserves the complete UInt32 dispatcher and its sole
constructor call. -/
theorem instructions_uint32ToNatSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext} {value : Lean.FVarId}
    {makeNaturalIndex : Nat}
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some 0)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (uint32ToNatSource value) =
        .ok (uint32ToNatProgram makeNaturalIndex) := by
  have immediateAdapted : FirTalos.instructions sourceModule sourceFunction
      (none :: labels) (immediateSource value .tobject) =
        .ok (immediateProgram 0) :=
    instructions_immediateSource valueFound
  simp [uint32ToNatSource, uint32ToNatProgram, typedReturnSource,
    typedReturnProgram, ResidentPrimitives.unsignedI32RoundTrip,
    FirTalos.instructions, FirTalos.instruction, valueFound, makeNaturalFound,
    immediateAdapted, Bind.bind, Except.bind, pure, Except.pure]

/-- Successful function adaptation lifts a UInt32 source-shape equation to
the exact installed split program. -/
theorem adaptedUInt32ToNat_body_of_shape
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {targetFunction : Wasm.Function} {makeNaturalIndex : Nat}
    (adapted : FirTalos.function sourceModule sourceFunction =
      .ok targetFunction)
    (shape : sourceFunction.body =
      uint32ToNatSource sourceFunction.params[0]!.1)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList)
        sourceFunction.params[0]!.1 = some 0)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex) :
    targetFunction.body = uint32ToNatProgram makeNaturalIndex ++
      FirTalos.functionTerminal sourceModule sourceFunction := by
  apply ResidentNat.adaptedFunction_body_of_exact adapted
  rw [shape]
  exact instructions_uint32ToNatSource valueFound makeNaturalFound

/-- Every i32 value below `2^31` fits Lean's wasm32 immediate-Nat payload. -/
theorem fitsImmediate_of_lt (value : UInt32)
    (fits : value.toNat < 2147483648) :
    value.toNat ≤ maxImmediatePayload := by
  unfold maxImmediatePayload
  omega

/-- The direct machine expression is exactly the canonical concrete Nat word. -/
theorem immediateWord_eq (value : UInt32)
    (fits : value.toNat < 2147483648) :
    (value <<< ((1 : UInt32) % 32)) ||| 1 =
      UInt32.ofNat
        (Word32.encodeImmediate value.toNat
          (fitsImmediate_of_lt value fits)).value := by
  have shiftOne : (1 % 32 : UInt32) = 1 := by decide
  rw [shiftOne]
  rw [show (value <<< (1 : UInt32)) ||| 1 =
      (value <<< (1 : UInt32)) + 1 by bv_decide]
  apply UInt32.toNat_inj.mp
  simp [Word32.encodeImmediate, UInt32.toNat_add,
    UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- The direct program returns the canonical tagged word without changing the
store or caller operand tail. -/
theorem wp_immediateProgram
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {value : UInt32} {valueIndex : Nat}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (fits : value.toNat < 2147483648)
    (valueLocal : locals.get valueIndex = some (.i32 value))
    (returned : Q (.Return store
      (.i32 (UInt32.ofNat
        (Word32.encodeImmediate value.toNat
          (fitsImmediate_of_lt value fits)).value) :: tail))) :
    Wasm.wp module (immediateProgram valueIndex ++ rest) Q store
      { locals with values := tail } env := by
  have valueLocal' :
      ({ locals with values := tail } : Wasm.Locals).get valueIndex =
        some (.i32 value) := by
    simpa using valueLocal
  unfold immediateProgram typedReturnProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_shl_cons, Wasm.wp_or_cons]
  rw [immediateWord_eq value fits]
  apply ResidentPrimitives.wp_unsignedI32RoundTrip
  simpa only [Wasm.wp_ret_cons] using returned

/-- The direct word refines the precise tagged ABI result. -/
theorem immediateResultRel_tagged (witness : RefinementWitness)
    (value : UInt32) (fits : value.toNat < 2147483648) :
    ValueRel witness .tagged
      (.word32 (Word32.encodeImmediate value.toNat
        (fitsImmediate_of_lt value fits)))
      (.object (.tagged (UInt64.ofNat value.toNat))) := by
  have fits64 : value.toNat < UInt64.size := by
    exact lt_trans fits (by decide)
  simpa [UInt64.toNat_ofNat_of_lt' fits64] using
    (ValueRel.tagged
      (TaggedReferenceRel.immediate (witness := witness)
        (UInt64.ofNat value.toNat)
        (by
          rw [UInt64.toNat_ofNat_of_lt' fits64]
          exact fitsImmediate_of_lt value fits)))

/-- The same physical direct word crosses the representation-polymorphic
object ABI used by `UInt8.toBitVec` and `UInt32.toNat`. -/
theorem immediateResultRel_tobject (witness : RefinementWitness)
    (value : UInt32) (fits : value.toNat < 2147483648) :
    ValueRel witness .tobject
      (.word32 (Word32.encodeImmediate value.toNat
        (fitsImmediate_of_lt value fits)))
      (.object (.tagged (UInt64.ofNat value.toNat))) :=
  ValueRel.tagged_to_tobject (immediateResultRel_tagged witness value fits)

/-- UInt8's complete value range selects the common immediate program. -/
theorem uint8_fitsImmediate (value : UInt8) :
    (UInt32.ofNat value.toNat).toNat < 2147483648 := by
  rw [UInt32.toNat_ofNat_of_lt' (lt_trans (UInt8.toNat_lt_size value)
    (by decide))]
  exact lt_trans (UInt8.toNat_lt_size value) (by decide)

/-- UInt16's complete value range selects the common immediate program. -/
theorem uint16_fitsImmediate (value : UInt16) :
    (UInt32.ofNat value.toNat).toNat < 2147483648 := by
  rw [UInt32.toNat_ofNat_of_lt' (lt_trans (UInt16.toNat_lt_size value)
    (by decide))]
  exact lt_trans (UInt16.toNat_lt_size value) (by decide)

/-- The low UInt32 arm selects the direct canonical boxing program. -/
theorem wp_uint32ToNatProgram_low
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {value : UInt32} {makeNaturalIndex : Nat}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (fits : value.toNat < 2147483648)
    (valueLocal : locals.get 0 = some (.i32 value))
    (returned : Q (.Return store
      (.i32 (UInt32.ofNat
        (Word32.encodeImmediate value.toNat
          (fitsImmediate_of_lt value fits)).value) :: tail))) :
    Wasm.wp module (uint32ToNatProgram makeNaturalIndex ++ rest) Q store
      { locals with values := tail } env := by
  have valueLocal' :
      ({ locals with values := tail } : Wasm.Locals).get 0 =
        some (.i32 value) := by
    simpa using valueLocal
  have selected : value < (2147483648 : UInt32) := by
    rw [UInt32.lt_iff_toNat_lt]
    simpa using fits
  unfold uint32ToNatProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_ltU_cons, if_pos selected]
  apply Wasm.wp_iff_cons rfl
  exact wp_immediateProgram fits valueLocal returned

/-- The high UInt32 arm preserves the exact constructor call, its store
transition, its result word, and the caller operand tail. -/
theorem wp_uint32ToNatProgram_high
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store resultStore : Wasm.Store host}
    {locals : Wasm.Locals} {value resultWord : UInt32}
    {makeNaturalIndex : Nat} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (wide : 2147483648 ≤ value.toNat)
    (valueLocal : locals.get 0 = some (.i32 value))
    (makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        ([.i32 0, .i32 value] ++ tail)
        (fun final values =>
          final = resultStore ∧ values = .i32 resultWord :: tail))
    (returned : Q (.Return resultStore (.i32 resultWord :: tail))) :
    Wasm.wp module (uint32ToNatProgram makeNaturalIndex ++ rest) Q store
      { locals with values := tail } env := by
  have valueLocal' :
      ({ locals with values := tail } : Wasm.Locals).get 0 =
        some (.i32 value) := by
    simpa using valueLocal
  have notSelected : ¬ value < (2147483648 : UInt32) := by
    rw [UInt32.lt_iff_toNat_lt]
    simp
    omega
  unfold uint32ToNatProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_ltU_cons,
    if_neg notSelected]
  apply Wasm.wp_iff_cons (c := (0 : UInt32)) (vs := tail) rfl
  simp only [if_neg (by simp : ¬ ((0 : UInt32) ≠ 0)),
    Wasm.wp_localGet_cons, valueLocal', Wasm.wp_const_cons]
  apply Wasm.wp_call_tw makeNaturalRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  apply ResidentPrimitives.wp_unsignedI32RoundTrip
  simpa only [Wasm.wp_ret_cons] using returned

end ResidentFixedWidthNat

end FirTalos.Concrete
