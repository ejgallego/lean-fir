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

/-- The three bounded helpers differ only in declaration name, input ABI, and
result ABI; their physical natural-boxing body is shared. -/
inductive BoundedConversionKind where
  | uint8ToNat
  | uint8ToBitVec
  | uint16ToNat
  deriving DecidableEq

def boundedFunction : BoundedConversionKind → Fir.Wasm.Function
  | .uint8ToNat => Fir.Wasm.Emit.ResidentFixedWidth.uint8ToNatFunction
  | .uint8ToBitVec => Fir.Wasm.Emit.ResidentFixedWidth.uint8ToBitVecFunction
  | .uint16ToNat => Fir.Wasm.Emit.ResidentFixedWidth.uint16ToNatFunction

def boundedResultKind : BoundedConversionKind → Fir.Wasm.AbiKind
  | .uint8ToNat | .uint16ToNat => .tagged
  | .uint8ToBitVec => .tobject

theorem boundedFunction_valueFound (kind : BoundedConversionKind) :
    FirTalos.findFVar?
      ((boundedFunction kind).params.toList ++
        (boundedFunction kind).locals.toList)
      (boundedFunction kind).params[0]!.1 = some 0 := by
  cases kind <;> decide

theorem uint32ToNatFunction_valueFound :
    FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction.params.toList ++
        Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction.locals.toList)
      Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction.params[0]!.1 =
        some 0 := by
  decide

/-- W7's three closed bounded-helper equations instantiate the single common
source spelling. -/
theorem boundedFunction_body (kind : BoundedConversionKind) :
    (boundedFunction kind).body =
      immediateSource (boundedFunction kind).params[0]!.1
        (boundedResultKind kind) := by
  cases kind
  · rw [boundedFunction, boundedResultKind,
      Fir.Wasm.Emit.ResidentFixedWidth.uint8ToNatFunction_body]
    rfl
  · rw [boundedFunction, boundedResultKind,
      Fir.Wasm.Emit.ResidentFixedWidth.uint8ToBitVecFunction_body]
    rfl
  · rw [boundedFunction, boundedResultKind,
      Fir.Wasm.Emit.ResidentFixedWidth.uint16ToNatFunction_body]
    rfl

/-- W7's closed UInt32 equation is the exact declaration-independent split
used by the target proof. -/
theorem uint32ToNatFunction_body :
    Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction.body =
      uint32ToNatSource
        Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction.params[0]!.1 := by
  rw [Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction_body]
  rfl

/-- Every successfully adapted bounded production alias contains the common
verified target body. -/
theorem adaptedBoundedFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {kind : BoundedConversionKind}
    (adapted : FirTalos.function sourceModule (boundedFunction kind) =
      .ok targetFunction) :
    targetFunction.body = immediateProgram 0 ++
      FirTalos.functionTerminal sourceModule (boundedFunction kind) := by
  exact adaptedImmediate_body_of_shape adapted (boundedFunction_body kind)
    (boundedFunction_valueFound kind)

/-- Every successfully adapted production UInt32 helper contains the verified
two-arm target dispatcher at the resolved Natural-constructor index. -/
theorem adaptedUInt32ToNatFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {makeNaturalIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction =
        .ok targetFunction)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex) :
    targetFunction.body = uint32ToNatProgram makeNaturalIndex ++
      FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction := by
  exact adaptedUInt32ToNat_body_of_shape adapted uint32ToNatFunction_body
    uint32ToNatFunction_valueFound makeNaturalFound

/-- All bounded production aliases erase to the same physical `i32 -> i32`
signature, even though their semantic ABI annotations differ. -/
theorem boundedFunction_physicalSignature (kind : BoundedConversionKind) :
    (boundedFunction kind).params.toList.map
        (FirTalos.abiKind ∘ Prod.snd) = [.i32] ∧
      (boundedFunction kind).locals.toList.map
        (FirTalos.abiKind ∘ Prod.snd) = [] ∧
      (boundedFunction kind).results.toList.map FirTalos.abiKind = [.i32] := by
  cases kind <;> native_decide

/-- The UInt32 dispatcher has the same physical one-word call signature. -/
theorem uint32ToNatFunction_physicalSignature :
    Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction.params.toList.map
        (FirTalos.abiKind ∘ Prod.snd) = [.i32] ∧
      Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction.locals.toList.map
        (FirTalos.abiKind ∘ Prod.snd) = [] ∧
      Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction.results.toList.map
        FirTalos.abiKind = [.i32] := by
  native_decide

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

/-- The common physical word has the result relation selected by each bounded
production alias. -/
theorem boundedResultRel (witness : RefinementWitness)
    (kind : BoundedConversionKind) (value : UInt32)
    (fits : value.toNat < 2147483648) :
    ValueRel witness (boundedResultKind kind)
      (.word32 (Word32.encodeImmediate value.toNat
        (fitsImmediate_of_lt value fits)))
      (.object (.tagged (UInt64.ofNat value.toNat))) := by
  cases kind
  · exact immediateResultRel_tagged witness value fits
  · exact immediateResultRel_tobject witness value fits
  · exact immediateResultRel_tagged witness value fits

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

theorem uint8_payloadFits (value : UInt8) :
    value.toNat ≤ maxImmediatePayload := by
  exact le_trans (Nat.le_of_lt (UInt8.toNat_lt_size value)) (by decide)

theorem uint16_payloadFits (value : UInt16) :
    value.toNat ≤ maxImmediatePayload := by
  exact le_trans (Nat.le_of_lt (UInt16.toNat_lt_size value)) (by decide)

/-- `UInt8.toNat` returns the exact canonical immediate word at `.tagged`. -/
theorem uint8ToNatResultRel (witness : RefinementWitness) (value : UInt8) :
    ValueRel witness .tagged
      (.word32 (Word32.encodeImmediate value.toNat
        (uint8_payloadFits value)))
      (.object (.tagged (UInt64.ofNat value.toNat))) := by
  have fits64 : value.toNat < UInt64.size :=
    lt_trans (UInt8.toNat_lt_size value) (by decide)
  simpa [UInt64.toNat_ofNat_of_lt' fits64] using
    (ValueRel.tagged
      (TaggedReferenceRel.immediate (witness := witness)
        (UInt64.ofNat value.toNat)
        (by
          rw [UInt64.toNat_ofNat_of_lt' fits64]
          exact uint8_payloadFits value)))

/-- `UInt8.toBitVec` preserves the same Nat object word through `.tobject`. -/
theorem uint8ToBitVecResultRel (witness : RefinementWitness) (value : UInt8) :
    ValueRel witness .tobject
      (.word32 (Word32.encodeImmediate value.toNat
        (uint8_payloadFits value)))
      (.object (.tagged (UInt64.ofNat value.toNat))) :=
  ValueRel.tagged_to_tobject (uint8ToNatResultRel witness value)

/-- `UInt16.toNat` also stays inside the precise tagged representation. -/
theorem uint16ToNatResultRel (witness : RefinementWitness) (value : UInt16) :
    ValueRel witness .tagged
      (.word32 (Word32.encodeImmediate value.toNat
        (uint16_payloadFits value)))
      (.object (.tagged (UInt64.ofNat value.toNat))) := by
  have fits64 : value.toNat < UInt64.size :=
    lt_trans (UInt16.toNat_lt_size value) (by decide)
  simpa [UInt64.toNat_ofNat_of_lt' fits64] using
    (ValueRel.tagged
      (TaggedReferenceRel.immediate (witness := witness)
        (UInt64.ofNat value.toNat)
        (by
          rw [UInt64.toNat_ofNat_of_lt' fits64]
          exact uint16_payloadFits value)))

/-- Complete UInt8 execution specialization of the common target program. -/
theorem wp_uint8ImmediateProgram
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {value : UInt8} {valueIndex : Nat}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (valueLocal : locals.get valueIndex =
      some (.i32 (UInt32.ofNat value.toNat)))
    (returned : Q (.Return store
      (.i32 (UInt32.ofNat
        (Word32.encodeImmediate value.toNat
          (uint8_payloadFits value)).value) :: tail))) :
    Wasm.wp module (immediateProgram valueIndex ++ rest) Q store
      { locals with values := tail } env := by
  have fits32 : value.toNat < UInt32.size :=
    lt_trans (UInt8.toNat_lt_size value) (by decide)
  have exactValue : (UInt32.ofNat value.toNat).toNat = value.toNat :=
    UInt32.toNat_ofNat_of_lt' fits32
  have returned' : Q (.Return store
      (.i32 (UInt32.ofNat
        (Word32.encodeImmediate (UInt32.ofNat value.toNat).toNat
          (fitsImmediate_of_lt (UInt32.ofNat value.toNat)
            (uint8_fitsImmediate value))).value) :: tail)) := by
    simpa [exactValue] using returned
  exact wp_immediateProgram
    (module := module) (env := env) (store := store) (locals := locals)
    (Q := Q)
    (value := UInt32.ofNat value.toNat) (valueIndex := valueIndex)
    (tail := tail) (rest := rest) (uint8_fitsImmediate value) valueLocal
    returned'

/-- Complete UInt16 execution specialization of the common target program. -/
theorem wp_uint16ImmediateProgram
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {value : UInt16} {valueIndex : Nat}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (valueLocal : locals.get valueIndex =
      some (.i32 (UInt32.ofNat value.toNat)))
    (returned : Q (.Return store
      (.i32 (UInt32.ofNat
        (Word32.encodeImmediate value.toNat
          (uint16_payloadFits value)).value) :: tail))) :
    Wasm.wp module (immediateProgram valueIndex ++ rest) Q store
      { locals with values := tail } env := by
  have fits32 : value.toNat < UInt32.size :=
    lt_trans (UInt16.toNat_lt_size value) (by decide)
  have exactValue : (UInt32.ofNat value.toNat).toNat = value.toNat :=
    UInt32.toNat_ofNat_of_lt' fits32
  have returned' : Q (.Return store
      (.i32 (UInt32.ofNat
        (Word32.encodeImmediate (UInt32.ofNat value.toNat).toNat
          (fitsImmediate_of_lt (UInt32.ofNat value.toNat)
            (uint16_fitsImmediate value))).value) :: tail)) := by
    simpa [exactValue] using returned
  exact wp_immediateProgram
    (module := module) (env := env) (store := store) (locals := locals)
    (Q := Q)
    (value := UInt32.ofNat value.toNat) (valueIndex := valueIndex)
    (tail := tail) (rest := rest) (uint16_fitsImmediate value) valueLocal
    returned'

/-- Any successfully adapted and installed bounded production alias is a
fuel-free exact natural-boxing call.  The only emitter-specific premise is its
closed public body equation; signature erasure, control flow, physical result,
store preservation, caller-tail preservation, and the semantic result
relation are all discharged here. -/
theorem terminatesWith_boundedFunction_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {kind : BoundedConversionKind} {store : Wasm.Store host}
    {witness : RefinementWitness} {value : UInt32}
    {tail : List Wasm.Value}
    (fits : value.toNat < 2147483648)
    (adapted : FirTalos.function sourceModule (boundedFunction kind) =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape : (boundedFunction kind).body =
      immediateSource (boundedFunction kind).params[0]!.1
        (boundedResultKind kind)) :
    Wasm.TerminatesWith env module functionIndex store
      (.i32 value :: tail)
      (fun final values =>
        final = store ∧
          values = .i32 (UInt32.ofNat
            (Word32.encodeImmediate value.toNat
              (fitsImmediate_of_lt value fits)).value) :: tail ∧
          ValueRel witness (boundedResultKind kind)
            (.word32 (Word32.encodeImmediate value.toNat
              (fitsImmediate_of_lt value fits)))
            (.object (.tagged (UInt64.ofNat value.toNat)))) := by
  obtain ⟨paramsEq, localsEq, resultsEq⟩ :=
    FirTalos.Correctness.function_preserves_signature adapted
  obtain ⟨sourceParams, sourceLocals, sourceResults⟩ :=
    boundedFunction_physicalSignature kind
  have targetParams : targetFunction.params = [.i32] :=
    paramsEq.trans sourceParams
  have targetLocals : targetFunction.locals = [] :=
    localsEq.trans sourceLocals
  have targetResults : targetFunction.results = [.i32] :=
    resultsEq.trans sourceResults
  have body := adaptedImmediate_body_of_shape adapted shape
    (boundedFunction_valueFound kind)
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let word := UInt32.ofNat
    (Word32.encodeImmediate value.toNat
      (fitsImmediate_of_lt value fits)).value
  let arguments := .i32 value :: tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 value) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, targetParams, targetLocals]
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 word :: tail ∧
            ValueRel witness (boundedResultKind kind)
              (.word32 (Word32.encodeImmediate value.toNat
                (fitsImmediate_of_lt value fits)))
              (.object (.tagged (UInt64.ofNat value.toNat))))
        (.Return store [.i32 word]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, targetParams, targetResults,
      word]
    simpa using boundedResultRel witness kind value fits
  simpa [entry, arguments, word, Wasm.Function.toLocals] using
    (wp_immediateProgram
      (module := module) (env := env) (store := store) (locals := entry)
      (Q := FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 word :: tail ∧
            ValueRel witness (boundedResultKind kind)
              (.word32 (Word32.encodeImmediate value.toNat
                (fitsImmediate_of_lt value fits)))
              (.object (.tagged (UInt64.ofNat value.toNat)))))
      (value := value) (valueIndex := 0) (tail := [])
      (rest := FirTalos.functionTerminal sourceModule (boundedFunction kind))
      fits valueLocal returned)

/-- Production corollary: W7's closed body equations discharge the last
emitter-specific premise of the generic bounded-helper theorem. -/
theorem terminatesWith_boundedFunction
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {kind : BoundedConversionKind} {store : Wasm.Store host}
    {witness : RefinementWitness} {value : UInt32}
    {tail : List Wasm.Value}
    (fits : value.toNat < 2147483648)
    (adapted : FirTalos.function sourceModule (boundedFunction kind) =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction) :
    Wasm.TerminatesWith env module functionIndex store
      (.i32 value :: tail)
      (fun final values =>
        final = store ∧
          values = .i32 (UInt32.ofNat
            (Word32.encodeImmediate value.toNat
              (fitsImmediate_of_lt value fits)).value) :: tail ∧
          ValueRel witness (boundedResultKind kind)
            (.word32 (Word32.encodeImmediate value.toNat
              (fitsImmediate_of_lt value fits)))
            (.object (.tagged (UInt64.ofNat value.toNat)))) := by
  exact terminatesWith_boundedFunction_of_adapted fits adapted notImport found
    (boundedFunction_body kind)

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

/-- Semantic post shared by the two UInt32 dispatcher arms.  It permits the
constructor arm to extend the witness and change memory while retaining the
exact Nat value and physical result word. -/
def UInt32NaturalPost (witness : RefinementWitness) (value : UInt32)
    (store : Wasm.Store host) (tail : List Wasm.Value) :
    Wasm.Assertion host :=
  fun continuation =>
    ∃ word : Word32,
      continuation =
          .Return store (.i32 (UInt32.ofNat word.value) :: tail) ∧
        ValueRel witness .tobject (.word32 word)
          (.object (.tagged (UInt64.ofNat value.toNat)))

/-- Below `2^31`, UInt32 conversion satisfies the semantic Nat post with the
unchanged witness, store, memory, and caller tail. -/
theorem wp_uint32ToNatProgram_low_refines
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {witness : RefinementWitness} {value : UInt32}
    {makeNaturalIndex : Nat} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (fits : value.toNat < 2147483648)
    (valueLocal : locals.get 0 = some (.i32 value)) :
    Wasm.wp module (uint32ToNatProgram makeNaturalIndex ++ rest)
      (UInt32NaturalPost witness value store tail) store
      { locals with values := tail } env := by
  apply wp_uint32ToNatProgram_low fits valueLocal
  refine ⟨Word32.encodeImmediate value.toNat
      (fitsImmediate_of_lt value fits), rfl, ?_⟩
  exact immediateResultRel_tobject witness value fits

/-- At and above `2^31`, the unchanged constructor call's refinement is
propagated exactly through the typed return facade.  This is the stable W6
boundary for the existing promoted-Natural implementation. -/
theorem wp_uint32ToNatProgram_high_refines
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store resultStore : Wasm.Store host} {locals : Wasm.Locals}
    {nextWitness : RefinementWitness} {value : UInt32}
    {resultWord : Word32} {makeNaturalIndex : Nat}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (wide : 2147483648 ≤ value.toNat)
    (valueLocal : locals.get 0 = some (.i32 value))
    (makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        ([.i32 0, .i32 value] ++ tail)
        (fun final values =>
          final = resultStore ∧
            values = .i32 (UInt32.ofNat resultWord.value) :: tail))
    (resultRelated : ValueRel nextWitness .tobject (.word32 resultWord)
      (.object (.tagged (UInt64.ofNat value.toNat)))) :
    Wasm.wp module (uint32ToNatProgram makeNaturalIndex ++ rest)
      (UInt32NaturalPost nextWitness value resultStore tail) store
      { locals with values := tail } env := by
  apply wp_uint32ToNatProgram_high wide valueLocal makeNaturalRun
  exact ⟨resultWord, rfl, resultRelated⟩

/-- The installed production UInt32 helper is an exact canonical immediate
Nat call throughout its low range. -/
theorem terminatesWith_uint32ToNatFunction_low
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {makeNaturalIndex : Nat} {store : Wasm.Store host}
    {witness : RefinementWitness} {value : UInt32}
    {tail : List Wasm.Value}
    (fits : value.toNat < 2147483648)
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction =
        .ok targetFunction)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction) :
    Wasm.TerminatesWith env module functionIndex store
      (.i32 value :: tail)
      (fun final values =>
        final = store ∧
          values = .i32 (UInt32.ofNat
            (Word32.encodeImmediate value.toNat
              (fitsImmediate_of_lt value fits)).value) :: tail ∧
          ValueRel witness .tobject
            (.word32 (Word32.encodeImmediate value.toNat
              (fitsImmediate_of_lt value fits)))
            (.object (.tagged (UInt64.ofNat value.toNat)))) := by
  obtain ⟨paramsEq, localsEq, resultsEq⟩ :=
    FirTalos.Correctness.function_preserves_signature adapted
  obtain ⟨sourceParams, sourceLocals, sourceResults⟩ :=
    uint32ToNatFunction_physicalSignature
  have targetParams : targetFunction.params = [.i32] :=
    paramsEq.trans sourceParams
  have targetLocals : targetFunction.locals = [] :=
    localsEq.trans sourceLocals
  have targetResults : targetFunction.results = [.i32] :=
    resultsEq.trans sourceResults
  have body := adaptedUInt32ToNatFunction_body adapted makeNaturalFound
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let word := UInt32.ofNat
    (Word32.encodeImmediate value.toNat
      (fitsImmediate_of_lt value fits)).value
  let arguments := .i32 value :: tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 value) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, targetParams, targetLocals]
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 word :: tail ∧
            ValueRel witness .tobject
              (.word32 (Word32.encodeImmediate value.toNat
                (fitsImmediate_of_lt value fits)))
              (.object (.tagged (UInt64.ofNat value.toNat))))
        (.Return store [.i32 word]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, targetParams, targetResults, word]
    simpa using immediateResultRel_tobject witness value fits
  simpa [entry, arguments, word, Wasm.Function.toLocals] using
    (wp_uint32ToNatProgram_low
      (module := module) (env := env) (store := store) (locals := entry)
      (Q := FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 word :: tail ∧
            ValueRel witness .tobject
              (.word32 (Word32.encodeImmediate value.toNat
                (fitsImmediate_of_lt value fits)))
              (.object (.tagged (UInt64.ofNat value.toNat)))))
      (value := value) (makeNaturalIndex := makeNaturalIndex)
      (tail := [])
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction)
      fits valueLocal returned)

/-- The installed production UInt32 helper's high arm inherits the exact
promoted-Natural constructor refinement, including its changed store and
extended witness, while restoring the caller operand tail. -/
theorem terminatesWith_uint32ToNatFunction_high
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {makeNaturalIndex : Nat} {store resultStore : Wasm.Store host}
    {nextWitness : RefinementWitness} {value : UInt32}
    {resultWord : Word32} {tail : List Wasm.Value}
    (wide : 2147483648 ≤ value.toNat)
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction =
        .ok targetFunction)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        [.i32 0, .i32 value]
        (fun final values =>
          final = resultStore ∧
            values = [.i32 (UInt32.ofNat resultWord.value)]))
    (resultRelated : ValueRel nextWitness .tobject (.word32 resultWord)
      (.object (.tagged (UInt64.ofNat value.toNat)))) :
    Wasm.TerminatesWith env module functionIndex store
      (.i32 value :: tail)
      (fun final values =>
        final = resultStore ∧
          values = .i32 (UInt32.ofNat resultWord.value) :: tail ∧
          ValueRel nextWitness .tobject (.word32 resultWord)
            (.object (.tagged (UInt64.ofNat value.toNat)))) := by
  obtain ⟨paramsEq, localsEq, resultsEq⟩ :=
    FirTalos.Correctness.function_preserves_signature adapted
  obtain ⟨sourceParams, sourceLocals, sourceResults⟩ :=
    uint32ToNatFunction_physicalSignature
  have targetParams : targetFunction.params = [.i32] :=
    paramsEq.trans sourceParams
  have targetLocals : targetFunction.locals = [] :=
    localsEq.trans sourceLocals
  have targetResults : targetFunction.results = [.i32] :=
    resultsEq.trans sourceResults
  have body := adaptedUInt32ToNatFunction_body adapted makeNaturalFound
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := .i32 value :: tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 value) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, targetParams, targetLocals]
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = resultStore ∧
            values = .i32 (UInt32.ofNat resultWord.value) :: tail ∧
            ValueRel nextWitness .tobject (.word32 resultWord)
              (.object (.tagged (UInt64.ofNat value.toNat))))
        (.Return resultStore [.i32 (UInt32.ofNat resultWord.value)]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, targetParams, targetResults]
    simpa using resultRelated
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_uint32ToNatProgram_high
      (module := module) (env := env) (store := store)
      (resultStore := resultStore) (locals := entry) (value := value)
      (resultWord := UInt32.ofNat resultWord.value)
      (makeNaturalIndex := makeNaturalIndex) (tail := [])
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentFixedWidth.uint32ToNatFunction)
      (Q := FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = resultStore ∧
            values = .i32 (UInt32.ofNat resultWord.value) :: tail ∧
            ValueRel nextWitness .tobject (.word32 resultWord)
              (.object (.tagged (UInt64.ofNat value.toNat)))))
      wide valueLocal makeNaturalRun returned)

end ResidentFixedWidthNat

end FirTalos.Concrete
