import FirTalos.ConcreteResidentNat

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident natural subtraction refinement

This module exposes and proves the direct two-immediate branch of W7's
resident `Nat.sub` helper.  Its checked promoted, mixed, arbitrary-limb, and
malformed-input behavior remains the exact adapted fallback.  The fast branch
compares canonical tagged words directly and returns either tagged zero or the
canonical tagged encoding of Lean's truncated natural subtraction, without
allocating.
-/

namespace ResidentNatSub

/-- Exact Talos spelling of W7's direct two-immediate subtraction arm. -/
def immediateSubProgram : Wasm.Program := [
  .localGet 0,
  .localGet 1,
  .ltU,
  .iff 0 0
    [.const 1,
      .localSet 2]
    [.localGet 0,
      .localGet 1,
      .sub,
      .const 1,
      .add,
      .localSet 2],
  .localGet 2] ++
  ResidentNat.retypeRawObjectResultProgram 2 3 4

/-- W6-side symbolic spelling of W7's private immediate subtraction arm.
Private local identifiers are recovered positionally from the public helper. -/
def immediateSubSource (left right raw saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet left,
  .localGet right,
  .i32LtU,
  .ifElse
    [.i32Const .uint32 1,
      .localSet raw]
    [.localGet left,
      .localGet right,
      .i32Sub,
      .i32Const .uint32 1,
      .i32Add,
      .localSet raw],
  .localGet raw] ++
  ResidentNat.retypeRawObjectResultSource raw saved result

/-- The public `Nat.sub` helper is the common immediate-pair dispatcher with
the exact arm above and its unchanged checked arbitrary-precision fallback. -/
theorem natSubFunction_immediate_shape :
    ∃ fallback,
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
          (immediateSubSource
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[2]!.1)
          fallback := by
  refine ⟨_, rfl⟩

/-- Public cardinality boundary for the generated subtraction helper. -/
theorem natSubFunction_locals_size :
    Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals.size = 17 := by
  rfl

/-- The adapter maps the actual symbolic immediate arm to the exact Talos
program used by the execution proof. -/
theorem instructions_immediateSubSource
    {sourceModule : Fir.Wasm.Module} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction []
      (immediateSubSource
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[2]!.1) =
      .ok immediateSubProgram := by
  have leftFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1 =
        some 0 := by decide
  have rightFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1 =
        some 1 := by decide
  have rawFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[0]!.1 =
        some 2 := by decide
  have savedFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[1]!.1 =
        some 3 := by decide
  have resultFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[2]!.1 =
        some 4 := by decide
  simp [immediateSubSource, immediateSubProgram,
    ResidentNat.retypeRawObjectResultSource,
    ResidentNat.retypeRawObjectResultProgram,
    FirTalos.instructions, FirTalos.instruction, leftFound, rightFound,
    rawFound, savedFound, resultFound,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Exact adaptation of the complete public subtraction body.  The checked
promoted/mixed/arbitrary-limb branch is preserved verbatim as
`targetFallback`; only the tagged-pair arm is exposed. -/
theorem instructions_natSubFunctionBody_of_shape
    {sourceModule : Fir.Wasm.Module}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program}
    (shape :
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
          (immediateSubSource
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[2]!.1)
          sourceFallback)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction [] sourceFallback =
        .ok targetFallback) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction []
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.body =
        .ok (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          immediateSubProgram targetFallback) := by
  rw [shape]
  apply ResidentPrimitives.instructions_withImmediateNaturalPair
      (leftIndex := 0) (rightIndex := 1)
  · decide
  · decide
  · exact instructions_immediateSubSource
  · exact fallbackAdapted

/-- Successful adaptation installs precisely the exposed dispatcher followed
by the adapter's standard physical terminal suffix. -/
theorem adaptedNatSubFunction_body_of_shape
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction = .ok targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
          (immediateSubSource
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[2]!.1)
          sourceFallback)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction [] sourceFallback =
        .ok targetFallback) :
    targetFunction.body =
      ResidentPrimitives.immediateNaturalPairDispatch 0 1
          immediateSubProgram targetFallback ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction := by
  exact ResidentNat.adaptedFunction_body_of_exact adapted
    (instructions_natSubFunctionBody_of_shape shape fallbackAdapted)

/-- Truncated subtraction of two immediate payloads remains immediate. -/
theorem difference_fits
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) :
    leftPayload.toNat - rightPayload.toNat ≤ maxImmediatePayload :=
  Nat.le_trans (Nat.sub_le _ _) pair.leftFits

/-- Canonical physical result of Lean's truncated subtraction on a pair of
immediate natural payloads. -/
def immediateDifferenceWord
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) : UInt32 :=
  UInt32.ofNat (Word32.encodeImmediate
    (leftPayload.toNat - rightPayload.toNat) (difference_fits pair)).value

/-- W7's unsigned word operation is exactly the canonical tagged encoding of
Lean's truncated natural subtraction.  In particular, machine underflow is
never observed: the strict-order arm returns tagged zero first. -/
theorem machineDifference_eq_immediateDifferenceWord
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) :
    (if UInt32.ofNat leftWord.value < UInt32.ofNat rightWord.value then 1
      else UInt32.ofNat leftWord.value - UInt32.ofNat rightWord.value + 1) =
        immediateDifferenceWord pair := by
  suffices
      (if UInt32.ofNat leftWord.value < UInt32.ofNat rightWord.value then 1
        else UInt32.ofNat leftWord.value - UInt32.ofNat rightWord.value + 1) =
          UInt32.ofNat
            ((leftPayload.toNat - rightPayload.toNat) * 2 + 1) by
    simpa [immediateDifferenceWord, Word32.encodeImmediate] using this
  by_cases payloadLt : leftPayload.toNat < rightPayload.toNat
  · rw [if_pos (pair.wasmWords_lt_iff.mpr payloadLt)]
    simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt payloadLt)]
  · rw [if_neg (not_congr pair.wasmWords_lt_iff |>.mpr payloadLt)]
    have leftValueEq : UInt32.ofNat leftWord.value =
        UInt32.ofNat (Word32.encodeImmediate leftPayload.toNat
          pair.leftFits).value := by
      exact congrArg (fun word => UInt32.ofNat word.value) pair.leftWordEq
    have rightValueEq : UInt32.ofNat rightWord.value =
        UInt32.ofNat (Word32.encodeImmediate rightPayload.toNat
          pair.rightFits).value := by
      exact congrArg (fun word => UInt32.ofNat word.value) pair.rightWordEq
    apply UInt32.toNat_inj.mp
    have wordNotLt : ¬UInt32.ofNat leftWord.value <
        UInt32.ofNat rightWord.value :=
      not_congr pair.wasmWords_lt_iff |>.mpr payloadLt
    have wordLe : UInt32.ofNat rightWord.value ≤
        UInt32.ofNat leftWord.value := by
      rw [UInt32.le_iff_toNat_le]
      rw [UInt32.lt_iff_toNat_lt] at wordNotLt
      omega
    rw [UInt32.toNat_add]
    rw [UInt32.toNat_sub_of_le (UInt32.ofNat leftWord.value)
      (UInt32.ofNat rightWord.value) wordLe]
    rw [leftValueEq, rightValueEq]
    simp only [Word32.encodeImmediate_uint32_toNat]
    have differenceEncodedLt :
        (leftPayload.toNat - rightPayload.toNat) * 2 + 1 < UInt32.size := by
      have fits := pair.leftFits
      unfold maxImmediatePayload at fits
      simp [UInt32.size]
      omega
    have payloadLe : rightPayload.toNat ≤ leftPayload.toNat :=
      Nat.le_of_not_gt payloadLt
    rw [UInt32.toNat_ofNat_of_lt' differenceEncodedLt]
    have oneToNat : (1 : UInt32).toNat = 1 := rfl
    rw [oneToNat]
    have differenceEq :
        leftPayload.toNat * 2 + 1 - (rightPayload.toNat * 2 + 1) + 1 =
          (leftPayload.toNat - rightPayload.toNat) * 2 + 1 := by omega
    rw [differenceEq, Nat.mod_eq_of_lt differenceEncodedLt]

/-- The direct subtraction arm selects the correct truncated branch, performs
only scalar local updates, crosses the common scratch-slot object cast, and
returns with the concrete store and caller operand tail unchanged. -/
theorem wp_immediateSubProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals afterChoice afterRaw afterSaved afterResult : Wasm.Locals}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (pagesPositive : 0 < store.mem.pages)
    (leftLocal : locals.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (choiceSet :
      ({ locals with values := .i32 (immediateDifferenceWord pair) :: tail
        }).set? 2 (.i32 (immediateDifferenceWord pair)) = some afterChoice)
    (rawSet :
      ({ afterChoice with values := .i32 (immediateDifferenceWord pair) :: tail
        }).set? 2 (.i32 (immediateDifferenceWord pair)) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (store.mem.read32 0) :: tail
        }).set? 3 (.i32 (store.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 (immediateDifferenceWord pair) :: tail
        }).set? 4 (.i32 (immediateDifferenceWord pair)) = some afterResult)
    (returned :
      Q (.Return store (.i32 (immediateDifferenceWord pair) :: tail))) :
    Wasm.wp module immediateSubProgram Q store
      { locals with values := tail } env := by
  have leftLocal' : ({ locals with values := tail } : Wasm.Locals).get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)) := by simpa using leftLocal
  have rightLocal' : ({ locals with values :=
      (.i32 (UInt32.ofNat leftWord.value) :: tail) } : Wasm.Locals).get 1 =
        some (.i32 (UInt32.ofNat rightWord.value)) := by simpa using rightLocal
  have choiceUpdate := FirTalos.Correctness.localUpdate_of_set? choiceSet
  have choiceGet : ({ afterChoice with values := tail } : Wasm.Locals).get 2 =
      some (.i32 (immediateDifferenceWord pair)) := by
    simpa using choiceUpdate.1
  have finish : Wasm.wp module
      (.localGet 2 :: ResidentNat.retypeRawObjectResultProgram 2 3 4)
      Q store { afterChoice with values := tail } env := by
    simp only [Wasm.wp_localGet_cons, choiceGet]
    exact ResidentNat.wp_retypeRawObjectResultProgram pagesPositive
      (by decide) (by decide) rawSet savedSet resultSet returned
  unfold immediateSubProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    leftLocal', rightLocal']
  rw [Wasm.wp_ltU_cons]
  by_cases less : UInt32.ofNat leftWord.value < UInt32.ofNat rightWord.value
  · simp only [less, ↓reduceIte]
    apply Wasm.wp_iff_cons rfl
    rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
    have resultEq : (1 : UInt32) = immediateDifferenceWord pair := by
      have exactDifference := machineDifference_eq_immediateDifferenceWord pair
      simpa [less] using exactDifference
    have choiceSetOne :
        ({ locals with values := .i32 1 :: tail }).set? 2 (.i32 1) =
          some afterChoice := by
      simpa only [resultEq] using choiceSet
    simpa only [Wasm.wp_const_cons, Wasm.wp_localSet_cons, choiceSetOne,
      Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_localGet_cons, choiceGet] using finish
  · simp only [less, ↓reduceIte]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    have resultEq :
        UInt32.ofNat leftWord.value - UInt32.ofNat rightWord.value + 1 =
          immediateDifferenceWord pair := by
      have exactDifference := machineDifference_eq_immediateDifferenceWord pair
      simpa [less] using exactDifference
    have resultEq' :
        1 + (UInt32.ofNat leftWord.value - UInt32.ofNat rightWord.value) =
          immediateDifferenceWord pair := by
      rw [UInt32.add_comm]
      exact resultEq
    have choiceSetDifference :
        ({ locals with values := (.i32
          (1 + (UInt32.ofNat leftWord.value - UInt32.ofNat rightWord.value)) ::
            tail) }).set? 2
            (.i32 (1 + (UInt32.ofNat leftWord.value -
              UInt32.ofNat rightWord.value))) = some afterChoice := by
      simpa only [resultEq'] using choiceSet
    simp only [Wasm.wp_localGet_cons, leftLocal', rightLocal',
      Wasm.wp_sub_cons, Wasm.wp_const_cons, Wasm.wp_add_cons]
    simpa only [Wasm.wp_localSet_cons, choiceSetDifference, Wasm.wp_nil,
      List.take_zero, List.drop_zero, List.nil_append, Wasm.wp_localGet_cons,
      choiceGet] using finish

/-- The shared pair dispatcher selects the proved immediate subtraction arm
for a related pair.  The complete checked fallback and the adapter terminal
suffix are retained in the program but unreachable after the arm's return. -/
theorem wp_immediateSubDispatch
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals afterChoice afterRaw afterSaved afterResult : Wasm.Locals}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (pagesPositive : 0 < store.mem.pages)
    (leftLocal : locals.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (choiceSet :
      ({ locals with values := .i32 (immediateDifferenceWord pair) :: tail
        }).set? 2 (.i32 (immediateDifferenceWord pair)) = some afterChoice)
    (rawSet :
      ({ afterChoice with values := .i32 (immediateDifferenceWord pair) :: tail
        }).set? 2 (.i32 (immediateDifferenceWord pair)) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (store.mem.read32 0) :: tail
        }).set? 3 (.i32 (store.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 (immediateDifferenceWord pair) :: tail
        }).set? 4 (.i32 (immediateDifferenceWord pair)) = some afterResult)
    (returned :
      Q (.Return store (.i32 (immediateDifferenceWord pair) :: tail))) :
    Wasm.wp module
      (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          immediateSubProgram fallback ++ rest)
      Q store { locals with values := tail } env := by
  apply ResidentPrimitives.wp_immediateNaturalPairDispatch pair leftLocal
    rightLocal
  apply wp_immediateSubProgram pair pagesPositive leftLocal rightLocal
    choiceSet rawSet savedSet resultSet
  simpa using returned

/-- The immediate path of the actual adapted resident `Nat.sub` function is
a fuel-free defined call.  It preserves the concrete store and caller operand
tail while returning the canonical tagged representation of Lean's truncated
natural subtraction. -/
theorem terminatesWith_natSubFunctionImmediate_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {store : Wasm.Store host}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction = .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
          (immediateSubSource
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction.locals[2]!.1)
          sourceFallback)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction [] sourceFallback =
        .ok targetFallback)
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (pagesPositive : 0 < store.mem.pages) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat rightWord.value),
        .i32 (UInt32.ofNat leftWord.value)] ++ tail)
      (fun final values =>
        final = store ∧
          values = .i32 (immediateDifferenceWord pair) :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedNatSubFunction_body_of_shape adapted shape
    fallbackAdapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let entry := targetFunction.toLocals
    (([Wasm.Value.i32 (UInt32.ofNat rightWord.value),
      Wasm.Value.i32 (UInt32.ofNat leftWord.value)] ++ tail).take
        targetFunction.numParams).reverse
  have leftLocal : entry.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction]
  have rightLocal : entry.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction]
  have targetLocalsLength : targetFunction.locals.length = 17 := by
    rw [localsEq, List.length_map, Array.length_toList,
      natSubFunction_locals_size]
  have choiceValid :
      ({ entry with values := [.i32 (immediateDifferenceWord pair)]
        }).validIndex 2 := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      targetLocalsLength,
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction]
  obtain ⟨afterChoice, choiceSet⟩ :=
    FirTalos.Correctness.locals_set?_exists choiceValid
  have choiceLengths := FirTalos.Correctness.locals_lengths_of_set? choiceSet
  have rawValid :
      ({ afterChoice with values := [.i32 (immediateDifferenceWord pair)]
        }).validIndex 2 := by
    simp only [Wasm.Locals.validIndex]
    simp [choiceLengths.1, choiceLengths.2, entry, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, targetLocalsLength,
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction]
  obtain ⟨afterRaw, rawSet⟩ :=
    FirTalos.Correctness.locals_set?_exists rawValid
  have rawLengths := FirTalos.Correctness.locals_lengths_of_set? rawSet
  have savedValid :
      ({ afterRaw with values := [.i32 (store.mem.read32 0)]
        }).validIndex 3 := by
    simp only [Wasm.Locals.validIndex]
    simp [rawLengths.1, rawLengths.2, choiceLengths.1, choiceLengths.2,
      entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      targetLocalsLength,
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction]
  obtain ⟨afterSaved, savedSet⟩ :=
    FirTalos.Correctness.locals_set?_exists savedValid
  have savedLengths := FirTalos.Correctness.locals_lengths_of_set? savedSet
  have resultValid :
      ({ afterSaved with values := [.i32 (immediateDifferenceWord pair)]
        }).validIndex 4 := by
    simp only [Wasm.Locals.validIndex]
    simp [savedLengths.1, savedLengths.2, rawLengths.1, rawLengths.2,
      choiceLengths.1, choiceLengths.2, entry, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, targetLocalsLength,
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction]
  obtain ⟨afterResult, resultSet⟩ :=
    FirTalos.Correctness.locals_set?_exists resultValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction
          ([.i32 (UInt32.ofNat rightWord.value),
            .i32 (UInt32.ofNat leftWord.value)] ++ tail)
          (fun final values =>
            final = store ∧
              values = .i32 (immediateDifferenceWord pair) :: tail)
          (.Return store [.i32 (immediateDifferenceWord pair)]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
      paramsEq, resultsEq,
      Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction]
  simpa [entry, Wasm.Function.toLocals] using
    (wp_immediateSubDispatch
      (module := module) (env := env) (store := store) (locals := entry)
      (fallback := targetFallback)
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentBigNumeric.natSubFunction)
      (tail := []) pair pagesPositive leftLocal rightLocal choiceSet rawSet
      savedSet resultSet returned)

end ResidentNatSub

end FirTalos.Concrete
