import FirTalos.ConcreteResidentNat

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident natural multiplication refinement

This module exposes and proves the direct two-immediate branch of W7's
resident `Nat.mul` helper.  Its checked promoted/mixed/arbitrary-limb branch
is retained as the exact adapted fallback.  The immediate branch decodes both
tagged payloads, multiplies them without overflow in `i64`, splits the exact
product into low and high words, and delegates representation choice to the
stable resident natural constructor.
-/

namespace ResidentNatMul

/-- Exact Talos spelling of the direct two-immediate multiplication arm. -/
def immediateMulProgram (makeNaturalIndex : Nat) : Wasm.Program :=
  ResidentPrimitives.immediateNaturalPayload 0 ++ [.extendUI32] ++
    ResidentPrimitives.immediateNaturalPayload 1 ++ [
      .extendUI32,
      .mulI64,
      .localSet 20,
      .localGet 20,
      .wrapI64,
      .localSet 12,
      .localGet 20,
      .constI64 32,
      .shrUI64,
      .wrapI64,
      .localSet 13,
      .localGet 12,
      .localGet 13,
      .call makeNaturalIndex] ++
    ResidentNat.retypeRawObjectResultProgram 19 21 22

/-- W6-side symbolic spelling of W7's private immediate multiplication arm.
Private local identifiers are recovered positionally from the public helper. -/
def immediateMulSource (left right raw64 low high raw saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload left ++ [
    .i64ExtendI32U .uint64] ++
  Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload right ++ [
    .i64ExtendI32U .uint64,
    .i64Mul,
    .localSet raw64,
    .localGet raw64,
    .i32WrapI64 .uint32,
    .localSet low,
    .localGet raw64,
    .i64Const .uint64 32,
    .i64ShrU,
    .i32WrapI64 .uint32,
    .localSet high,
    .localGet low,
    .localGet high,
    .call (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName)] ++
  ResidentNat.retypeRawObjectResultSource raw saved result

/-- The public `Nat.mul` helper is the common immediate-pair dispatcher with
the exact arm above and the unchanged checked arbitrary-precision fallback. -/
theorem mulFunction_immediate_shape :
    ∃ fallback,
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
          (immediateMulSource
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[18]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[10]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[11]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[17]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[19]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[20]!.1)
          fallback := by
  refine ⟨_, rfl⟩

/-- Public cardinality boundary for the generated multiplication helper. -/
theorem mulFunction_locals_size :
    Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.size = 21 := by
  rfl

/-- The adapter maps the actual symbolic immediate arm to the exact Talos
program used by the execution proof. -/
theorem instructions_immediateMulSource
    {sourceModule : Fir.Wasm.Module} {makeNaturalIndex : Nat}
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction []
      (immediateMulSource
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[18]!.1
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[10]!.1
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[11]!.1
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[17]!.1
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[19]!.1
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[20]!.1) =
      .ok (immediateMulProgram makeNaturalIndex) := by
  have leftFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1 =
        some 0 := by decide
  have rightFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1 =
        some 1 := by decide
  have raw64Found : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[18]!.1 =
        some 20 := by decide
  have lowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[10]!.1 =
        some 12 := by decide
  have highFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[11]!.1 =
        some 13 := by decide
  have rawFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[17]!.1 =
        some 19 := by decide
  have savedFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[19]!.1 =
        some 21 := by decide
  have resultFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[20]!.1 =
        some 22 := by decide
  simp [immediateMulSource, immediateMulProgram,
    Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload,
    ResidentPrimitives.immediateNaturalPayload,
    ResidentNat.retypeRawObjectResultSource,
    ResidentNat.retypeRawObjectResultProgram,
    FirTalos.instructions, FirTalos.instruction, leftFound, rightFound,
    raw64Found, lowFound, highFound, rawFound, savedFound, resultFound,
    makeNaturalFound,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Exact adaptation of the complete public multiplication body.  The
checked promoted/mixed/arbitrary-limb branch is preserved byte for byte as
`targetFallback`; only the direct tagged-pair arm is exposed. -/
theorem instructions_mulFunctionBody_of_shape
    {sourceModule : Fir.Wasm.Module}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {makeNaturalIndex : Nat}
    (shape :
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
          (immediateMulSource
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[18]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[10]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[11]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[17]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[19]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[20]!.1)
          sourceFallback)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction [] sourceFallback =
        .ok targetFallback) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction []
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.body =
        .ok (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateMulProgram makeNaturalIndex) targetFallback) := by
  rw [shape]
  apply ResidentPrimitives.instructions_withImmediateNaturalPair
      (leftIndex := 0) (rightIndex := 1)
  · decide
  · decide
  · exact instructions_immediateMulSource makeNaturalFound
  · exact fallbackAdapted

/-- Successful adaptation installs precisely the exposed dispatcher followed
by the adapter's standard physical terminal suffix. -/
theorem adaptedMulFunction_body_of_shape
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {makeNaturalIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction = .ok targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
          (immediateMulSource
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[18]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[10]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[11]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[17]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[19]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[20]!.1)
          sourceFallback)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction [] sourceFallback =
        .ok targetFallback) :
    targetFunction.body =
      ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateMulProgram makeNaturalIndex) targetFallback ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction := by
  exact ResidentNat.adaptedFunction_body_of_exact adapted
    (instructions_mulFunctionBody_of_shape shape makeNaturalFound
      fallbackAdapted)

/-- The exact 64-bit product used by the direct arm. -/
def product64 (left right : UInt64) : UInt64 :=
  UInt64.ofNat left.toNat * UInt64.ofNat right.toNat

/-- Low constructor word selected from the exact 64-bit product. -/
def productLow (left right : UInt64) : UInt32 :=
  UInt32.ofNat ((product64 left right).toNat % 2 ^ 32)

/-- High constructor word selected from the exact 64-bit product. -/
def productHigh (left right : UInt64) : UInt32 :=
  UInt32.ofNat ((product64 left right >>> 32).toNat % 2 ^ 32)

/-- Two immediate payloads are at most 31 bits each, so their mathematical
product fits in the 64-bit lane and machine multiplication does not wrap. -/
theorem product64_toNat
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) :
    (product64 leftPayload rightPayload).toNat =
      leftPayload.toNat * rightPayload.toNat := by
  have productLt :
      leftPayload.toNat * rightPayload.toNat < UInt64.size := by
    have bounded := Nat.mul_le_mul pair.leftFits pair.rightFits
    unfold maxImmediatePayload at bounded
    simp [UInt64.size]
    omega
  have productLt' :
      leftPayload.toNat * rightPayload.toNat < 18446744073709551616 := by
    simpa [UInt64.size] using productLt
  unfold product64
  rw [← UInt64.ofNat_mul]
  exact UInt64.toNat_ofNat_of_lt' productLt'

/-- When the mathematical product remains tagged, the low constructor word
is the ordinary wasm32 encoding of that product. -/
theorem productLow_of_fits
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (productFits : leftPayload.toNat * rightPayload.toNat ≤
      maxImmediatePayload) :
    productLow leftPayload rightPayload =
      UInt32.ofNat (leftPayload.toNat * rightPayload.toNat) := by
  have productLt32 : leftPayload.toNat * rightPayload.toNat < 2 ^ 32 := by
    have fits := productFits
    unfold maxImmediatePayload at fits
    norm_num
    omega
  unfold productLow
  rw [product64_toNat pair, Nat.mod_eq_of_lt productLt32]

/-- A still-tagged product has no high constructor word. -/
theorem productHigh_of_fits
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (productFits : leftPayload.toNat * rightPayload.toNat ≤
      maxImmediatePayload) :
    productHigh leftPayload rightPayload = 0 := by
  have productLt32 : leftPayload.toNat * rightPayload.toNat < 2 ^ 32 := by
    have fits := productFits
    unfold maxImmediatePayload at fits
    norm_num
    omega
  unfold productHigh
  rw [UInt64.toNat_shiftRight]
  have shift32 : (32 : UInt64).toNat % 64 = 32 := by decide
  rw [shift32]
  rw [product64_toNat pair, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt productLt32]
  rfl

/-- Canonical tagged result of a two-immediate multiplication whose product
remains in the immediate range. -/
def immediateProductWord
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (_pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (productFits : leftPayload.toNat * rightPayload.toNat ≤
      maxImmediatePayload) : UInt32 :=
  UInt32.ofNat (Word32.encodeImmediate
    (leftPayload.toNat * rightPayload.toNat) productFits).value

/-- The direct multiplication arm computes the precise low/high constructor
arguments and then composes with either outcome of the canonical constructor:
an unchanged-store tagged word or a heap-extending promoted word.  No
constructor behavior is assumed beyond the supplied terminating call. -/
theorem wp_immediateMulProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store resultStore : Wasm.Store host}
    {locals afterRaw64 afterLow afterHigh afterRaw afterSaved afterResult :
      Wasm.Locals}
    {makeNaturalIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {resultWord : UInt32}
    {tail : List Wasm.Value}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (resultPagesPositive : 0 < resultStore.mem.pages)
    (leftLocal : locals.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (raw64Set :
      ({ locals with values := .i64 (product64 leftPayload rightPayload) :: tail
        }).set? 20 (.i64 (product64 leftPayload rightPayload)) =
          some afterRaw64)
    (lowSet :
      ({ afterRaw64 with values := .i32 (productLow leftPayload rightPayload) ::
        tail }).set? 12 (.i32 (productLow leftPayload rightPayload)) =
          some afterLow)
    (highSet :
      ({ afterLow with values := .i32 (productHigh leftPayload rightPayload) ::
        tail }).set? 13 (.i32 (productHigh leftPayload rightPayload)) =
          some afterHigh)
    (makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        ([.i32 (productHigh leftPayload rightPayload),
          .i32 (productLow leftPayload rightPayload)] ++ tail)
        (fun final values =>
          final = resultStore ∧ values = .i32 resultWord :: tail))
    (rawSet :
      ({ afterHigh with values := .i32 resultWord :: tail }).set? 19
        (.i32 resultWord) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (resultStore.mem.read32 0) :: tail
        }).set? 21 (.i32 (resultStore.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 resultWord :: tail }).set? 22
        (.i32 resultWord) = some afterResult)
    (returned : Q (.Return resultStore (.i32 resultWord :: tail))) :
    Wasm.wp module (immediateMulProgram makeNaturalIndex) Q store
      { locals with values := tail } env := by
  have raw64Update := FirTalos.Correctness.localUpdate_of_set? raw64Set
  have lowUpdate := FirTalos.Correctness.localUpdate_of_set? lowSet
  have highUpdate := FirTalos.Correctness.localUpdate_of_set? highSet
  have raw64AfterSet' :
      ({ afterRaw64 with values := tail } : Wasm.Locals).get 20 =
        some (.i64 (product64 leftPayload rightPayload)) := by
    simpa using raw64Update.1
  have raw64Get : afterLow.get 20 =
      some (.i64 (product64 leftPayload rightPayload)) := by
    rw [lowUpdate.2 (by decide : 20 ≠ 12)]
    exact raw64Update.1
  have raw64Get' :
      ({ afterLow with values := tail } : Wasm.Locals).get 20 =
        some (.i64 (product64 leftPayload rightPayload)) := by
    simpa using raw64Get
  have lowGet : afterHigh.get 12 =
      some (.i32 (productLow leftPayload rightPayload)) := by
    rw [highUpdate.2 (by decide : 12 ≠ 13)]
    exact lowUpdate.1
  have lowGet' :
      ({ afterHigh with values := tail } : Wasm.Locals).get 12 =
        some (.i32 (productLow leftPayload rightPayload)) := by
    simpa using lowGet
  have highGet' :
      ({ afterHigh with values :=
        (.i32 (productLow leftPayload rightPayload) :: tail) } :
          Wasm.Locals).get 13 =
        some (.i32 (productHigh leftPayload rightPayload)) := by
    simpa using highUpdate.1
  have leftLt : leftPayload.toNat < UInt32.size := by
    have fits := pair.leftFits
    unfold maxImmediatePayload at fits
    simp [UInt32.size]
    omega
  have rightLt : rightPayload.toNat < UInt32.size := by
    have fits := pair.rightFits
    unfold maxImmediatePayload at fits
    simp [UInt32.size]
    omega
  unfold immediateMulProgram
  simp only [List.append_assoc]
  apply ResidentPrimitives.wp_immediateNaturalLeftPayload pair leftLocal
  simp only [List.cons_append, List.nil_append, Wasm.wp_extendUI32_cons]
  apply ResidentPrimitives.wp_immediateNaturalRightPayload pair rightLocal
  simp only [Wasm.wp_extendUI32_cons, Wasm.wp_mulI64_cons]
  rw [UInt32.toNat_ofNat_of_lt' leftLt,
    UInt32.toNat_ofNat_of_lt' rightLt]
  change Wasm.wp module
    (.localSet 20 :: .localGet 20 :: .wrapI64 :: .localSet 12 ::
      .localGet 20 :: .constI64 32 :: .shrUI64 :: .wrapI64 ::
      .localSet 13 :: .localGet 12 :: .localGet 13 ::
      .call makeNaturalIndex ::
      ResidentNat.retypeRawObjectResultProgram 19 21 22)
    Q store
    { locals with values :=
      (.i64 (product64 leftPayload rightPayload) :: tail) } env
  simp only [Wasm.wp_localSet_cons, raw64Set, Wasm.wp_localGet_cons,
    raw64AfterSet', Wasm.wp_wrapI64_cons]
  have lowEq :
      UInt32.ofNat ((product64 leftPayload rightPayload).toNat % 2 ^ 32) =
        productLow leftPayload rightPayload := by
    rfl
  rw [lowEq]
  simp only [lowSet, raw64Get', Wasm.wp_constI64_cons,
    Wasm.wp_shrUI64_cons]
  have shift32 : (32 % 64 : UInt64) = 32 := by decide
  rw [shift32]
  simp only [Wasm.wp_wrapI64_cons]
  change Wasm.wp module
    (.localSet 13 :: .localGet 12 :: .localGet 13 ::
      .call makeNaturalIndex ::
      ResidentNat.retypeRawObjectResultProgram 19 21 22)
    Q store
    { afterLow with values :=
      (.i32 (productHigh leftPayload rightPayload) :: tail) } env
  simp only [Wasm.wp_localSet_cons, highSet, Wasm.wp_localGet_cons, lowGet',
    highGet']
  apply Wasm.wp_call_tw makeNaturalRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  exact ResidentNat.wp_retypeRawObjectResultProgram resultPagesPositive
    (by decide) (by decide) rawSet savedSet resultSet returned

/-- The shared dispatcher selects the direct multiplication arm for every
related tagged pair.  Its complete checked fallback and terminal suffix are
unreachable, while the constructor's exact store transition is retained. -/
theorem wp_immediateMulDispatch
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store resultStore : Wasm.Store host}
    {locals afterRaw64 afterLow afterHigh afterRaw afterSaved afterResult :
      Wasm.Locals}
    {makeNaturalIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {resultWord : UInt32}
    {tail : List Wasm.Value} {fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (resultPagesPositive : 0 < resultStore.mem.pages)
    (leftLocal : locals.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (raw64Set :
      ({ locals with values := .i64 (product64 leftPayload rightPayload) :: tail
        }).set? 20 (.i64 (product64 leftPayload rightPayload)) =
          some afterRaw64)
    (lowSet :
      ({ afterRaw64 with values := .i32 (productLow leftPayload rightPayload) ::
        tail }).set? 12 (.i32 (productLow leftPayload rightPayload)) =
          some afterLow)
    (highSet :
      ({ afterLow with values := .i32 (productHigh leftPayload rightPayload) ::
        tail }).set? 13 (.i32 (productHigh leftPayload rightPayload)) =
          some afterHigh)
    (makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        ([.i32 (productHigh leftPayload rightPayload),
          .i32 (productLow leftPayload rightPayload)] ++ tail)
        (fun final values =>
          final = resultStore ∧ values = .i32 resultWord :: tail))
    (rawSet :
      ({ afterHigh with values := .i32 resultWord :: tail }).set? 19
        (.i32 resultWord) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (resultStore.mem.read32 0) :: tail
        }).set? 21 (.i32 (resultStore.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 resultWord :: tail }).set? 22
        (.i32 resultWord) = some afterResult)
    (returned : Q (.Return resultStore (.i32 resultWord :: tail))) :
    Wasm.wp module
      (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateMulProgram makeNaturalIndex) fallback ++ rest)
      Q store { locals with values := tail } env := by
  apply ResidentPrimitives.wp_immediateNaturalPairDispatch pair leftLocal
    rightLocal
  apply wp_immediateMulProgram pair resultPagesPositive leftLocal rightLocal
    raw64Set lowSet highSet makeNaturalRun rawSet savedSet resultSet
  simpa using returned

/-- The direct tagged-pair path of the actual adapted resident `Nat.mul`
function is a fuel-free defined call.  It supplies the exact mathematical
product words to the canonical constructor and preserves that constructor's
choice of a tagged or promoted result, including its exact store transition.
The checked fallback is present unchanged but unreachable for this relation. -/
theorem terminatesWith_mulFunctionImmediate_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex makeNaturalIndex : Nat}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {store resultStore : Wasm.Store host}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {resultWord : UInt32}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction = .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
          (immediateMulSource
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[18]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[10]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[11]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[17]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[19]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[20]!.1)
          sourceFallback)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction [] sourceFallback =
        .ok targetFallback)
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (resultPagesPositive : 0 < resultStore.mem.pages)
    (makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        [.i32 (productHigh leftPayload rightPayload),
          .i32 (productLow leftPayload rightPayload)]
        (fun final values =>
          final = resultStore ∧ values = [.i32 resultWord])) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat rightWord.value),
        .i32 (UInt32.ofNat leftWord.value)] ++ tail)
      (fun final values =>
        final = resultStore ∧ values = .i32 resultWord :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedMulFunction_body_of_shape adapted shape
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
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction]
  have rightLocal : entry.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction]
  have targetLocalsLength : targetFunction.locals.length = 21 := by
    rw [localsEq, List.length_map, Array.length_toList,
      mulFunction_locals_size]
  have raw64Valid :
      ({ entry with values :=
        [.i64 (product64 leftPayload rightPayload)] }).validIndex 20 := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      targetLocalsLength, Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction]
  obtain ⟨afterRaw64, raw64Set⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i64 (product64 leftPayload rightPayload)) raw64Valid
  have raw64Lengths := FirTalos.Correctness.locals_lengths_of_set? raw64Set
  have lowValid :
      ({ afterRaw64 with values :=
        [.i32 (productLow leftPayload rightPayload)] }).validIndex 12 := by
    simp only [Wasm.Locals.validIndex]
    simp [raw64Lengths.1, raw64Lengths.2, entry, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, targetLocalsLength]
  obtain ⟨afterLow, lowSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 (productLow leftPayload rightPayload)) lowValid
  have lowLengths := FirTalos.Correctness.locals_lengths_of_set? lowSet
  have highValid :
      ({ afterLow with values :=
        [.i32 (productHigh leftPayload rightPayload)] }).validIndex 13 := by
    simp only [Wasm.Locals.validIndex]
    simp [lowLengths.1, lowLengths.2, raw64Lengths.1, raw64Lengths.2,
      entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      targetLocalsLength]
  obtain ⟨afterHigh, highSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 (productHigh leftPayload rightPayload)) highValid
  have highLengths := FirTalos.Correctness.locals_lengths_of_set? highSet
  have rawValid :
      ({ afterHigh with values := [.i32 resultWord] }).validIndex 19 := by
    simp only [Wasm.Locals.validIndex]
    simp [highLengths.1, highLengths.2, lowLengths.1, lowLengths.2,
      raw64Lengths.1, raw64Lengths.2, entry, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, targetLocalsLength]
  obtain ⟨afterRaw, rawSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 resultWord) rawValid
  have rawLengths := FirTalos.Correctness.locals_lengths_of_set? rawSet
  have savedValid :
      ({ afterRaw with values := [.i32 (resultStore.mem.read32 0)]
        }).validIndex 21 := by
    simp only [Wasm.Locals.validIndex]
    simp [rawLengths.1, rawLengths.2, highLengths.1, highLengths.2,
      lowLengths.1, lowLengths.2, raw64Lengths.1, raw64Lengths.2,
      entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      targetLocalsLength,
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction]
  obtain ⟨afterSaved, savedSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 (resultStore.mem.read32 0)) savedValid
  have savedLengths := FirTalos.Correctness.locals_lengths_of_set? savedSet
  have resultValid :
      ({ afterSaved with values := [.i32 resultWord] }).validIndex 22 := by
    simp only [Wasm.Locals.validIndex]
    simp [savedLengths.1, savedLengths.2, rawLengths.1, rawLengths.2,
      highLengths.1, highLengths.2, lowLengths.1, lowLengths.2,
      raw64Lengths.1, raw64Lengths.2, entry, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, targetLocalsLength,
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction]
  obtain ⟨afterResult, resultSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 resultWord) resultValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction
          ([.i32 (UInt32.ofNat rightWord.value),
            .i32 (UInt32.ofNat leftWord.value)] ++ tail)
          (fun final values =>
            final = resultStore ∧ values = .i32 resultWord :: tail)
          (.Return resultStore [.i32 resultWord]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
      paramsEq, resultsEq, Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction]
  simpa [entry, Wasm.Function.toLocals] using
    (wp_immediateMulDispatch
      (module := module) (env := env) (store := store)
      (resultStore := resultStore) (locals := entry)
      (makeNaturalIndex := makeNaturalIndex) (fallback := targetFallback)
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction)
      (tail := []) pair resultPagesPositive leftLocal rightLocal raw64Set
      lowSet highSet makeNaturalRun rawSet savedSet resultSet returned)

/-- Allocation-free specialization: when the exact product still fits the
tagged range, the actual adapted multiplication and constructor functions
return the canonical tagged product and leave the complete store unchanged. -/
theorem terminatesWith_mulFunctionImmediate_tagged_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction targetMakeNatural : Wasm.Function}
    {functionIndex makeNaturalIndex : Nat}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {store : Wasm.Store host}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction = .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
          (immediateMulSource
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[18]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[10]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[11]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[17]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[19]!.1
            Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction.locals[20]!.1)
          sourceFallback)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNatArithmetic.mulFunction [] sourceFallback =
        .ok targetFallback)
    (makeNaturalAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction =
        .ok targetMakeNatural)
    (makeNaturalNotImport : module.imports[makeNaturalIndex]? = none)
    (makeNaturalTargetFound :
      module.funcs[makeNaturalIndex - module.imports.length]? =
        some targetMakeNatural)
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (productFits : leftPayload.toNat * rightPayload.toNat ≤
      maxImmediatePayload)
    (pagesPositive : 0 < store.mem.pages) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat rightWord.value),
        .i32 (UInt32.ofNat leftWord.value)] ++ tail)
      (fun final values =>
        final = store ∧
          values = .i32 (immediateProductWord pair productFits) :: tail) := by
  have makeNaturalRun :
      Wasm.TerminatesWith env module makeNaturalIndex store
        [.i32 (productHigh leftPayload rightPayload),
          .i32 (productLow leftPayload rightPayload)]
        (fun final values =>
          final = store ∧
            values = [.i32 (immediateProductWord pair productFits)]) := by
    have constructorRun :=
      ResidentNat.terminatesWith_makeNaturalImmediate_of_adapted
        (module := module) (env := env) (store := store) (tail := [])
        makeNaturalAdapted productFits makeNaturalNotImport
        makeNaturalTargetFound
    simpa [productHigh_of_fits pair productFits,
      productLow_of_fits pair productFits, immediateProductWord] using
      constructorRun
  exact terminatesWith_mulFunctionImmediate_of_adapted
    (resultStore := store)
    (resultWord := immediateProductWord pair productFits)
    adapted notImport found shape makeNaturalFound fallbackAdapted pair
    pagesPositive makeNaturalRun

end ResidentNatMul

end FirTalos.Concrete
