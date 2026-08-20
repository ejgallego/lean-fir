import FirTalos.ConcreteResidentNat

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident natural decision refinement

This module proves the shared two-immediate branch of the generated
`Nat.decEq`, `Nat.decLt`, and `Nat.decLe` helpers once.  The checked
arbitrary-precision fallback remains an opaque adapted program and is reused
unchanged for every non-immediate pair.
-/

namespace ResidentNatDecision

abbrev DecisionKind := Fir.Wasm.Emit.ResidentBigNumeric.DecisionKind

/-- Select one of the three public generated Nat decision helpers. -/
def decisionFunction : DecisionKind → Fir.Wasm.Function
  | .eq => Fir.Wasm.Emit.ResidentBigNumeric.natDecEqFunction
  | .lt => Fir.Wasm.Emit.ResidentBigNumeric.natDecLtFunction
  | .le => Fir.Wasm.Emit.ResidentBigNumeric.natDecLeFunction

/-- Source-level `UInt8` result used by Lean's Nat decision externals. -/
def semanticDecisionResult (kind : DecisionKind) (left right : Nat) : UInt8 :=
  match kind with
  | .eq => if left = right then 1 else 0
  | .lt => if left < right then 1 else 0
  | .le => if left ≤ right then 1 else 0

/-- The target comparison word is exactly the source decision byte, embedded
in the Wasm `i32` lane. -/
theorem immediateNaturalDecisionResult_eq_semantic
    (kind : DecisionKind) (left right : UInt64) :
    ResidentPrimitives.immediateNaturalDecisionResult kind left right =
      UInt32.ofNat (semanticDecisionResult kind left.toNat right.toNat).toNat := by
  cases kind
  · by_cases equal : left.toNat = right.toNat <;>
      simp [ResidentPrimitives.immediateNaturalDecisionResult,
        semanticDecisionResult, equal]
  · by_cases less : left.toNat < right.toNat <;>
      simp [ResidentPrimitives.immediateNaturalDecisionResult,
        semanticDecisionResult, less]
  · by_cases lessEqual : left.toNat ≤ right.toNat <;>
      simp [ResidentPrimitives.immediateNaturalDecisionResult,
        semanticDecisionResult, lessEqual]

/-- W6-side symbolic spelling of the direct encoded-word comparison. -/
def immediateDecisionSource (kind : DecisionKind)
    (left right raw : Lean.FVarId) : List Fir.Wasm.Instruction :=
  [.localGet left, .localGet right] ++
    (match kind with
    | .eq => [.i32Eq]
    | .lt => [.i32LtU]
    | .le => [.i32LeU]) ++
    [.localSet raw]

/-- Source suffix after the branch has installed its normalized Boolean word.
The typed `i32 → i64 → UInt8` roundtrip carries the symbolic ABI witness while
remaining a physical identity on the already-normalized `0`/`1` value. -/
def decisionResultSource (raw : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet raw,
  .i64ExtendI32U .uint64,
  .i32WrapI64 .uint8,
  .ret]

/-- Exact Talos immediate arm, including the branch-local result write. -/
def immediateDecisionProgram (kind : DecisionKind)
    (left right raw : Nat) : Wasm.Program :=
  ResidentPrimitives.immediateNaturalDecision kind left right ++
    [.localSet raw]

/-- Exact Talos suffix returning the decision through the scalar ABI without
borrowing linear-memory scratch. -/
def decisionResultProgram (raw : Nat) : Wasm.Program := [
  .localGet raw,
  .extendUI32,
  .wrapI64,
  .ret]

/-- Complete target skeleton with an opaque checked arbitrary-precision arm. -/
def decisionProgram (kind : DecisionKind) (fallback : Wasm.Program) :
    Wasm.Program :=
  ResidentPrimitives.immediateNaturalPairDispatch 0 1
      (immediateDecisionProgram kind 0 1 2) fallback ++
    decisionResultProgram 2

/-- Every public Nat decision helper has the same dispatcher/result skeleton.
Only its comparison instruction and checked fallback differ. -/
theorem decisionFunction_shape (kind : DecisionKind) :
    ∃ fallback,
      (decisionFunction kind).body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          (decisionFunction kind).params[0]!.1
          (decisionFunction kind).params[1]!.1
          (immediateDecisionSource kind
            (decisionFunction kind).params[0]!.1
            (decisionFunction kind).params[1]!.1
            (decisionFunction kind).locals[0]!.1)
          fallback ++
        decisionResultSource
          (decisionFunction kind).locals[0]!.1 := by
  cases kind <;> refine ⟨_, rfl⟩

/-- The three generated helpers expose only their raw-result and checked-path
comparison locals. -/
theorem decisionFunction_locals_size (kind : DecisionKind) :
    (decisionFunction kind).locals.size = 2 := by
  cases kind <;> rfl

/-- Adapter preservation for the branch-local direct comparison. -/
theorem instructions_immediateDecisionSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {kind : DecisionKind}
    {left right raw : Lean.FVarId} {leftIndex rightIndex rawIndex : Nat}
    (leftFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) left =
        some leftIndex)
    (rightFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) right =
        some rightIndex)
    (rawFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) raw =
        some rawIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (immediateDecisionSource kind left right raw) =
        .ok (immediateDecisionProgram kind leftIndex rightIndex rawIndex) := by
  cases kind <;>
    simp [immediateDecisionSource, immediateDecisionProgram,
      ResidentPrimitives.immediateNaturalDecision, FirTalos.instructions,
      FirTalos.instruction, leftFound, rightFound, rawFound, Bind.bind,
      Except.bind, pure, Except.pure]

/-- Adapter preservation for the common post-dispatch result suffix. -/
theorem instructions_decisionResultSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {raw : Lean.FVarId} {rawIndex : Nat}
    (rawFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) raw =
        some rawIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (decisionResultSource raw) = .ok (decisionResultProgram rawIndex) := by
  simp [decisionResultProgram, FirTalos.instructions, FirTalos.instruction,
    decisionResultSource, rawFound, Bind.bind, Except.bind, pure, Except.pure]

/-- Exact adaptation of any public Nat decision body, preserving the complete
checked fallback as one opaque target program. -/
theorem instructions_decisionFunctionBody_of_shape
    {sourceModule : Fir.Wasm.Module} {kind : DecisionKind}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program}
    (shape :
      (decisionFunction kind).body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          (decisionFunction kind).params[0]!.1
          (decisionFunction kind).params[1]!.1
          (immediateDecisionSource kind
            (decisionFunction kind).params[0]!.1
            (decisionFunction kind).params[1]!.1
            (decisionFunction kind).locals[0]!.1)
          sourceFallback ++
        decisionResultSource
          (decisionFunction kind).locals[0]!.1)
    (fallbackAdapted : FirTalos.instructions sourceModule
      (decisionFunction kind) [] sourceFallback = .ok targetFallback) :
    FirTalos.instructions sourceModule (decisionFunction kind) []
      (decisionFunction kind).body = .ok (decisionProgram kind targetFallback) := by
  rw [shape, FirTalos.Correctness.instructions_append]
  have immediateAdapted : FirTalos.instructions sourceModule
      (decisionFunction kind) []
      (immediateDecisionSource kind
        (decisionFunction kind).params[0]!.1
        (decisionFunction kind).params[1]!.1
        (decisionFunction kind).locals[0]!.1) =
      .ok (immediateDecisionProgram kind 0 1 2) := by
    apply instructions_immediateDecisionSource
    all_goals cases kind <;> decide
  have dispatchAdapted : FirTalos.instructions sourceModule
      (decisionFunction kind) []
      (Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
        (decisionFunction kind).params[0]!.1
        (decisionFunction kind).params[1]!.1
        (immediateDecisionSource kind
          (decisionFunction kind).params[0]!.1
          (decisionFunction kind).params[1]!.1
          (decisionFunction kind).locals[0]!.1)
        sourceFallback) =
      .ok (ResidentPrimitives.immediateNaturalPairDispatch 0 1
        (immediateDecisionProgram kind 0 1 2) targetFallback) := by
    apply ResidentPrimitives.instructions_withImmediateNaturalPair
    · cases kind <;> decide
    · cases kind <;> decide
    · exact immediateAdapted
    · exact fallbackAdapted
  rw [dispatchAdapted]
  have suffixAdapted : FirTalos.instructions sourceModule
      (decisionFunction kind) []
      (decisionResultSource
        (decisionFunction kind).locals[0]!.1) =
      .ok (decisionResultProgram 2) := by
    apply instructions_decisionResultSource
    cases kind <;> decide
  rw [suffixAdapted]
  rfl

/-- Successful function adaptation installs the proved skeleton followed only
by the adapter's standard terminal suffix. -/
theorem adaptedDecisionFunction_body_of_shape
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {kind : DecisionKind} {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program}
    (adapted : FirTalos.function sourceModule (decisionFunction kind) =
      .ok targetFunction)
    (shape :
      (decisionFunction kind).body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          (decisionFunction kind).params[0]!.1
          (decisionFunction kind).params[1]!.1
          (immediateDecisionSource kind
            (decisionFunction kind).params[0]!.1
            (decisionFunction kind).params[1]!.1
            (decisionFunction kind).locals[0]!.1)
          sourceFallback ++
        decisionResultSource
          (decisionFunction kind).locals[0]!.1)
    (fallbackAdapted : FirTalos.instructions sourceModule
      (decisionFunction kind) [] sourceFallback = .ok targetFallback) :
    targetFunction.body = decisionProgram kind targetFallback ++
      FirTalos.functionTerminal sourceModule (decisionFunction kind) := by
  exact ResidentNat.adaptedFunction_body_of_exact adapted
    (instructions_decisionFunctionBody_of_shape shape fallbackAdapted)

/-- The branch-local comparison writes the exact Boolean word and otherwise
preserves the store, locals, and caller operand tail. -/
theorem wp_immediateDecisionProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals afterRaw : Wasm.Locals} {kind : DecisionKind}
    {leftIndex rightIndex rawIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (rawSet :
      ({ locals with values :=
        (.i32 (ResidentPrimitives.immediateNaturalDecisionResult
          kind leftPayload rightPayload) :: tail) }).set? rawIndex
        (.i32 (ResidentPrimitives.immediateNaturalDecisionResult
          kind leftPayload rightPayload)) = some afterRaw)
    (continued : Q (.Fallthrough store { afterRaw with values := tail })) :
    Wasm.wp module (immediateDecisionProgram kind leftIndex rightIndex rawIndex)
      Q store { locals with values := tail } env := by
  unfold immediateDecisionProgram
  apply ResidentPrimitives.wp_immediateNaturalDecision pair leftLocal rightLocal
  simp only [Wasm.wp_localSet_cons, rawSet]
  simpa using continued

/-- The shared dispatcher selects the immediate comparison and returns its raw
Boolean word through the typed scratch-free scalar roundtrip.  The store and
caller operand tail are unchanged; the checked fallback and adapter suffix are
unreachable. -/
theorem wp_immediateDecisionDispatch
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals afterBranch : Wasm.Locals}
    {kind : DecisionKind} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (branchSet :
      ({ locals with values :=
        (.i32 (ResidentPrimitives.immediateNaturalDecisionResult
          kind leftPayload rightPayload) :: tail) }).set? 2
        (.i32 (ResidentPrimitives.immediateNaturalDecisionResult
          kind leftPayload rightPayload)) = some afterBranch)
    (returned : Q (.Return store
      (.i32 (ResidentPrimitives.immediateNaturalDecisionResult
        kind leftPayload rightPayload) :: tail))) :
    Wasm.wp module (decisionProgram kind fallback ++ rest) Q store
      { locals with values := tail } env := by
  unfold decisionProgram
  rw [List.append_assoc]
  apply ResidentPrimitives.wp_immediateNaturalPairDispatch pair leftLocal
    rightLocal
  apply wp_immediateDecisionProgram pair leftLocal rightLocal branchSet
  have branchUpdate := FirTalos.Correctness.localUpdate_of_set? branchSet
  have rawGet : afterBranch.get 2 = some
      (.i32 (ResidentPrimitives.immediateNaturalDecisionResult
        kind leftPayload rightPayload)) := branchUpdate.1
  have rawGet' : ({ afterBranch with values := tail } : Wasm.Locals).get 2 =
      some (.i32 (ResidentPrimitives.immediateNaturalDecisionResult
        kind leftPayload rightPayload)) := by
    simpa using rawGet
  unfold decisionResultProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons, rawGet',
    Wasm.wp_extendUI32_cons, UInt64.ofNat_uInt32ToNat,
    Wasm.wp_wrapI64_cons]
  have retyped : UInt32.ofNat
      ((ResidentPrimitives.immediateNaturalDecisionResult kind leftPayload
        rightPayload).toUInt64.toNat % 2 ^ 32) =
      ResidentPrimitives.immediateNaturalDecisionResult kind leftPayload
        rightPayload := by
    apply UInt32.toNat_inj.mp
    simp
  rw [retyped]
  simpa only [Wasm.wp_ret_cons] using returned

/-- The immediate path of each actual adapted resident Nat decision helper is
a fuel-free defined call.  The theorem is uniform in the public helper kind:
the two encoded operands are compared directly and the exact `UInt8` result is
returned with caller tail, locals outside the result slot, and store unchanged.
The adapted checked fallback is preserved in the body but unreachable under
`ImmediateNaturalPairRel`. -/
theorem terminatesWith_decisionFunctionImmediate_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {kind : DecisionKind} {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {store : Wasm.Store host}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule (decisionFunction kind) =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape :
      (decisionFunction kind).body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          (decisionFunction kind).params[0]!.1
          (decisionFunction kind).params[1]!.1
          (immediateDecisionSource kind
            (decisionFunction kind).params[0]!.1
            (decisionFunction kind).params[1]!.1
            (decisionFunction kind).locals[0]!.1)
          sourceFallback ++
        decisionResultSource
          (decisionFunction kind).locals[0]!.1)
    (fallbackAdapted : FirTalos.instructions sourceModule
      (decisionFunction kind) [] sourceFallback = .ok targetFallback)
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat rightWord.value),
        .i32 (UInt32.ofNat leftWord.value)] ++ tail)
      (fun final values =>
        final = store ∧
          values = .i32
            (ResidentPrimitives.immediateNaturalDecisionResult kind
              leftPayload rightPayload) :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedDecisionFunction_body_of_shape adapted shape
    fallbackAdapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let entry := targetFunction.toLocals
    (([Wasm.Value.i32 (UInt32.ofNat rightWord.value),
      Wasm.Value.i32 (UInt32.ofNat leftWord.value)] ++ tail).take
        targetFunction.numParams).reverse
  have leftLocal : entry.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)) := by
    cases kind <;>
      simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
        decisionFunction, Fir.Wasm.Emit.ResidentBigNumeric.natDecEqFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecLtFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecLeFunction]
  have rightLocal : entry.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)) := by
    cases kind <;>
      simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
        decisionFunction, Fir.Wasm.Emit.ResidentBigNumeric.natDecEqFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecLtFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecLeFunction]
  have targetLocalsLength : targetFunction.locals.length = 2 := by
    rw [localsEq, List.length_map, Array.length_toList,
      decisionFunction_locals_size]
  have branchValid :
      ({ entry with values :=
        [.i32 (ResidentPrimitives.immediateNaturalDecisionResult kind
          leftPayload rightPayload)] }).validIndex 2 := by
    cases kind <;>
      simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
        targetLocalsLength, decisionFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecEqFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecLtFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecLeFunction]
  obtain ⟨afterBranch, branchSet⟩ :=
    FirTalos.Correctness.locals_set?_exists branchValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction
          ([.i32 (UInt32.ofNat rightWord.value),
            .i32 (UInt32.ofNat leftWord.value)] ++ tail)
          (fun final values =>
            final = store ∧
              values = .i32
                (ResidentPrimitives.immediateNaturalDecisionResult kind
                  leftPayload rightPayload) :: tail)
          (.Return store
            [.i32 (ResidentPrimitives.immediateNaturalDecisionResult kind
              leftPayload rightPayload)]) := by
    cases kind <;>
      simp [FirTalos.Correctness.FunctionBodyPost,
        Wasm.Function.numParams, paramsEq, resultsEq, decisionFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecEqFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecLtFunction,
        Fir.Wasm.Emit.ResidentBigNumeric.natDecLeFunction]
  simpa [entry, Wasm.Function.toLocals] using
    (wp_immediateDecisionDispatch
      (module := module) (env := env) (store := store) (locals := entry)
      (fallback := targetFallback)
      (rest := FirTalos.functionTerminal sourceModule (decisionFunction kind))
      (tail := []) pair leftLocal rightLocal branchSet returned)

/-- The direct decision result is an exact W6 `UInt8` value relation. -/
theorem immediateDecisionResult_related
    (witness : RefinementWitness) (kind : DecisionKind)
    (left right : UInt64) :
    ValueRel witness .uint8
      (.word32 (Word32.ofUInt32
        (ResidentPrimitives.immediateNaturalDecisionResult kind left right)))
      (.scalar (.uint8
        (semanticDecisionResult kind left.toNat right.toNat))) := by
  apply ValueRel.uint8
  rw [immediateNaturalDecisionResult_eq_semantic]
  simp

end ResidentNatDecision

end FirTalos.Concrete
