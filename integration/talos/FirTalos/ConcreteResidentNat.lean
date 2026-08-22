import Fir.Wasm.Emit.ResidentNatArithmetic
import FirTalos.ConcreteResidentBigNumericAllocator
import FirTalos.ConcreteRuntime
import FirTalos.ConcreteResidentPrimitives
import FirTalos.Correctness.Adapter
import FirTalos.Correctness.Function
import FirTalos.Correctness.Locals
import Interpreter.Wasm.Wp.Loop
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

/-- Generic bridge from exact body adaptation to the body installed in the
target function.  Resident operation proofs can expose their own scalar
skeleton without repeating the adapter bookkeeping for the terminal suffix. -/
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

/-- Symbolic-emitter spelling of the natural constructor's scalar control
skeleton.  Allocation branches remain parameters so the immediate proof does
not depend on their private helper-local implementation. -/
def makeNaturalSourceProgram (low high : Lean.FVarId)
    (lowOverflow highNonzero big : List Fir.Wasm.Instruction) :
    List Fir.Wasm.Instruction := [
  .localGet high,
  .i32Const .uint32 2147483648,
  .i32LtU,
  .ifElse
    ([.localGet high,
      .i32Const .uint32 0,
      .i32Eq,
      .ifElse
        [.localGet low,
          .i32Const .uint32 2147483648,
          .i32LtU,
          .ifElse
            [.localGet low,
              .localGet low,
              .i32Add,
              .i32Const .uint32 1,
              .i32Add,
              .ret]
            lowOverflow]
        highNonzero])
    big]

/-- The public resident constructor has exactly the W6-spelled scalar
skeleton with three opaque allocation alternatives. -/
theorem makeNaturalFunction_shape :
    ∃ lowOverflow highNonzero big,
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.body =
        makeNaturalSourceProgram
          Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params[1]!.1
          lowOverflow highNonzero big := by
  refine ⟨_, _, _, rfl⟩

/-- Adapting the symbolic scalar skeleton preserves its shape exactly; only
the three opaque allocation alternatives need independent adaptation. -/
theorem instructions_makeNaturalSourceProgram
    {sourceModule : Fir.Wasm.Module}
    {sourceLowOverflow sourceHighNonzero sourceBig :
      List Fir.Wasm.Instruction}
    {targetLowOverflow targetHighNonzero targetBig : Wasm.Program}
    (lowAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction [] sourceLowOverflow =
        .ok targetLowOverflow)
    (highAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction [] sourceHighNonzero =
        .ok targetHighNonzero)
    (bigAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction [] sourceBig =
        .ok targetBig) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction []
      (makeNaturalSourceProgram
        Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params[1]!.1
        sourceLowOverflow sourceHighNonzero sourceBig) =
      .ok (makeNaturalProgram targetLowOverflow targetHighNonzero targetBig) := by
  have lowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params[0]!.1 =
        some 0 := by decide
  have highFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params[1]!.1 =
        some 1 := by decide
  simp [makeNaturalSourceProgram, makeNaturalProgram, FirTalos.instructions,
    FirTalos.instruction, lowFound, highFound, lowAdapted, highAdapted,
    bigAdapted, Bind.bind, Except.bind, pure, Except.pure]

/-- For a low word in the immediate range and zero high word, the prefix of
the actual constructor follows only scalar instructions and returns the
canonical tagged representation. Empty alternatives stand for allocation
branches that are unreachable under these premises. -/
theorem wp_makeNaturalImmediateProgram
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α}
    {lowOverflow highNonzero big rest : Wasm.Program}
    {payload : Nat} (fits : payload ≤ maxImmediatePayload)
    (returned : Q (.Return store [
      .i32 (UInt32.ofNat (Word32.encodeImmediate payload fits).value)])) :
    Wasm.wp module (makeNaturalProgram lowOverflow highNonzero big ++ rest) Q store
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
  simp only [List.cons_append, List.nil_append]
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
    (lowOverflow highNonzero big : Wasm.Program)
    (rest : Wasm.Program := []) : Wasm.Function := {
  params := [.i32, .i32]
  locals := []
  results := [.i32]
  body := makeNaturalProgram lowOverflow highNonzero big ++ rest }

/-- Successful adaptation of the public resident constructor produces the
exact target skeleton used by the scalar proof.  The three allocation
alternatives are existential because their implementation is irrelevant to
the immediate path; the adapter's physical terminal suffix is retained
exactly. -/
theorem makeNaturalTargetFunction_of_adapted
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction = .ok targetFunction) :
    ∃ lowOverflow highNonzero big,
      targetFunction = makeNaturalTargetFunction lowOverflow highNonzero big
        (FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction) := by
  obtain ⟨sourceLowOverflow, sourceHighNonzero, sourceBig, sourceShape⟩ :=
    makeNaturalFunction_shape
  have lowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params[0]!.1 =
        some 0 := by decide
  have highFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction.params[1]!.1 =
        some 1 := by decide
  unfold FirTalos.function at adapted
  cases lowAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction []
      sourceLowOverflow with
  | error error =>
      rw [sourceShape] at adapted
      simp [makeNaturalSourceProgram,
        FirTalos.instructions, FirTalos.instruction, lowFound, highFound,
        lowAdapted, Bind.bind, Except.bind, pure, Except.pure] at adapted
  | ok lowOverflow =>
      cases highAdapted : FirTalos.instructions sourceModule
          Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction []
          sourceHighNonzero with
      | error error =>
          rw [sourceShape] at adapted
          simp [makeNaturalSourceProgram,
            FirTalos.instructions, FirTalos.instruction, lowFound, highFound,
            lowAdapted, highAdapted, Bind.bind, Except.bind, pure,
            Except.pure] at adapted
      | ok highNonzero =>
          cases bigAdapted : FirTalos.instructions sourceModule
              Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction [] sourceBig with
          | error error =>
              rw [sourceShape] at adapted
              simp [makeNaturalSourceProgram,
                FirTalos.instructions, FirTalos.instruction, lowFound,
                highFound, lowAdapted, highAdapted, bigAdapted, Bind.bind,
                Except.bind, pure, Except.pure] at adapted
          | ok big =>
              have bodyAdapted := instructions_makeNaturalSourceProgram
                lowAdapted highAdapted bigAdapted
              rw [sourceShape, bodyAdapted] at adapted
              simp only [Bind.bind, Except.bind, pure,
                Except.pure, Except.ok.injEq] at adapted
              subst targetFunction
              exact ⟨lowOverflow, highNonzero, big, rfl⟩

/-- Fuel-free, store-specific call theorem for the immediate constructor
path. This is the call boundary consumed by arithmetic helpers; unlike a
global `FuncSpec`, it can state that the current store is exactly unchanged. -/
theorem terminatesWith_makeNaturalImmediate
    {host : Type} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {functionIndex : Nat}
    {store : Wasm.Store host}
    {payload : Nat} {tail : List Wasm.Value}
    {lowOverflow highNonzero big rest : Wasm.Program}
    (fits : payload ≤ maxImmediatePayload)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some (makeNaturalTargetFunction lowOverflow highNonzero big rest)) :
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

/-- The immediate constructor theorem for the actual public helper after
successful FIR-to-Talos adaptation.  Consumers no longer provide or trust a
hand-written target body: its exact scalar skeleton follows from adaptation. -/
theorem terminatesWith_makeNaturalImmediate_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {targetFunction : Wasm.Function}
    {functionIndex : Nat} {store : Wasm.Store host}
    {payload : Nat} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction = .ok targetFunction)
    (fits : payload ≤ maxImmediatePayload)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 0, .i32 (UInt32.ofNat payload)] ++ tail)
      (fun final values =>
        final = store ∧
          values =
            .i32 (UInt32.ofNat (Word32.encodeImmediate payload fits).value) ::
              tail) := by
  obtain ⟨lowOverflow, highNonzero, big, targetShape⟩ :=
    makeNaturalTargetFunction_of_adapted adapted
  rw [targetShape] at found
  exact terminatesWith_makeNaturalImmediate fits notImport found

/-- Shared Talos spelling of the resident unsigned 64-bit sum skeleton.
The final call chooses whether the same carry-propagation code constructs a
natural or an integer. -/
def unsignedSumProgram (makeIndex : Nat) : Wasm.Program := [
  .localGet 0,
  .localGet 2,
  .add,
  .localSet 4,
  .localGet 4,
  .localGet 0,
  .ltU,
  .localSet 6,
  .localGet 1,
  .localGet 3,
  .add,
  .localSet 5,
  .localGet 5,
  .localGet 1,
  .ltU,
  .iff 0 0 [.unreachable] [],
  .localGet 5,
  .localGet 6,
  .add,
  .localSet 5,
  .localGet 5,
  .localGet 6,
  .ltU,
  .iff 0 0 [.unreachable] [],
  .localGet 4,
  .localGet 5,
  .call makeIndex,
  .ret]

/-- Symbolic-emitter spelling of the same carry-propagation primitive. -/
def unsignedSumSourceProgram
    (leftLow leftHigh rightLow rightHigh low high carry : Lean.FVarId)
    (make : Lean.Name) : List Fir.Wasm.Instruction := [
  .localGet leftLow,
  .localGet rightLow,
  .i32Add,
  .localSet low,
  .localGet low,
  .localGet leftLow,
  .i32LtU,
  .localSet carry,
  .localGet leftHigh,
  .localGet rightHigh,
  .i32Add,
  .localSet high,
  .localGet high,
  .localGet leftHigh,
  .i32LtU,
  .ifElse [.unreachable] [],
  .localGet high,
  .localGet carry,
  .i32Add,
  .localSet high,
  .localGet high,
  .localGet carry,
  .i32LtU,
  .ifElse [.unreachable] [],
  .localGet low,
  .localGet high,
  .call (.declaration make),
  .ret]

/-- The public natural-sum helper is an instance of the shared unsigned-sum
skeleton. -/
theorem naturalSumFunction_shape :
    Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.body =
      unsignedSumSourceProgram
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params[2]!.1
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params[3]!.1
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals[0]!.1
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals[1]!.1
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals[2]!.1
        Fir.Wasm.Emit.ResidentNumeric.makeNaturalName := by
  rfl

/-- Adapting the shared unsigned-sum source skeleton yields the exact Talos
program whenever its constructor declaration resolves. -/
theorem instructions_naturalSumSourceProgram
    {sourceModule : Fir.Wasm.Module} {makeIndex : Nat}
    (makeFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction []
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.body =
        .ok (unsignedSumProgram makeIndex) := by
  have leftLowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params[0]!.1 =
        some 0 := by decide
  have leftHighFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params[1]!.1 =
        some 1 := by decide
  have rightLowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params[2]!.1 =
        some 2 := by decide
  have rightHighFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params[3]!.1 =
        some 3 := by decide
  have lowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals[0]!.1 =
        some 4 := by decide
  have highFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals[1]!.1 =
        some 5 := by decide
  have carryFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.params.toList ++
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals.toList)
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction.locals[2]!.1 =
        some 6 := by decide
  rw [naturalSumFunction_shape]
  simp [unsignedSumSourceProgram, unsignedSumProgram, FirTalos.instructions,
    FirTalos.instruction, leftLowFound, leftHighFound, rightLowFound,
    rightHighFound, lowFound, highFound, carryFound, makeFound, Bind.bind,
    Except.bind, pure, Except.pure]

/-- Exact adapted target for the public natural-sum helper, including the
adapter's physical terminal suffix. -/
def naturalSumTargetFunction (makeIndex : Nat)
    (rest : Wasm.Program := []) : Wasm.Function := {
  params := [.i32, .i32, .i32, .i32]
  locals := [.i32, .i32, .i32]
  results := [.i32]
  body := unsignedSumProgram makeIndex ++ rest }

theorem naturalSumTargetFunction_of_adapted
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {makeIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction = .ok targetFunction)
    (makeFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeIndex) :
    targetFunction = naturalSumTargetFunction makeIndex
      (FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction) := by
  have bodyAdapted := instructions_naturalSumSourceProgram makeFound
  unfold FirTalos.function at adapted
  rw [bodyAdapted] at adapted
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at adapted
  subst targetFunction
  rfl

def unsignedSumLow (leftLow rightLow : UInt32) : UInt32 :=
  rightLow + leftLow

def unsignedSumCarry (leftLow rightLow : UInt32) : UInt32 :=
  if unsignedSumLow leftLow rightLow < leftLow then 1 else 0

def unsignedSumHighBase (leftHigh rightHigh : UInt32) : UInt32 :=
  rightHigh + leftHigh

def unsignedSumHigh (leftLow leftHigh rightLow rightHigh : UInt32) : UInt32 :=
  unsignedSumCarry leftLow rightLow +
    unsignedSumHighBase leftHigh rightHigh

/-- Generic execution contract for the factored unsigned-sum primitive.  It
is independent of the logical result type: the caller supplies the final
constructor run, while the theorem proves carry propagation, both overflow
guards, exact store threading, and the outer return convention. -/
theorem terminatesWith_unsignedSum
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {functionIndex makeIndex : Nat} {store : Wasm.Store host}
    {leftLow leftHigh rightLow rightHigh result : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (highBaseNoOverflow :
      ¬ unsignedSumHighBase leftHigh rightHigh < leftHigh)
    (highCarryNoOverflow :
      ¬ unsignedSumHigh leftLow leftHigh rightLow rightHigh <
        unsignedSumCarry leftLow rightLow)
    (makeRun : Wasm.TerminatesWith env module makeIndex store
      [.i32 ((if rightLow + leftLow < leftLow then (1 : UInt32) else 0) +
          (rightHigh + leftHigh)),
        .i32 (rightLow + leftLow)]
      (fun final values => final = store ∧ values = [.i32 result]))
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some (naturalSumTargetFunction makeIndex rest)) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 rightHigh, .i32 rightLow, .i32 leftHigh, .i32 leftLow] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 result :: tail) := by
  change ¬ rightHigh + leftHigh < leftHigh at highBaseNoOverflow
  change Not (((if rightLow + leftLow < leftLow then (1 : UInt32) else 0) + (rightHigh + leftHigh)) < (if rightLow + leftLow < leftLow then (1 : UInt32) else 0)) at highCarryNoOverflow
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  unfold naturalSumTargetFunction
  simp [Wasm.Function.toLocals, Wasm.Function.numParams]
  unfold unsignedSumProgram
  simp only [List.cons_append, List.nil_append]
  wp_run
  simp [highBaseNoOverflow]
  apply Wasm.wp_iff_cons rfl
  wp_run
  simp [highCarryNoOverflow]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide), Wasm.wp_nil]
  simp only [List.take_zero, List.drop_nil, List.nil_append]
  wp_run
  apply Wasm.wp_call_tw makeRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  wp_run
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams]

/-- Store-evolving form of `terminatesWith_unsignedSum`.  The arithmetic
helper itself performs only scalar work, but its final constructor may
allocate a promoted or ordinary Natural in linear memory.  This theorem
threads that exact successor store through the actual adapted helper call. -/
theorem terminatesWith_unsignedSum_to
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {functionIndex makeIndex : Nat} {store resultStore : Wasm.Store host}
    {leftLow leftHigh rightLow rightHigh result : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (highBaseNoOverflow :
      ¬ unsignedSumHighBase leftHigh rightHigh < leftHigh)
    (highCarryNoOverflow :
      ¬ unsignedSumHigh leftLow leftHigh rightLow rightHigh <
        unsignedSumCarry leftLow rightLow)
    (makeRun : Wasm.TerminatesWith env module makeIndex store
      [.i32 ((if rightLow + leftLow < leftLow then (1 : UInt32) else 0) +
          (rightHigh + leftHigh)),
        .i32 (rightLow + leftLow)]
      (fun final values =>
        final = resultStore ∧ values = [.i32 result]))
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some (naturalSumTargetFunction makeIndex rest)) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 rightHigh, .i32 rightLow, .i32 leftHigh, .i32 leftLow] ++ tail)
      (fun final values =>
        final = resultStore ∧ values = .i32 result :: tail) := by
  change ¬ rightHigh + leftHigh < leftHigh at highBaseNoOverflow
  change Not (
    ((if rightLow + leftLow < leftLow then (1 : UInt32) else 0) +
      (rightHigh + leftHigh)) <
        (if rightLow + leftLow < leftLow then (1 : UInt32) else 0)) at highCarryNoOverflow
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  unfold naturalSumTargetFunction
  simp [Wasm.Function.toLocals, Wasm.Function.numParams]
  unfold unsignedSumProgram
  simp only [List.cons_append, List.nil_append]
  wp_run
  simp [highBaseNoOverflow]
  apply Wasm.wp_iff_cons rfl
  wp_run
  simp [highCarryNoOverflow]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide), Wasm.wp_nil]
  simp only [List.take_zero, List.drop_nil, List.nil_append]
  wp_run
  apply Wasm.wp_call_tw makeRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  wp_run
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams]

/-- Canonical-result contract for the actual adapted `naturalSum` helper.
The proof performs every low/high carry step and overflow guard itself.  Its
only producer premise is the nested `makeNatural` call for the exact computed
pair; that call must return a word already related to the claimed Nat object.
Thus the outer helper cannot manufacture an arbitrary object-typed `i32`. -/
theorem terminatesWith_naturalSumRelated_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function}
    {functionIndex makeNaturalIndex : Nat}
    {store resultStore : Wasm.Store host}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {resultWitness : RefinementWitness} {resultWord : Word32}
    {resultReference : Fir.LeanIR.Impure.ObjectRef}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction = .ok targetFunction)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (highBaseNoOverflow :
      ¬ unsignedSumHighBase leftHigh rightHigh < leftHigh)
    (highCarryNoOverflow :
      ¬ unsignedSumHigh leftLow leftHigh rightLow rightHigh <
        unsignedSumCarry leftLow rightLow)
    (makeNaturalRun : Wasm.TerminatesWith env module makeNaturalIndex store
      [.i32 (unsignedSumHigh leftLow leftHigh rightLow rightHigh),
        .i32 (unsignedSumLow leftLow rightLow)]
      (fun final values =>
        final = resultStore ∧
          values = [.i32 (UInt32.ofNat resultWord.value)]))
    (resultRelated :
      ValueRel resultWitness .tobject (.word32 resultWord)
        (.object resultReference)) :
    Wasm.TerminatesWith env module functionIndex store
        ([.i32 rightHigh, .i32 rightLow, .i32 leftHigh, .i32 leftLow] ++ tail)
        (fun final values =>
          final = resultStore ∧
            values = .i32 (UInt32.ofNat resultWord.value) :: tail) ∧
      ValueRel resultWitness .tobject (.word32 resultWord)
        (.object resultReference) := by
  have targetShape :=
    naturalSumTargetFunction_of_adapted adapted makeNaturalFound
  rw [targetShape] at found
  refine ⟨terminatesWith_unsignedSum_to
    (result := UInt32.ofNat resultWord.value)
    highBaseNoOverflow highCarryNoOverflow ?_ notImport found, resultRelated⟩
  change Wasm.TerminatesWith env module makeNaturalIndex store
    [.i32 (unsignedSumHigh leftLow leftHigh rightLow rightHigh),
      .i32 (unsignedSumLow leftLow rightLow)]
    (fun final values =>
      final = resultStore ∧
        values = [.i32 (UInt32.ofNat resultWord.value)])
  exact makeNaturalRun

/-- Mathematical Nat encoded by the low/high pair passed to
`makeNatural`. -/
def naturalWordsValue (low high : UInt32) : Nat :=
  low.toNat + 2 ^ 32 * high.toNat

/-! ## Arithmetic core of the installed arbitrary-precision addition loops -/

/-- The wrapped wasm32 result of adding two words and a one-bit incoming
carry.  The spelling follows `ResidentBigNumeric.sumStep`: first add both
operand words, then add the incoming carry. -/
def wordAddWithCarry (left right carry : UInt32) : UInt32 :=
  left + right + carry

/-- The outgoing carry computed by `ResidentBigNumeric.sumStep` for one
wasm32 word.  The two tests cannot both contribute when `carry` is a bit, but
retaining their generated addition here keeps the proof tied to the installed
machine code. -/
def wordAddCarryOut (left right carry : UInt32) : UInt32 :=
  (if left + right < left then 1 else 0) +
    (if wordAddWithCarry left right carry < carry then 1 else 0)

/-- One wasm32 word addition preserves the unbounded value when its outgoing
carry is interpreted in base `2^32`.  The second conjunct is the invariant
needed to feed that carry into the high half of a limb or the next limb. -/
theorem wordAddWithCarry_spec
    (left right carry : UInt32) (carryBit : carry = 0 ∨ carry = 1) :
    (wordAddWithCarry left right carry).toNat +
          UInt32.size * (wordAddCarryOut left right carry).toNat =
        left.toNat + right.toNat + carry.toNat ∧
      (wordAddCarryOut left right carry = 0 ∨
        wordAddCarryOut left right carry = 1) := by
  have leftLt := left.toNat_lt
  have rightLt := right.toNat_lt
  have carryNat : carry.toNat = 0 ∨ carry.toNat = 1 := by
    rcases carryBit with rfl | rfl <;> simp
  unfold wordAddCarryOut wordAddWithCarry
  simp only [UInt32.size, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]
  by_cases baseFits : left.toNat + right.toNat < 2 ^ 32
  · rw [Nat.mod_eq_of_lt baseFits]
    rw [if_neg (by omega)]
    by_cases resultFits :
        left.toNat + right.toNat + carry.toNat < 2 ^ 32
    · rw [Nat.mod_eq_of_lt resultFits]
      rw [if_neg (by omega)]
      simp
    · have resultOverflow :
          2 ^ 32 ≤ left.toNat + right.toNat + carry.toNat :=
        Nat.le_of_not_gt resultFits
      have resultSubLt :
          left.toNat + right.toNat + carry.toNat - 2 ^ 32 < 2 ^ 32 := by
        omega
      rw [Nat.mod_eq_sub_mod resultOverflow,
        Nat.mod_eq_of_lt resultSubLt]
      rw [if_pos (by omega)]
      simp
      omega
  · have baseOverflow : 2 ^ 32 ≤ left.toNat + right.toNat :=
      Nat.le_of_not_gt baseFits
    have baseSubLt :
        left.toNat + right.toNat - 2 ^ 32 < 2 ^ 32 := by
      omega
    rw [Nat.mod_eq_sub_mod baseOverflow, Nat.mod_eq_of_lt baseSubLt]
    rw [if_pos (by omega)]
    have resultFits :
        left.toNat + right.toNat - 2 ^ 32 + carry.toNat < 2 ^ 32 := by
      omega
    rw [Nat.mod_eq_of_lt resultFits]
    rw [if_neg (by omega)]
    simp
    omega

/-- Low half produced by one installed 64-bit-limb addition step. -/
def limbSumLow (leftLow rightLow carry : UInt32) : UInt32 :=
  wordAddWithCarry leftLow rightLow carry

/-- Carry from the low half into the high half of the same limb. -/
def limbSumMiddleCarry (leftLow rightLow carry : UInt32) : UInt32 :=
  wordAddCarryOut leftLow rightLow carry

/-- High half produced after feeding the low-half carry into the second
wasm32 addition. -/
def limbSumHigh (leftLow leftHigh rightLow rightHigh carry : UInt32) :
    UInt32 :=
  wordAddWithCarry leftHigh rightHigh
    (limbSumMiddleCarry leftLow rightLow carry)

/-- Carry from one complete base-`2^64` limb into the next limb. -/
def limbSumCarryOut
    (leftLow leftHigh rightLow rightHigh carry : UInt32) : UInt32 :=
  wordAddCarryOut leftHigh rightHigh
    (limbSumMiddleCarry leftLow rightLow carry)

/-- The exact two-word arithmetic performed by `ResidentBigNumeric.sumStep`
is one base-`2^64` addition step.  Besides its numerical equation, the theorem
exports the bit invariant required by the following loop iteration. -/
theorem limbSum_spec
    (leftLow leftHigh rightLow rightHigh carry : UInt32)
    (carryBit : carry = 0 ∨ carry = 1) :
    naturalWordsValue
          (limbSumLow leftLow rightLow carry)
          (limbSumHigh leftLow leftHigh rightLow rightHigh carry) +
        2 ^ 64 *
          (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry).toNat =
      naturalWordsValue leftLow leftHigh +
        naturalWordsValue rightLow rightHigh + carry.toNat ∧
      (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry = 0 ∨
        limbSumCarryOut leftLow leftHigh rightLow rightHigh carry = 1) := by
  obtain ⟨lowValue, middleCarryBit⟩ :=
    wordAddWithCarry_spec leftLow rightLow carry carryBit
  obtain ⟨highValue, finalCarryBit⟩ :=
    wordAddWithCarry_spec leftHigh rightHigh
      (limbSumMiddleCarry leftLow rightLow carry) middleCarryBit
  refine ⟨?_, finalCarryBit⟩
  unfold limbSumCarryOut limbSumHigh limbSumMiddleCarry limbSumLow
  unfold naturalWordsValue
  unfold limbSumMiddleCarry at highValue
  norm_num [UInt32.size] at lowValue highValue ⊢
  omega

/-! ### One installed scan-loop arithmetic step -/

/-- Commutativity of wrapped wasm32 addition.  `UInt32` intentionally does
not expose the usual algebraic typeclass hierarchy, so instruction proofs use
this local bridge through its injective mathematical view. -/
theorem uint32_add_comm (left right : UInt32) :
    left + right = right + left := by
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_add]
  rw [Nat.add_comm]

/-- Operand order exposed by Talos after executing the emitter's two
`local.get`s.  Addition is commutative, but retaining this spelling makes the
instruction proof reduce definitionally instead of asking simplification to
normalize arithmetic inside an entire local frame. -/
def emittedWordAddWithCarry (left right carry : UInt32) : UInt32 :=
  carry + (right + left)

/-- Canonical carry spelling using the emitter's operand order. -/
def emittedWordAddCarryOut (left right carry : UInt32) : UInt32 :=
  (if right + left < left then 1 else 0) +
    (if emittedWordAddWithCarry left right carry < carry then 1 else 0)

@[simp] theorem emittedWordAddWithCarry_eq
    (left right carry : UInt32) :
    emittedWordAddWithCarry left right carry =
      wordAddWithCarry left right carry := by
  unfold emittedWordAddWithCarry wordAddWithCarry
  calc
    carry + (right + left) = (right + left) + carry :=
      uint32_add_comm _ _
    _ = (left + right) + carry := by rw [uint32_add_comm right left]

@[simp] theorem emittedWordAddCarryOut_eq
    (left right carry : UInt32) :
    emittedWordAddCarryOut left right carry =
      wordAddCarryOut left right carry := by
  unfold emittedWordAddCarryOut wordAddCarryOut
  rw [emittedWordAddWithCarry_eq, uint32_add_comm right left]

def emittedLimbSumLow (leftLow rightLow carry : UInt32) : UInt32 :=
  emittedWordAddWithCarry leftLow rightLow carry

def emittedLimbSumMiddleCarry
    (leftLow rightLow carry : UInt32) : UInt32 :=
  (if emittedWordAddWithCarry leftLow rightLow carry < carry then 1 else 0) +
    (if rightLow + leftLow < leftLow then 1 else 0)

def emittedLimbSumHigh
    (leftLow leftHigh rightLow rightHigh carry : UInt32) : UInt32 :=
  emittedWordAddWithCarry leftHigh rightHigh
    (emittedLimbSumMiddleCarry leftLow rightLow carry)

def emittedLimbSumCarryOut
    (leftLow leftHigh rightLow rightHigh carry : UInt32) : UInt32 :=
  emittedWordAddCarryOut leftHigh rightHigh
    (emittedLimbSumMiddleCarry leftLow rightLow carry)

@[simp] theorem emittedLimbSumLow_eq
    (leftLow rightLow carry : UInt32) :
    emittedLimbSumLow leftLow rightLow carry =
      limbSumLow leftLow rightLow carry := by
  simp [emittedLimbSumLow, limbSumLow]

@[simp] theorem emittedLimbSumMiddleCarry_eq
    (leftLow rightLow carry : UInt32) :
    emittedLimbSumMiddleCarry leftLow rightLow carry =
      limbSumMiddleCarry leftLow rightLow carry := by
  unfold emittedLimbSumMiddleCarry limbSumMiddleCarry wordAddCarryOut
  rw [emittedWordAddWithCarry_eq, uint32_add_comm rightLow leftLow]
  apply uint32_add_comm

@[simp] theorem emittedLimbSumHigh_eq
    (leftLow leftHigh rightLow rightHigh carry : UInt32) :
    emittedLimbSumHigh leftLow leftHigh rightLow rightHigh carry =
      limbSumHigh leftLow leftHigh rightLow rightHigh carry := by
  simp [emittedLimbSumHigh, limbSumHigh]

@[simp] theorem emittedLimbSumCarryOut_eq
    (leftLow leftHigh rightLow rightHigh carry : UInt32) :
    emittedLimbSumCarryOut leftLow leftHigh rightLow rightHigh carry =
      limbSumCarryOut leftLow leftHigh rightLow rightHigh carry := by
  simp [emittedLimbSumCarryOut, limbSumCarryOut]

/-- Talos spelling of the arithmetic suffix of `sumStep` in
`sumCarryFromFunction`.  The four magnitude accessor calls have already
placed their results in locals `7` through `10`; this suffix overwrites the
low/high result and carry scratch locals exactly as emitted by W7. -/
def sumCarryArithmeticProgram : Wasm.Program := [
  .localGet 7, .localGet 9, .add, .localSet 11,
  .localGet 11, .localGet 7, .ltU, .localSet 13,
  .localGet 11, .localGet 6, .add, .localSet 11,
  .localGet 11, .localGet 6, .ltU, .localSet 14,
  .localGet 13, .localGet 14, .add, .localSet 13,
  .localGet 8, .localGet 10, .add, .localSet 12,
  .localGet 12, .localGet 8, .ltU, .localSet 14,
  .localGet 12, .localGet 13, .add, .localSet 12,
  .localGet 12, .localGet 13, .ltU, .localSet 13,
  .localGet 13, .localGet 14, .add, .localSet 13]

/-- Explicit local frame at the arithmetic boundary of one
`sumCarryFromFunction` loop iteration.  Naming the scratch words makes the
theorem independent of zero initialization and therefore reusable after the
first iteration. -/
def sumCarryArithmeticLocals
    (left leftFlavor right rightFlavor index count carry : UInt32)
    (leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32)
    (values : List Wasm.Value) : Wasm.Locals := {
  params := [.i32 left, .i32 leftFlavor, .i32 right, .i32 rightFlavor,
    .i32 index, .i32 count, .i32 carry]
  locals := [.i32 leftLow, .i32 leftHigh, .i32 rightLow, .i32 rightHigh,
    .i32 low, .i32 high, .i32 carryLocal, .i32 carryExtra, .i32 scaled]
  values := values }

/-- Direct execution of the installed arithmetic suffix realizes the
emitter-order model definitionally.  All parameters, magnitude inputs, the
unrelated scaled-address scratch local, the store, and the operand-stack tail
are framed. -/
theorem wp_sumCarryArithmeticProgram_emitted
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor index count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (continued : Wasm.wp module rest Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor index count
        carry leftLow leftHigh rightLow rightHigh
        (emittedLimbSumLow leftLow rightLow carry)
        (emittedLimbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (emittedLimbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        scaled tail) env) :
    Wasm.wp module (sumCarryArithmeticProgram ++ rest) Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor index count
        carry leftLow leftHigh rightLow rightHigh low high carryLocal
        carryExtra scaled tail) env := by
  simp [sumCarryArithmeticProgram, sumCarryArithmeticLocals]
  exact continued

/-- Direct execution of the installed arithmetic suffix realizes the pure
base-`2^64` limb step.  The emitter-order equalities above are the only bridge
needed between stack order and the canonical arithmetic contract. -/
theorem wp_sumCarryArithmeticProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor index count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (continued : Wasm.wp module rest Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor index count
        carry leftLow leftHigh rightLow rightHigh
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        scaled tail) env) :
    Wasm.wp module (sumCarryArithmeticProgram ++ rest) Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor index count
        carry leftLow leftHigh rightLow rightHigh low high carryLocal
        carryExtra scaled tail) env := by
  apply wp_sumCarryArithmeticProgram_emitted
  simpa using continued

/-- One complete `sumStep` in the fixed local layout of
`sumCarryFromFunction`: four read-only magnitude calls followed by the proved
arithmetic suffix. -/
def sumCarryStepProgram (magnitudeLowIndex magnitudeHighIndex : Nat) :
    Wasm.Program := [
  .localGet 0, .localGet 1, .localGet 4,
  .call magnitudeLowIndex, .localSet 7,
  .localGet 0, .localGet 1, .localGet 4,
  .call magnitudeHighIndex, .localSet 8,
  .localGet 2, .localGet 3, .localGet 4,
  .call magnitudeLowIndex, .localSet 9,
  .localGet 2, .localGet 3, .localGet 4,
  .call magnitudeHighIndex, .localSet 10] ++
  sumCarryArithmeticProgram

/-- Public proof-side spelling of the emitter's private `sumStep`. -/
def sumCarryStepSource
    (left leftFlavor right rightFlavor index carryParam leftLow leftHigh
      rightLow rightHigh low high carryLocal carryExtra : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet left, .localGet leftFlavor, .localGet index,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName),
  .localSet leftLow,
  .localGet left, .localGet leftFlavor, .localGet index,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName),
  .localSet leftHigh,
  .localGet right, .localGet rightFlavor, .localGet index,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName),
  .localSet rightLow,
  .localGet right, .localGet rightFlavor, .localGet index,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName),
  .localSet rightHigh,
  .localGet leftLow, .localGet rightLow, .i32Add, .localSet low,
  .localGet low, .localGet leftLow, .i32LtU, .localSet carryLocal,
  .localGet low, .localGet carryParam, .i32Add, .localSet low,
  .localGet low, .localGet carryParam, .i32LtU, .localSet carryExtra,
  .localGet carryLocal, .localGet carryExtra, .i32Add, .localSet carryLocal,
  .localGet leftHigh, .localGet rightHigh, .i32Add, .localSet high,
  .localGet high, .localGet leftHigh, .i32LtU, .localSet carryExtra,
  .localGet high, .localGet carryLocal, .i32Add, .localSet high,
  .localGet high, .localGet carryLocal, .i32LtU, .localSet carryLocal,
  .localGet carryLocal, .localGet carryExtra, .i32Add, .localSet carryLocal]

/-- Public proof-side spelling of the installed scan guard. -/
def sumCarryGuardSource (index count carry : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet index, .localGet count, .i32Eq,
  .ifElse [.localGet carry, .ret] []]

/-- Public proof-side spelling of the installed scan back-edge. -/
def sumCarryContinueSource
    (carryLocal carry index loopLabel : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet carryLocal, .localSet carry,
  .localGet index, .i32Const .uint32 1, .i32Add, .localSet index,
  .br loopLabel]

@[simp] theorem sumCarryFrom_index_found : FirTalos.findFVar?
    (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
    Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1 =
      some 4 := by decide

@[simp] theorem sumCarryFrom_count_found : FirTalos.findFVar?
    (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
    Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[5]!.1 =
      some 5 := by decide

@[simp] theorem sumCarryFrom_carry_found : FirTalos.findFVar?
    (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
    Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1 =
      some 6 := by decide

@[simp] theorem sumCarryFrom_carryLocal_found : FirTalos.findFVar?
    (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
    Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[6]!.1 =
      some 13 := by decide

/-- The private step embedded in W7's public scan helper is exactly the
proof-side source spelling.  The loop label remains existential because it
has no data-semantic role and is private to the emitter. -/
theorem sumCarryFromFunction_step_shape :
    ∃ loopLabel,
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.body = [
        .loop loopLabel <|
          sumCarryGuardSource
              Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[5]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1 ++
          sumCarryStepSource
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[2]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[3]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[2]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[3]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[4]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[5]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[6]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[7]!.1 ++
          sumCarryContinueSource
              Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[6]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
              loopLabel] := by
  refine ⟨_, rfl⟩

/-- Successful helper lookup adapts W7's exact source step to the fixed Talos
program used by `wp_sumCarryStepProgram`. -/
theorem instructions_sumCarryStepSource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction labels
      (sumCarryStepSource
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[2]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[3]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[2]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[3]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[4]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[5]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[6]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[7]!.1) =
      .ok (sumCarryStepProgram magnitudeLowIndex magnitudeHighIndex) := by
  have leftFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[0]!.1 =
        some 0 := by decide
  have leftFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[1]!.1 =
        some 1 := by decide
  have rightFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[2]!.1 =
        some 2 := by decide
  have rightFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[3]!.1 =
        some 3 := by decide
  have indexFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1 =
        some 4 := by decide
  have carryParamFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1 =
        some 6 := by decide
  have leftLowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[0]!.1 =
        some 7 := by decide
  have leftHighFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[1]!.1 =
        some 8 := by decide
  have rightLowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[2]!.1 =
        some 9 := by decide
  have rightHighFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[3]!.1 =
        some 10 := by decide
  have lowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[4]!.1 =
        some 11 := by decide
  have highFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[5]!.1 =
        some 12 := by decide
  have carryLocalFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[6]!.1 =
        some 13 := by decide
  have carryExtraFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[7]!.1 =
        some 14 := by decide
  set_option maxRecDepth 100000 in
    simp [sumCarryStepSource, sumCarryStepProgram, sumCarryArithmeticProgram,
      FirTalos.instructions, FirTalos.instruction, leftFound, leftFlavorFound,
      rightFound, rightFlavorFound, indexFound, carryParamFound, leftLowFound,
      leftHighFound, rightLowFound, rightHighFound, lowFound, highFound,
      carryLocalFound, carryExtraFound, magnitudeLowFound, magnitudeHighFound,
      Bind.bind, Except.bind, pure, Except.pure]

/-- One installed scan-loop step implements one pure limb step whenever the
four accessor calls return the selected operand words without changing the
store.  No arithmetic fact is assumed about those words here; connecting the
accessor results to canonical padded Nat limbs is the next refinement edge. -/
theorem wp_sumCarryStepProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor index count carry : UInt32}
    {oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high carryLocal
      carryExtra scaled : UInt32}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (leftLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftLow :: tail))
    (leftHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftHigh :: tail))
    (rightLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightLow :: tail))
    (rightHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightHigh :: tail))
    (continued : Wasm.wp module rest Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor index count
        carry leftLow leftHigh rightLow rightHigh
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        scaled tail) env) :
    Wasm.wp module (sumCarryStepProgram magnitudeLowIndex magnitudeHighIndex ++
        rest) Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor index count
        carry oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled tail) env := by
  rw [sumCarryStepProgram, List.append_assoc]
  simp [sumCarryArithmeticLocals]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 index, .i32 leftFlavor, .i32 left])
      (tail := tail)
      (locals := sumCarryArithmeticLocals left leftFlavor right rightFlavor
        index count carry oldLeftLow oldLeftHigh oldRightLow oldRightHigh low
        high carryLocal carryExtra scaled (.i32 leftLow :: tail))
      (updated := sumCarryArithmeticLocals left leftFlavor right rightFlavor
        index count carry leftLow oldLeftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled (.i32 leftLow :: tail))
      (physicalResult := .i32 leftLow)
      (callRun := leftLowRun) (targetSet := by rfl)
  simp [sumCarryArithmeticLocals]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 index, .i32 leftFlavor, .i32 left])
      (tail := tail)
      (locals := sumCarryArithmeticLocals left leftFlavor right rightFlavor
        index count carry leftLow oldLeftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled (.i32 leftHigh :: tail))
      (updated := sumCarryArithmeticLocals left leftFlavor right rightFlavor
        index count carry leftLow leftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled (.i32 leftHigh :: tail))
      (physicalResult := .i32 leftHigh)
      (callRun := leftHighRun) (targetSet := by rfl)
  simp [sumCarryArithmeticLocals]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 index, .i32 rightFlavor, .i32 right])
      (tail := tail)
      (locals := sumCarryArithmeticLocals left leftFlavor right rightFlavor
        index count carry leftLow leftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled (.i32 rightLow :: tail))
      (updated := sumCarryArithmeticLocals left leftFlavor right rightFlavor
        index count carry leftLow leftHigh rightLow oldRightHigh low high
        carryLocal carryExtra scaled (.i32 rightLow :: tail))
      (physicalResult := .i32 rightLow)
      (callRun := rightLowRun) (targetSet := by rfl)
  simp [sumCarryArithmeticLocals]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 index, .i32 rightFlavor, .i32 right])
      (tail := tail)
      (locals := sumCarryArithmeticLocals left leftFlavor right rightFlavor
        index count carry leftLow leftHigh rightLow oldRightHigh low high
        carryLocal carryExtra scaled (.i32 rightHigh :: tail))
      (updated := sumCarryArithmeticLocals left leftFlavor right rightFlavor
        index count carry leftLow leftHigh rightLow rightHigh low high
        carryLocal carryExtra scaled (.i32 rightHigh :: tail))
      (physicalResult := .i32 rightHigh)
      (callRun := rightHighRun) (targetSet := by rfl)
  exact wp_sumCarryArithmeticProgram continued

/-! ### Installed carry-scan loop -/

/-- Machine spelling of the scan's next absolute limb index. -/
def sumCarryNextIndex (index : UInt32) : UInt32 :=
  1 + index

/-- Below the validated count, incrementing the wasm32 index cannot wrap. -/
theorem sumCarryNextIndex_toNat {index count : UInt32}
    (beforeCount : index.toNat < count.toNat) :
    (sumCarryNextIndex index).toNat = index.toNat + 1 := by
  have countBound : count.toNat < 2 ^ 32 := by
    simpa [UInt32.size] using count.toNat_lt
  unfold sumCarryNextIndex
  simp only [UInt32.toNat_add, UInt32.reduceToNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Loop back-edge after one arithmetic step: install the generated carry,
increment the absolute limb index, and branch to depth zero. -/
def sumCarryContinueProgram : Wasm.Program := [
  .localGet 13, .localSet 6,
  .localGet 4, .const 1, .add, .localSet 4,
  .br 0]

/-- Exact control effect of the scan back-edge. -/
theorem wp_sumCarryContinueProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor index count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high nextCarry carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value}
    (continued : Q (.Break 0 store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor
        (sumCarryNextIndex index) count nextCarry leftLow leftHigh rightLow
        rightHigh low high nextCarry carryExtra scaled tail))) :
    Wasm.wp module sumCarryContinueProgram Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor index count
        carry leftLow leftHigh rightLow rightHigh low high nextCarry carryExtra
        scaled tail) env := by
  simpa [sumCarryContinueProgram, sumCarryArithmeticLocals,
    sumCarryNextIndex] using continued

/-- Fixed Talos body of the installed carry scan. -/
def sumCarryLoopBody (magnitudeLowIndex magnitudeHighIndex : Nat) :
    Wasm.Program := [
  .localGet 4, .localGet 5, .eq,
  .iff 0 0 [.localGet 6, .ret] []] ++
  sumCarryStepProgram magnitudeLowIndex magnitudeHighIndex ++
  sumCarryContinueProgram

/-- Fixed Talos loop installed by `sumCarryFromFunction`. -/
def sumCarryLoopProgram (magnitudeLowIndex magnitudeHighIndex : Nat) :
    Wasm.Program := [
  .loop 0 0 (sumCarryLoopBody magnitudeLowIndex magnitudeHighIndex)]

/-- The symbolic guard of the installed helper adapts to the fixed numeric
local layout used by the loop proof. -/
theorem instructions_sumCarryGuardSource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction labels
      (sumCarryGuardSource
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[5]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1) =
      .ok [
        .localGet 4, .localGet 5, .eq,
        .iff 0 0 [.localGet 6, .ret] []] := by
  set_option maxRecDepth 100000 in
    simp [sumCarryGuardSource, FirTalos.instructions, FirTalos.instruction,
      sumCarryFrom_index_found, sumCarryFrom_count_found,
      sumCarryFrom_carry_found, Bind.bind, Except.bind, pure, Except.pure]

/-- The symbolic increment and back-edge adapt to the fixed numeric local and
label layout used by the loop proof. -/
theorem instructions_sumCarryContinueSource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId}
    {loopLabel : Lean.FVarId} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction
      (loopLabel :: labels)
      (sumCarryContinueSource
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[6]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
        loopLabel) = .ok sumCarryContinueProgram := by
  set_option maxRecDepth 100000 in
    simp [sumCarryContinueSource, sumCarryContinueProgram,
      FirTalos.instructions, FirTalos.instruction, FirTalos.findLabel?,
      sumCarryFrom_index_found, sumCarryFrom_carry_found,
      sumCarryFrom_carryLocal_found,
      Bind.bind, Except.bind, pure, Except.pure]

/-- Exact adaptation of the private loop body assembled from the separately
proved guard, arithmetic step, and back-edge fragments. -/
theorem instructions_sumCarryLoopBodySource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId}
    {loopLabel : Lean.FVarId} {magnitudeLowIndex magnitudeHighIndex : Nat}
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction
      (loopLabel :: labels)
      (sumCarryGuardSource
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[5]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1 ++
        sumCarryStepSource
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[1]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[2]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[3]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[1]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[2]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[3]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[4]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[5]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[6]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[7]!.1 ++
        sumCarryContinueSource
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.locals[6]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[6]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.params[4]!.1
          loopLabel) =
      .ok (sumCarryLoopBody magnitudeLowIndex magnitudeHighIndex) := by
  rw [FirTalos.Correctness.instructions_append,
    FirTalos.Correctness.instructions_append]
  rw [instructions_sumCarryGuardSource,
    instructions_sumCarryStepSource magnitudeLowFound magnitudeHighFound,
    instructions_sumCarryContinueSource]
  rfl

/-- W7's complete symbolic `sumCarryFrom` body adapts exactly to the fixed
Talos loop consumed by the semantic proof. -/
theorem instructions_sumCarryFromFunction
    {sourceModule : Fir.Wasm.Module}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction []
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction.body =
        .ok (sumCarryLoopProgram magnitudeLowIndex magnitudeHighIndex) := by
  obtain ⟨loopLabel, shape⟩ := sumCarryFromFunction_step_shape
  rw [shape]
  simp only [FirTalos.instructions, FirTalos.instruction]
  rw [instructions_sumCarryLoopBodySource magnitudeLowFound magnitudeHighFound]
  rfl

/-- Successful function adaptation installs precisely the loop consumed by
the carry-scan proof, followed by the adapter's standard terminal suffix. -/
theorem adaptedSumCarryFromFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction =
        .ok targetFunction)
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    targetFunction.body =
      sumCarryLoopProgram magnitudeLowIndex magnitudeHighIndex ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction := by
  exact adaptedFunction_body_of_exact adapted
    (instructions_sumCarryFromFunction magnitudeLowFound magnitudeHighFound)

/-- The loop guard returns the current carry without entering the accessor or
arithmetic suffix when the absolute index has reached the count. -/
theorem wp_sumCarryLoopBody_exit
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value}
    (completed : Q (.Return store (.i32 carry :: tail))) :
    Wasm.wp module
      (sumCarryLoopBody magnitudeLowIndex magnitudeHighIndex) Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor count count
        carry leftLow leftHigh rightLow rightHigh low high carryLocal
        carryExtra scaled tail) env := by
  unfold sumCarryLoopBody
  simp [sumCarryArithmeticLocals]
  apply Wasm.wp_iff_cons rfl
  simpa [sumCarryArithmeticLocals] using completed

/-- A nonterminal loop body executes one exact arithmetic step and then the
proved back-edge. -/
theorem wp_sumCarryLoopBody_continue
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor index count carry : UInt32}
    {oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high carryLocal
      carryExtra scaled : UInt32}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {tail : List Wasm.Value}
    (notDone : index ≠ count)
    (leftLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftLow :: tail))
    (leftHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftHigh :: tail))
    (rightLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightLow :: tail))
    (rightHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightHigh :: tail))
    (continued : Q (.Break 0 store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor
        (sumCarryNextIndex index) count
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        leftLow leftHigh rightLow rightHigh
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        scaled tail))) :
    Wasm.wp module
      (sumCarryLoopBody magnitudeLowIndex magnitudeHighIndex) Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor index count
        carry oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled tail) env := by
  unfold sumCarryLoopBody
  simp [sumCarryArithmeticLocals, notDone]
  apply Wasm.wp_iff_cons rfl
  simp
  apply wp_sumCarryStepProgram leftLowRun leftHighRun rightLowRun rightHighRun
  apply wp_sumCarryContinueProgram
  exact continued

/-- Machine-frame lifting of an abstract index/carry invariant.  All scratch
locals are existential because every iteration overwrites the inputs and
arithmetic destinations it consumes. -/
def sumCarryLoopInvariant
    (store : Wasm.Store host)
    (left leftFlavor right rightFlavor count : UInt32)
    (tail : List Wasm.Value) (Inv : UInt32 → UInt32 → Prop) :
    Wasm.AssertionF host :=
  fun current locals =>
    current = store ∧
      ∃ index carry leftLow leftHigh rightLow rightHigh low high carryLocal
          carryExtra scaled,
        locals = sumCarryArithmeticLocals left leftFlavor right rightFlavor
          index count carry leftLow leftHigh rightLow rightHigh low high
          carryLocal carryExtra scaled tail ∧
        Inv index carry

/-- Variant read from the scan's absolute-index parameter. -/
def sumCarryLoopMeasure (count : UInt32) :
    Wasm.Store host → Wasm.Locals → Nat :=
  fun _ locals =>
    match locals.get 4 with
    | some (.i32 index) => count.toNat - index.toNat
    | _ => 0

/-- Generic total-correctness rule for the installed carry scan.

The client supplies only an abstract invariant on the current absolute index
and carry, a bound by the fixed count, the terminal carry characterization,
and read-only accessor runs plus preservation for one nonterminal step.  The
Talos loop rule discharges termination from `count - index`; no fuel or
execution certificate enters the contract. -/
theorem wp_sumCarryLoopProgram_of_invariant
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor count initialIndex initialCarry
      expectedCarry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value} {Inv : UInt32 → UInt32 → Prop}
    {rest : Wasm.Program}
    (initialInv : Inv initialIndex initialCarry)
    (bounded : ∀ index carry, Inv index carry →
      index.toNat ≤ count.toNat)
    (atEnd : ∀ carry, Inv count carry → carry = expectedCarry)
    (step : ∀ index carry, Inv index carry →
      index.toNat < count.toNat →
      ∃ stepLeftLow stepLeftHigh stepRightLow stepRightHigh,
        Wasm.TerminatesWith env module magnitudeLowIndex store
          ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
          (fun final values =>
            final = store ∧ values = .i32 stepLeftLow :: tail) ∧
        Wasm.TerminatesWith env module magnitudeHighIndex store
          ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
          (fun final values =>
            final = store ∧ values = .i32 stepLeftHigh :: tail) ∧
        Wasm.TerminatesWith env module magnitudeLowIndex store
          ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
          (fun final values =>
            final = store ∧ values = .i32 stepRightLow :: tail) ∧
        Wasm.TerminatesWith env module magnitudeHighIndex store
          ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
          (fun final values =>
            final = store ∧ values = .i32 stepRightHigh :: tail) ∧
        Inv (sumCarryNextIndex index)
          (limbSumCarryOut stepLeftLow stepLeftHigh stepRightLow
            stepRightHigh carry))
    (completed : Q (.Return store (.i32 expectedCarry :: tail))) :
    Wasm.wp module
      (sumCarryLoopProgram magnitudeLowIndex magnitudeHighIndex ++ rest) Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor initialIndex
        count initialCarry leftLow leftHigh rightLow rightHigh low high
        carryLocal carryExtra scaled tail) env := by
  unfold sumCarryLoopProgram
  apply Wasm.wp_loop_cons
    (Inv := sumCarryLoopInvariant store left leftFlavor right rightFlavor
      count tail Inv)
    (μ := sumCarryLoopMeasure count)
  · exact ⟨rfl, initialIndex, initialCarry, leftLow, leftHigh, rightLow,
      rightHigh, low, high, carryLocal, carryExtra, scaled, rfl, initialInv⟩
  · rintro current locals
      ⟨rfl, index, carry, oldLeftLow, oldLeftHigh, oldRightLow, oldRightHigh,
        oldLow, oldHigh, oldCarryLocal, oldCarryExtra, oldScaled, rfl,
        invariant⟩
    by_cases done : index = count
    · subst index
      apply wp_sumCarryLoopBody_exit
      rw [atEnd carry invariant]
      exact completed
    · have beforeCount : index.toNat < count.toNat := by
        have indexBound := bounded index carry invariant
        have differentNat : index.toNat ≠ count.toNat := by
          intro same
          exact done (UInt32.toNat.inj same)
        omega
      obtain ⟨stepLeftLow, stepLeftHigh, stepRightLow, stepRightHigh,
        leftLowRun, leftHighRun, rightLowRun, rightHighRun, nextInvariant⟩ :=
        step index carry invariant beforeCount
      apply wp_sumCarryLoopBody_continue done leftLowRun leftHighRun
        rightLowRun rightHighRun
      refine ⟨?_, ?_⟩
      · exact ⟨rfl, sumCarryNextIndex index,
          limbSumCarryOut stepLeftLow stepLeftHigh stepRightLow stepRightHigh
            carry,
          stepLeftLow, stepLeftHigh, stepRightLow, stepRightHigh,
          limbSumLow stepLeftLow stepRightLow carry,
          limbSumHigh stepLeftLow stepLeftHigh stepRightLow stepRightHigh carry,
          limbSumCarryOut stepLeftLow stepLeftHigh stepRightLow stepRightHigh
            carry,
          (if stepRightHigh + stepLeftHigh < stepLeftHigh then 1 else 0),
          oldScaled, rfl, nextInvariant⟩
      · simp [sumCarryLoopMeasure, sumCarryArithmeticLocals,
          sumCarryNextIndex_toNat beforeCount]
        omega

/-- The two wasm32 halves of one little-endian base-`2^64` limb. -/
abbrev LimbWords := UInt32 × UInt32

def limbWordsValue (limb : LimbWords) : Nat :=
  naturalWordsValue limb.1 limb.2

/-- Unbounded value of a least-significant-limb-first word list. -/
def limbWordsListValue : List LimbWords → Nat
  | [] => 0
  | limb :: limbs => limbWordsValue limb + 2 ^ 64 * limbWordsListValue limbs

/-- Split the concrete runtime's `UInt64` limb into the low/high wasm32 words
observed by the resident magnitude accessors. -/
def limbWordsOfUInt64 (limb : UInt64) : LimbWords :=
  (limb.toUInt32, (limb >>> (32 : UInt64)).toUInt32)

/-- Reassemble the resident low/high word pair as one concrete-runtime limb. -/
def limbUInt64OfWords (limb : LimbWords) : UInt64 :=
  limb.1.toUInt64 + limb.2.toUInt64 * 4294967296

theorem limbWordsValue_ofUInt64 (limb : UInt64) :
    limbWordsValue (limbWordsOfUInt64 limb) = limb.toNat := by
  have limbLt : limb.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using limb.toNat_lt
  have highLt : limb.toNat / 2 ^ 32 < 2 ^ 32 := by
    omega
  unfold limbWordsValue limbWordsOfUInt64 naturalWordsValue
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  have shift32 : (32 : UInt64).toNat % 64 = 32 := by decide
  rw [shift32, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt highLt]
  exact Nat.mod_add_div limb.toNat (2 ^ 32)

@[simp] theorem limbWordsOfUInt64_limbUInt64OfWords (limb : LimbWords) :
    limbWordsOfUInt64 (limbUInt64OfWords limb) = limb := by
  rcases limb with ⟨low, high⟩
  apply Prod.ext
  · change (low.toUInt64 + high.toUInt64 * 4294967296).toUInt32 = low
    bv_decide
  · change
      ((low.toUInt64 + high.toUInt64 * 4294967296) >>>
        (32 : UInt64)).toUInt32 = high
    bv_decide

@[simp] theorem limbUInt64OfWords_toNat (limb : LimbWords) :
    (limbUInt64OfWords limb).toNat = limbWordsValue limb := by
  calc
    _ = limbWordsValue
          (limbWordsOfUInt64 (limbUInt64OfWords limb)) :=
      (limbWordsValue_ofUInt64 (limbUInt64OfWords limb)).symm
    _ = limbWordsValue limb := by simp

/-- Reassembling every word pair preserves the complete little-endian
unbounded list value. -/
theorem naturalLimbsValue_map_limbUInt64OfWords (limbs : List LimbWords) :
    naturalLimbsValue (limbs.map limbUInt64OfWords) =
      limbWordsListValue limbs := by
  induction limbs with
  | nil => rfl
  | cons limb limbs inductionHypothesis =>
      simp [naturalLimbsValue, limbWordsListValue, inductionHypothesis,
        UInt64.size]

/-- The W6 word-pair view and the concrete runtime's `UInt64`-limb view have
the same little-endian unbounded value. -/
theorem limbWordsListValue_ofUInt64s (limbs : List UInt64) :
    limbWordsListValue (limbs.map limbWordsOfUInt64) =
      naturalLimbsValue limbs := by
  induction limbs with
  | nil => rfl
  | cons limb limbs inductionHypothesis =>
      simp [limbWordsListValue, naturalLimbsValue,
        limbWordsValue_ofUInt64, inductionHypothesis, UInt64.size]

@[simp] theorem limbWordsListValue_replicate_zero (count : Nat) :
    limbWordsListValue (List.replicate count ((0, 0) : LimbWords)) = 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp [List.replicate_succ, limbWordsListValue, limbWordsValue,
        naturalWordsValue, inductionHypothesis]

theorem limbWordsListValue_append_zeros
    (limbs : List LimbWords) (count : Nat) :
    limbWordsListValue
        (limbs ++ List.replicate count ((0, 0) : LimbWords)) =
      limbWordsListValue limbs := by
  induction limbs with
  | nil => simp [limbWordsListValue]
  | cons limb limbs inductionHypothesis =>
      simp [limbWordsListValue, inductionHypothesis]

/-- Little-endian list concatenation shifts the appended high limbs by the
complete width of the low prefix. -/
theorem limbWordsListValue_append (low high : List LimbWords) :
    limbWordsListValue (low ++ high) =
      limbWordsListValue low +
        2 ^ (64 * low.length) * limbWordsListValue high := by
  induction low with
  | nil => simp [limbWordsListValue]
  | cons limb low inductionHypothesis =>
      simp only [List.cons_append, limbWordsListValue, List.length_cons,
        inductionHypothesis]
      rw [Nat.mul_succ, Nat.pow_add]
      norm_num
      ring

/-- Pad a least-significant-first limb view to a shared loop count.  This is
the pure counterpart of `magnitudeLow`/`magnitudeHigh` returning zero beyond
an operand's own count. -/
def padLimbWords (count : Nat) (limbs : List LimbWords) : List LimbWords :=
  limbs ++ List.replicate (count - limbs.length) (0, 0)

theorem padLimbWords_length {count : Nat} {limbs : List LimbWords}
    (fits : limbs.length ≤ count) :
    (padLimbWords count limbs).length = count := by
  simp [padLimbWords, Nat.add_sub_of_le fits]

theorem padLimbWords_value (count : Nat) (limbs : List LimbWords) :
    limbWordsListValue (padLimbWords count limbs) =
      limbWordsListValue limbs := by
  exact limbWordsListValue_append_zeros limbs (count - limbs.length)

/-- Canonical concrete Natural limbs, split into the wasm32 words seen by the
installed addition loops and padded to their common maximum count. -/
def paddedNaturalLimbWords (count value : Nat) : List LimbWords :=
  padLimbWords count ((naturalLimbs value).map limbWordsOfUInt64)

theorem paddedNaturalLimbWords_length {count value : Nat}
    (fits : (naturalLimbs value).length ≤ count) :
    (paddedNaturalLimbWords count value).length = count := by
  apply padLimbWords_length
  simpa using fits

theorem paddedNaturalLimbWords_value (count value : Nat) :
    limbWordsListValue (paddedNaturalLimbWords count value) = value := by
  rw [paddedNaturalLimbWords, padLimbWords_value,
    limbWordsListValue_ofUInt64s, naturalLimbs_value]

/-- Pure recursion matching the carry flow of both installed addition loops.
The mismatched-list cases are unreachable once validation has padded both
operand views to the common maximum count. -/
def addLimbWords : List LimbWords → List LimbWords → UInt32 →
    List LimbWords × UInt32
  | [], [], carry => ([], carry)
  | left :: lefts, right :: rights, carry =>
      let low := limbSumLow left.1 right.1 carry
      let high := limbSumHigh left.1 left.2 right.1 right.2 carry
      let nextCarry :=
        limbSumCarryOut left.1 left.2 right.1 right.2 carry
      let rest := addLimbWords lefts rights nextCarry
      ((low, high) :: rest.1, rest.2)
  | _, _, carry => ([], carry)

/-- Equal-length inputs produce exactly one output limb per input limb. -/
theorem addLimbWords_length
    (left right : List LimbWords) (carry : UInt32)
    (sameLength : left.length = right.length) :
    (addLimbWords left right carry).1.length = left.length := by
  induction left generalizing right carry with
  | nil =>
      cases right with
      | nil => rfl
      | cons right rights => simp at sameLength
  | cons left lefts inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons right rights =>
          have restSameLength : lefts.length = rights.length := by
            simpa using sameLength
          simp [addLimbWords,
            inductionHypothesis rights
              (limbSumCarryOut left.1 left.2 right.1 right.2 carry)
              restSameLength]

/-- Processed-prefix invariant for the shared scan/writer arithmetic.  The
output prefix plus its final carry has exactly the value of both equally sized
input prefixes plus the incoming bit. -/
theorem addLimbWords_spec
    (left right : List LimbWords) (carry : UInt32)
    (sameLength : left.length = right.length)
    (carryBit : carry = 0 ∨ carry = 1) :
    limbWordsListValue (addLimbWords left right carry).1 +
          2 ^ (64 * left.length) *
            (addLimbWords left right carry).2.toNat =
        limbWordsListValue left + limbWordsListValue right + carry.toNat ∧
      ((addLimbWords left right carry).2 = 0 ∨
        (addLimbWords left right carry).2 = 1) := by
  induction left generalizing right carry with
  | nil =>
      cases right with
      | nil => simp [addLimbWords, limbWordsListValue, carryBit]
      | cons right rights => simp at sameLength
  | cons left lefts inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons right rights =>
          have restSameLength : lefts.length = rights.length := by
            simpa using sameLength
          obtain ⟨stepValue, nextCarryBit⟩ :=
            limbSum_spec left.1 left.2 right.1 right.2 carry carryBit
          obtain ⟨restValue, finalCarryBit⟩ :=
            inductionHypothesis rights
              (limbSumCarryOut left.1 left.2 right.1 right.2 carry)
              restSameLength nextCarryBit
          refine ⟨?_, finalCarryBit⟩
          simp only [addLimbWords, limbWordsListValue, limbWordsValue,
            List.length_cons]
          calc
            _ = naturalWordsValue
                  (limbSumLow left.1 right.1 carry)
                  (limbSumHigh left.1 left.2 right.1 right.2 carry) +
                2 ^ 64 *
                  (limbWordsListValue
                      (addLimbWords lefts rights
                        (limbSumCarryOut left.1 left.2 right.1 right.2
                          carry)).1 +
                    2 ^ (64 * lefts.length) *
                      (addLimbWords lefts rights
                        (limbSumCarryOut left.1 left.2 right.1 right.2
                          carry)).2.toNat) := by
                    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_add]
                    ac_rfl
            _ = naturalWordsValue
                  (limbSumLow left.1 right.1 carry)
                  (limbSumHigh left.1 left.2 right.1 right.2 carry) +
                2 ^ 64 *
                  (limbWordsListValue lefts + limbWordsListValue rights +
                    (limbSumCarryOut left.1 left.2 right.1 right.2
                      carry).toNat) := by rw [restValue]
            _ = (naturalWordsValue left.1 left.2 +
                    2 ^ 64 * limbWordsListValue lefts) +
                  (naturalWordsValue right.1 right.2 +
                    2 ^ 64 * limbWordsListValue rights) + carry.toNat := by
                    simp only [Nat.mul_add]
                    norm_num at stepValue ⊢
                    omega

/-- Final payload list produced by the installed writer and its conditional
carry-limb stores. -/
def completedAddLimbWords (words : List LimbWords) (carry : UInt32) :
    List LimbWords :=
  if carry = 0 then words else words ++ [(1, 0)]

theorem completedAddLimbWords_length
    (words : List LimbWords) (carry : UInt32)
    (carryBit : carry = 0 ∨ carry = 1) :
    (completedAddLimbWords words carry).length =
      words.length + carry.toNat := by
  rcases carryBit with rfl | rfl <;>
    simp [completedAddLimbWords]

theorem completedAddLimbWords_value
    (words : List LimbWords) (carry : UInt32)
    (carryBit : carry = 0 ∨ carry = 1) :
    limbWordsListValue (completedAddLimbWords words carry) =
      limbWordsListValue words +
        2 ^ (64 * words.length) * carry.toNat := by
  rcases carryBit with rfl | rfl
  · simp [completedAddLimbWords]
  · rw [completedAddLimbWords, if_neg (by decide),
      limbWordsListValue_append]
    simp [limbWordsListValue, limbWordsValue, naturalWordsValue]

/-- Appending the writer's optional carry limb turns the arithmetic invariant
into the exact unbounded value and physical result count. -/
theorem completedAddLimbWords_spec
    (left right : List LimbWords) (carry : UInt32)
    (sameLength : left.length = right.length)
    (carryBit : carry = 0 ∨ carry = 1) :
    let result := addLimbWords left right carry
    limbWordsListValue (completedAddLimbWords result.1 result.2) =
        limbWordsListValue left + limbWordsListValue right + carry.toNat ∧
      (completedAddLimbWords result.1 result.2).length =
        left.length + result.2.toNat := by
  dsimp only
  obtain ⟨value, finalCarryBit⟩ :=
    addLimbWords_spec left right carry sameLength carryBit
  have outputLength := addLimbWords_length left right carry sameLength
  constructor
  · rw [completedAddLimbWords_value _ _ finalCarryBit, outputLength]
    exact value
  · rw [completedAddLimbWords_length _ _ finalCarryBit,
      outputLength]

/-- End-to-end pure contract that the installed scan and writer loops must
realize.  With canonical operands padded to the validated maximum count, the
computed prefix and final carry denote the mathematical Nat sum. -/
theorem addPaddedNaturalLimbWords_spec
    {count left right : Nat}
    (leftFits : (naturalLimbs left).length ≤ count)
    (rightFits : (naturalLimbs right).length ≤ count) :
    limbWordsListValue
          (addLimbWords (paddedNaturalLimbWords count left)
            (paddedNaturalLimbWords count right) 0).1 +
        2 ^ (64 * count) *
          (addLimbWords (paddedNaturalLimbWords count left)
            (paddedNaturalLimbWords count right) 0).2.toNat =
      left + right ∧
    ((addLimbWords (paddedNaturalLimbWords count left)
          (paddedNaturalLimbWords count right) 0).2 = 0 ∨
      (addLimbWords (paddedNaturalLimbWords count left)
          (paddedNaturalLimbWords count right) 0).2 = 1) := by
  have leftLength := paddedNaturalLimbWords_length leftFits
  have rightLength := paddedNaturalLimbWords_length rightFits
  have sameLength :
      (paddedNaturalLimbWords count left).length =
        (paddedNaturalLimbWords count right).length := by
    rw [leftLength, rightLength]
  have specification := addLimbWords_spec
    (paddedNaturalLimbWords count left)
    (paddedNaturalLimbWords count right) 0 sameLength (Or.inl rfl)
  rw [leftLength, paddedNaturalLimbWords_value,
    paddedNaturalLimbWords_value] at specification
  simpa using specification

/-- The complete physical payload, including a possible final carry limb,
decodes exactly to the mathematical sum and has the allocator's result count. -/
theorem completedAddPaddedNaturalLimbWords_spec
    {count left right : Nat}
    (leftFits : (naturalLimbs left).length ≤ count)
    (rightFits : (naturalLimbs right).length ≤ count) :
    let result := addLimbWords (paddedNaturalLimbWords count left)
      (paddedNaturalLimbWords count right) 0
    limbWordsListValue (completedAddLimbWords result.1 result.2) =
        left + right ∧
      (completedAddLimbWords result.1 result.2).length =
        count + result.2.toNat := by
  dsimp only
  obtain ⟨sumValue, carryBit⟩ :=
    addPaddedNaturalLimbWords_spec leftFits rightFits
  have leftLength := paddedNaturalLimbWords_length leftFits
  have rightLength := paddedNaturalLimbWords_length rightFits
  have sameLength :
      (paddedNaturalLimbWords count left).length =
        (paddedNaturalLimbWords count right).length := by
    rw [leftLength, rightLength]
  have outputLength := addLimbWords_length
    (paddedNaturalLimbWords count left)
    (paddedNaturalLimbWords count right) 0 sameLength
  constructor
  · rw [completedAddLimbWords_value _ _ carryBit, outputLength,
      leftLength]
    exact sumValue
  · rw [completedAddLimbWords_length _ _ carryBit, outputLength,
      leftLength]

/-- Complete installed carry-scan theorem over equally sized machine limb
views.  The helper starts at absolute index zero and returns exactly the final
carry of `addLimbWords`; accessor calls are tied pointwise to the corresponding
low/high word pair. -/
theorem wp_sumCarryLoopProgram_of_limbWords
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor count initialCarry : UInt32}
    {initialLeftLow initialLeftHigh initialRightLow initialRightHigh low high
      carryLocal carryExtra scaled : UInt32}
    {tail : List Wasm.Value} {leftWords rightWords : List LimbWords}
    {rest : Wasm.Program}
    (leftLength : leftWords.length = count.toNat)
    (rightLength : rightWords.length = count.toNat)
    (leftLowRun : ∀ (index : UInt32)
      (beforeCount : index.toNat < count.toNat),
      Wasm.TerminatesWith env module magnitudeLowIndex store
        ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (leftWords[index.toNat]'(by omega)).1 :: tail))
    (leftHighRun : ∀ (index : UInt32)
      (beforeCount : index.toNat < count.toNat),
      Wasm.TerminatesWith env module magnitudeHighIndex store
        ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (leftWords[index.toNat]'(by omega)).2 :: tail))
    (rightLowRun : ∀ (index : UInt32)
      (beforeCount : index.toNat < count.toNat),
      Wasm.TerminatesWith env module magnitudeLowIndex store
        ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (rightWords[index.toNat]'(by omega)).1 :: tail))
    (rightHighRun : ∀ (index : UInt32)
      (beforeCount : index.toNat < count.toNat),
      Wasm.TerminatesWith env module magnitudeHighIndex store
        ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (rightWords[index.toNat]'(by omega)).2 :: tail))
    (completed : Q (.Return store
      (.i32 (addLimbWords leftWords rightWords initialCarry).2 :: tail))) :
    Wasm.wp module
      (sumCarryLoopProgram magnitudeLowIndex magnitudeHighIndex ++ rest) Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor 0 count
        initialCarry initialLeftLow initialLeftHigh initialRightLow
        initialRightHigh low high carryLocal carryExtra scaled tail) env := by
  let expectedCarry := (addLimbWords leftWords rightWords initialCarry).2
  let Inv : UInt32 → UInt32 → Prop := fun index carry =>
    index.toNat ≤ count.toNat ∧
      (addLimbWords (leftWords.drop index.toNat)
        (rightWords.drop index.toNat) carry).2 = expectedCarry
  apply wp_sumCarryLoopProgram_of_invariant
    (Inv := Inv) (expectedCarry := expectedCarry)
  · constructor
    · simp
    · simp [expectedCarry]
  · intro index carry invariant
    exact invariant.1
  · intro carry invariant
    have leftDrop : leftWords.drop count.toNat = [] := by
      rw [← leftLength]
      simp
    have rightDrop : rightWords.drop count.toNat = [] := by
      rw [← rightLength]
      simp
    simpa [Inv, leftDrop, rightDrop, addLimbWords] using invariant.2
  · intro index carry invariant beforeCount
    let leftLimb : LimbWords := leftWords[index.toNat]'(by omega)
    let rightLimb : LimbWords := rightWords[index.toNat]'(by omega)
    refine ⟨leftLimb.1, leftLimb.2, rightLimb.1, rightLimb.2,
      leftLowRun index beforeCount, leftHighRun index beforeCount,
      rightLowRun index beforeCount, rightHighRun index beforeCount, ?_⟩
    constructor
    · rw [sumCarryNextIndex_toNat beforeCount]
      omega
    · have leftDrop := List.drop_eq_getElem_cons
          (l := leftWords) (i := index.toNat) (by omega)
      have rightDrop := List.drop_eq_getElem_cons
          (l := rightWords) (i := index.toNat) (by omega)
      have carryResult := invariant.2
      rw [leftDrop, rightDrop] at carryResult
      simp only [addLimbWords] at carryResult
      rw [sumCarryNextIndex_toNat beforeCount]
      simpa [Inv, leftLimb, rightLimb] using carryResult
  · simpa [expectedCarry] using completed

/-- Correctness of the body actually installed for W7's `sumCarryFrom`
helper.  Successful source-to-Talos adaptation and pointwise correctness of
the two magnitude accessors imply that the physical function body terminates
with exactly the pure `addLimbWords` carry; the adapter terminal is admitted
only as an unreachable suffix after the loop's explicit return. -/
theorem wp_adaptedSumCarryFromFunction_of_limbWords
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor count initialCarry : UInt32}
    {initialLeftLow initialLeftHigh initialRightLow initialRightHigh low high
      carryLocal carryExtra scaled : UInt32}
    {tail : List Wasm.Value} {leftWords rightWords : List LimbWords}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromFunction =
        .ok targetFunction)
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex)
    (leftLength : leftWords.length = count.toNat)
    (rightLength : rightWords.length = count.toNat)
    (leftLowRun : ∀ (index : UInt32)
      (beforeCount : index.toNat < count.toNat),
      Wasm.TerminatesWith env module magnitudeLowIndex store
        ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (leftWords[index.toNat]'(by omega)).1 :: tail))
    (leftHighRun : ∀ (index : UInt32)
      (beforeCount : index.toNat < count.toNat),
      Wasm.TerminatesWith env module magnitudeHighIndex store
        ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (leftWords[index.toNat]'(by omega)).2 :: tail))
    (rightLowRun : ∀ (index : UInt32)
      (beforeCount : index.toNat < count.toNat),
      Wasm.TerminatesWith env module magnitudeLowIndex store
        ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (rightWords[index.toNat]'(by omega)).1 :: tail))
    (rightHighRun : ∀ (index : UInt32)
      (beforeCount : index.toNat < count.toNat),
      Wasm.TerminatesWith env module magnitudeHighIndex store
        ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (rightWords[index.toNat]'(by omega)).2 :: tail))
    (completed : Q (.Return store
      (.i32 (addLimbWords leftWords rightWords initialCarry).2 :: tail))) :
    Wasm.wp module targetFunction.body Q store
      (sumCarryArithmeticLocals left leftFlavor right rightFlavor 0 count
        initialCarry initialLeftLow initialLeftHigh initialRightLow
        initialRightHigh low high carryLocal carryExtra scaled tail) env := by
  rw [adaptedSumCarryFromFunction_body adapted magnitudeLowFound
    magnitudeHighFound]
  exact wp_sumCarryLoopProgram_of_limbWords leftLength rightLength leftLowRun
    leftHighRun rightLowRun rightHighRun completed

/-- Every semantic Nat literal returns an object reference, independently of
whether its canonical concrete representation is immediate, promoted, or an
ordinary limb object. -/
theorem literal_nat_objectReference
    (runtime : Fir.LeanIR.Impure.RuntimeState) (value : Nat) :
    ∃ reference,
      (Fir.LeanIR.Impure.literal runtime (.nat value)).2 =
        .object reference := by
  by_cases small : value ≤ Fir.LeanIR.Impure.maxTaggedPayload <;>
    simp [Fir.LeanIR.Impure.literal, small]

/-- Representation-polymorphic checked one-limb `naturalSum` refinement.

The resident `makeNatural` call is tied to W6's concrete allocator by the
same input word pair and returned address.  The existing allocator theorem
then constructs the extended witness and canonical Nat relation for all three
representations.  The adapted `naturalSum` body proves the arithmetic and
threads the exact successor store; no independent result-typing premise is
accepted. -/
theorem terminatesWith_naturalSum_of_concreteAllocation
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function}
    {functionIndex makeNaturalIndex : Nat}
    {store resultStore : Wasm.Store host}
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {value : Nat} {address : Word32} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction = .ok targetFunction)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (highBaseNoOverflow :
      ¬ unsignedSumHighBase leftHigh rightHigh < leftHigh)
    (highCarryNoOverflow :
      ¬ unsignedSumHigh leftLow leftHigh rightLow rightHigh <
        unsignedSumCarry leftLow rightLow)
    (valueEq : value = naturalWordsValue
      (unsignedSumLow leftLow rightLow)
      (unsignedSumHigh leftLow leftHigh rightLow rightHigh))
    (heapRelated : LiveHeapRel before witness runtime)
    (beforeMemoryRelated : ResidentMemoryRel before store.mem)
    (allocated : allocateNatural before value = .ok (after, address))
    (afterMemoryRelated : ResidentMemoryRel after resultStore.mem)
    (hostUnchanged : resultStore.host = store.host)
    (makeNaturalRun : Wasm.TerminatesWith env module makeNaturalIndex store
      [.i32 (unsignedSumHigh leftLow leftHigh rightLow rightHigh),
        .i32 (unsignedSumLow leftLow rightLow)]
      (fun final values =>
        final = resultStore ∧
          values = [.i32 (UInt32.ofNat address.value)])) :
    ∃ nextWitness reference,
      witness.Extends nextWitness ∧
        ClosureAllocationsPersistent witness nextWitness ∧
        LiveHeapRel after nextWitness
          (Fir.LeanIR.Impure.literal runtime (.nat value)).1 ∧
        ResidentMemoryRel before store.mem ∧
        ResidentMemoryRel after resultStore.mem ∧
        resultStore.host = store.host ∧
        value = naturalWordsValue
          (unsignedSumLow leftLow rightLow)
          (unsignedSumHigh leftLow leftHigh rightLow rightHigh) ∧
        Wasm.TerminatesWith env module functionIndex store
          ([.i32 rightHigh, .i32 rightLow, .i32 leftHigh, .i32 leftLow] ++
            tail)
          (fun final values =>
            final = resultStore ∧
              values = .i32 (UInt32.ofNat address.value) :: tail) ∧
        ValueRel nextWitness .tobject (.word32 address)
          (.object reference) ∧
        (Fir.LeanIR.Impure.literal runtime (.nat value)).2 =
          .object reference := by
  obtain ⟨nextWitness, extension, closureAllocationsPersistent,
      nextHeapRelated, valueRelated⟩ :=
    allocateNatural_liveHeapRel_extends before after witness runtime value
      address heapRelated allocated
  obtain ⟨reference, referenceEq⟩ :=
    literal_nat_objectReference runtime value
  rw [referenceEq] at valueRelated
  obtain ⟨naturalSumRun, resultRelated⟩ :=
    terminatesWith_naturalSumRelated_of_adapted
      (tail := tail) adapted makeNaturalFound notImport found
      highBaseNoOverflow highCarryNoOverflow makeNaturalRun valueRelated
  exact ⟨nextWitness, reference, extension, closureAllocationsPersistent,
    nextHeapRelated, beforeMemoryRelated, afterMemoryRelated, hostUnchanged,
    valueEq, naturalSumRun, resultRelated, referenceEq⟩

/-- Converting a Nat addition to wasm32 is exact modulo the machine word, in
the operand order used by the resident sum primitive. -/
theorem uint32_ofNat_add_comm (left right : Nat) :
    UInt32.ofNat right + UInt32.ofNat left =
      UInt32.ofNat (left + right) := by
  calc
    _ = UInt32.ofNat (right + left) := (UInt32.ofNat_add right left).symm
    _ = UInt32.ofNat (left + right) := by rw [Nat.add_comm]

/-- A bounded immediate-Nat sum cannot set the carry word. -/
theorem uint32_ofNat_add_noCarry_of_immediate_sum
    {left right : Nat} (fits : left + right ≤ maxImmediatePayload) :
    ¬ UInt32.ofNat right + UInt32.ofNat left < UInt32.ofNat left := by
  have sumLt : left + right < UInt32.size := by
    unfold maxImmediatePayload at fits
    simp [UInt32.size]
    omega
  have leftLt : left < UInt32.size := by omega
  rw [uint32_ofNat_add_comm left right, UInt32.lt_iff_toNat_lt,
    UInt32.toNat_ofNat_of_lt' sumLt,
    UInt32.toNat_ofNat_of_lt' leftLt]
  omega

/-- The actual adapted natural-sum helper returns the canonical tagged result
when the mathematical sum remains immediate.  Both the sum helper and its
constructor callee are obtained from successful FIR-to-Talos adaptation; no
hand-written target body is assumed by the theorem. -/
theorem terminatesWith_naturalSumImmediate_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {targetFunction targetMakeNatural : Wasm.Function}
    {functionIndex makeNaturalIndex : Nat} {store : Wasm.Store host}
    {left right : Nat} {tail : List Wasm.Value}
    (sumFits : left + right ≤ maxImmediatePayload)
    (naturalAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction = .ok targetFunction)
    (makeFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (makeNaturalAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction =
        .ok targetMakeNatural)
    (naturalNotImport : module.imports[functionIndex]? = none)
    (naturalTargetFound :
      module.funcs[functionIndex - module.imports.length]? =
        some targetFunction)
    (makeNaturalNotImport : module.imports[makeNaturalIndex]? = none)
    (makeNaturalTargetFound :
      module.funcs[makeNaturalIndex - module.imports.length]? =
        some targetMakeNatural) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 0, .i32 (UInt32.ofNat right),
        .i32 0, .i32 (UInt32.ofNat left)] ++ tail)
      (fun final values =>
        final = store ∧
          values =
            .i32 (UInt32.ofNat
              (Word32.encodeImmediate (left + right) sumFits).value) ::
              tail) := by
  have sumEq := uint32_ofNat_add_comm left right
  have noCarry := uint32_ofNat_add_noCarry_of_immediate_sum sumFits
  have targetShape :=
    naturalSumTargetFunction_of_adapted naturalAdapted makeFound
  rw [targetShape] at naturalTargetFound
  have constructorRun :=
    terminatesWith_makeNaturalImmediate_of_adapted
      (module := module) (env := env) (store := store)
      (functionIndex := makeNaturalIndex) (payload := left + right) (tail := [])
      makeNaturalAdapted sumFits makeNaturalNotImport makeNaturalTargetFound
  have makeRun : Wasm.TerminatesWith env module makeNaturalIndex store
      [.i32 ((if UInt32.ofNat right + UInt32.ofNat left < UInt32.ofNat left
          then (1 : UInt32) else 0) + (0 + 0)),
        .i32 (UInt32.ofNat right + UInt32.ofNat left)]
      (fun final values =>
        final = store ∧
          values = [.i32 (UInt32.ofNat
            (Word32.encodeImmediate (left + right) sumFits).value)]) := by
    rw [if_neg noCarry, sumEq]
    simpa using constructorRun
  exact terminatesWith_unsignedSum
    (leftLow := UInt32.ofNat left) (leftHigh := 0)
    (rightLow := UInt32.ofNat right) (rightHigh := 0)
    (result := UInt32.ofNat
      (Word32.encodeImmediate (left + right) sumFits).value)
    (tail := tail)
    (by simp [unsignedSumHighBase])
    (by simp [unsignedSumHigh, unsignedSumCarry, unsignedSumHighBase])
    makeRun naturalNotImport naturalTargetFound

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

/-- Exact Talos form of the public `Nat.add` two-immediate arm.  The shared
payload decoder feeds zero high words to `naturalSum`, whose already-valid
object result crosses the typed, scratch-free word round trip. -/
def immediateAddProgram (naturalSumIndex : Nat) : Wasm.Program :=
  ResidentPrimitives.immediateNaturalPayload 0 ++ [.const 0] ++
    ResidentPrimitives.immediateNaturalPayload 1 ++ [
      .const 0,
      .call naturalSumIndex] ++
    ResidentPrimitives.unsignedI32RoundTrip ++ [.ret]

/-- Symbolic source spelling of `immediateAddProgram`; the public function's
parameter identifiers are supplied positionally by the shape theorem. -/
def immediateAddSource (left right : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload left ++ [
      .i32Const .uint32 0] ++
    Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload right ++ [
      .i32Const .uint32 0,
      .call (.declaration
        Fir.Wasm.Emit.ResidentNumeric.naturalSumName)] ++
    ResidentPrimitives.typedObjectWordRoundTripSource ++ [.ret]

/-- Shared source suffix for a physical word whose producer has already
established the concrete object relation.  Unlike the historical scratch
cast, this suffix contains no memory instruction and carries no local-index
obligation. -/
def typedNaturalReturnSource : List Fir.Wasm.Instruction :=
  ResidentPrimitives.typedObjectWordRoundTripSource ++ [.ret]

/-- Exact Talos adaptation of `typedNaturalReturnSource`. -/
def typedNaturalReturnProgram : Wasm.Program :=
  ResidentPrimitives.unsignedI32RoundTrip ++ [.ret]

/-- Adapting the checked natural-result suffix preserves the two scalar word
operations and the explicit return. -/
theorem instructions_typedNaturalReturnSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} :
    FirTalos.instructions sourceModule sourceFunction labels
      typedNaturalReturnSource = .ok typedNaturalReturnProgram := by
  simp [typedNaturalReturnSource, typedNaturalReturnProgram,
    ResidentPrimitives.typedObjectWordRoundTripSource,
    ResidentPrimitives.unsignedI32RoundTrip, FirTalos.instructions,
    FirTalos.instruction, Bind.bind, Except.bind, pure, Except.pure]

/-- Operation-specific postcondition for returning a canonical concrete Nat
word.  The scalar round trip may preserve any physical word, but this post is
inhabited only when the producer supplies the corresponding `ValueRel`. -/
def TypedNaturalReturnPost (witness : RefinementWitness) (word : Word32)
    (reference : Fir.LeanIR.Impure.ObjectRef) (store : Wasm.Store host)
    (tail : List Wasm.Value) : Wasm.Assertion host :=
  fun continuation =>
    continuation =
        .Return store (.i32 (UInt32.ofNat word.value) :: tail) ∧
      ValueRel witness .tobject (.word32 word) (.object reference)

/-- A related Nat word crosses the typed, scratch-free return suffix with its
exact bits, store, memory, and caller stack tail unchanged.  This theorem is
the admissible boundary for checked result producers: an arbitrary `i32`
cannot satisfy its conclusion. -/
theorem wp_typedNaturalReturnProgram
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {witness : RefinementWitness} {word : Word32}
    {reference : Fir.LeanIR.Impure.ObjectRef} {tail : List Wasm.Value}
    (related :
      ValueRel witness .tobject (.word32 word) (.object reference)) :
    Wasm.wp module typedNaturalReturnProgram
      (TypedNaturalReturnPost witness word reference store tail) store
      { locals with values :=
          (Wasm.Value.i32 (UInt32.ofNat word.value) :: tail) } env := by
  unfold typedNaturalReturnProgram
  apply ResidentPrimitives.wp_unsignedI32RoundTrip
  simp [TypedNaturalReturnPost, related]

/-- The complete public `Nat.add` checked arm has one common validated/count
prefix followed by a result-count split.  Both the one-limb producer and the
multi-limb allocation/writer producer end in the same typed, scratch-free Nat
return suffix.  The producer bodies stay existential here so their semantic
contracts can be proved independently without duplicating the large prefix. -/
theorem natAddFunction_checkedResult_shape :
    ∃ checkedPrefix oneLimbProducer multiLimbProducer,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          (checkedPrefix ++ [
            .localGet
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1,
            .i32Const .uint32 1,
            .i32Eq,
            .ifElse
              (oneLimbProducer ++ typedNaturalReturnSource)
              (multiLimbProducer ++ typedNaturalReturnSource)]) := by
  refine ⟨_, _, _, rfl⟩

/-- Fixed-local Talos spelling of the checked result-count split. -/
def checkedResultDispatchProgram (oneLimb multiLimb : Wasm.Program) :
    Wasm.Program := [
  .localGet 10,
  .const 1,
  .eq,
  .iff 0 0 oneLimb multiLimb]

/-- Exact source prefix of checked `Nat.add`, from flavor initialization
through validation, magnitude counts, maximum-count selection, and the carry
scan.  Every potentially trapping operation is a named resident helper call;
the remaining instructions only update scalar locals. -/
def checkedNatAddPrefixSource
    (left right leftFlavor rightFlavor leftCount rightCount count resultCount
      carry : Lean.FVarId) : List Fir.Wasm.Instruction := [
  .i32Const .uint32 0,
  .localSet leftFlavor,
  .i32Const .uint32 0,
  .localSet rightFlavor,
  .localGet left,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalName),
  .localGet right,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalName),
  .localGet left,
  .localGet leftFlavor,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountName),
  .localSet leftCount,
  .localGet right,
  .localGet rightFlavor,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountName),
  .localSet rightCount,
  .localGet leftCount,
  .localGet rightCount,
  .i32LtU,
  .ifElse
    [.localGet rightCount, .localSet count]
    [.localGet leftCount, .localSet count],
  .localGet left,
  .localGet leftFlavor,
  .localGet right,
  .localGet rightFlavor,
  .i32Const .uint32 0,
  .localGet count,
  .i32Const .uint32 0,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromName),
  .localSet carry,
  .localGet count,
  .localGet carry,
  .i32Add,
  .localSet resultCount]

/-- Fixed-local Talos spelling of `checkedNatAddPrefixSource`. -/
def checkedNatAddPrefixProgram
    (validateNaturalIndex magnitudeCountIndex sumCarryIndex : Nat) :
    Wasm.Program := [
  .const 0, .localSet 5,
  .const 0, .localSet 6,
  .localGet 0, .call validateNaturalIndex,
  .localGet 1, .call validateNaturalIndex,
  .localGet 0, .localGet 5, .call magnitudeCountIndex, .localSet 7,
  .localGet 1, .localGet 6, .call magnitudeCountIndex, .localSet 8,
  .localGet 7, .localGet 8, .ltU,
  .iff 0 0 [.localGet 8, .localSet 9] [.localGet 7, .localSet 9],
  .localGet 0, .localGet 5, .localGet 1, .localGet 6,
  .const 0, .localGet 9, .const 0,
  .call sumCarryIndex, .localSet 15,
  .localGet 9, .localGet 15, .add, .localSet 10]

/-- Machine-word maximum used by the checked `Nat.add` count selection. -/
def checkedMaxCountWord (leftCount rightCount : UInt32) : UInt32 :=
  if leftCount < rightCount then rightCount else leftCount

/-- Factored Talos program for the checked operand-count maximum. -/
def checkedMaxCountProgram : Wasm.Program := [
  .localGet 7, .localGet 8, .ltU,
  .iff 0 0 [.localGet 8, .localSet 9] [.localGet 7, .localSet 9]]

/-- The generated count selector computes the machine maximum and changes
only its destination local. -/
theorem wp_checkedMaxCountProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterCount : Wasm.Locals} {leftCount rightCount : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (leftCountLocal : initial.get 7 = some (.i32 leftCount))
    (rightCountLocal : initial.get 8 = some (.i32 rightCount))
    (countSet :
      ({ initial with values :=
          (.i32 (checkedMaxCountWord leftCount rightCount) :: tail) }).set? 9
        (.i32 (checkedMaxCountWord leftCount rightCount)) = some afterCount)
    (continued : Wasm.wp module rest Q store
      { afterCount with values := tail } env) :
    Wasm.wp module (checkedMaxCountProgram ++ rest) Q store
      { initial with values := tail } env := by
  have leftAt (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get 7 =
        some (.i32 leftCount) := by simpa using leftCountLocal
  have rightAt (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get 8 =
        some (.i32 rightCount) := by simpa using rightCountLocal
  unfold checkedMaxCountProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    leftAt, rightAt, Wasm.wp_ltU_cons]
  apply Wasm.wp_iff_cons rfl
  by_cases less : leftCount < rightCount
  · simp only [if_pos less, if_pos (by decide : (1 : UInt32) ≠ 0),
      Wasm.wp_localGet_cons, rightAt, Wasm.wp_localSet_cons]
    have countSetRight :
        ({ initial with values := .i32 rightCount :: tail }).set? 9
          (.i32 rightCount) = some afterCount := by
      simpa [checkedMaxCountWord, less] using countSet
    rw [countSetRight]
    simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
    exact continued
  · simp only [if_neg less, if_neg (by decide : ¬(0 : UInt32) ≠ 0),
      Wasm.wp_localGet_cons, leftAt, Wasm.wp_localSet_cons]
    have countSetLeft :
        ({ initial with values := .i32 leftCount :: tail }).set? 9
          (.i32 leftCount) = some afterCount := by
      simpa [checkedMaxCountWord, less] using countSet
    rw [countSetLeft]
    simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
    exact continued

/-- Factored carry-scan call and result-count update from checked `Nat.add`. -/
def checkedCarryResultCountProgram (sumCarryIndex : Nat) : Wasm.Program := [
  .localGet 0, .localGet 5, .localGet 1, .localGet 6,
  .const 0, .localGet 9, .const 0,
  .call sumCarryIndex, .localSet 15,
  .localGet 9, .localGet 15, .add, .localSet 10]

/-- A semantically specified carry scan composes with the exact generated
local writes.  The result count is machine addition of the selected limb
count and the returned carry; a later helper contract proves the carry is a
bit and denotes the mathematical overflow limb. -/
theorem wp_checkedCarryResultCountProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterCarry afterResultCount : Wasm.Locals}
    {sumCarryIndex : Nat}
    {leftWord rightWord leftFlavor rightFlavor count carry : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorLocal : initial.get 5 = some (.i32 leftFlavor))
    (rightFlavorLocal : initial.get 6 = some (.i32 rightFlavor))
    (countLocal : initial.get 9 = some (.i32 count))
    (carrySet :
      ({ initial with values := .i32 carry :: tail }).set? 15 (.i32 carry) =
        some afterCarry)
    (resultCountSet :
      ({ afterCarry with values := .i32 (carry + count) :: tail }).set? 10
        (.i32 (carry + count)) = some afterResultCount)
    (sumCarryRun : Wasm.TerminatesWith env module sumCarryIndex store
      ([.i32 0, .i32 count, .i32 0, .i32 rightFlavor, .i32 rightWord,
          .i32 leftFlavor, .i32 leftWord] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 carry :: tail))
    (continued : Wasm.wp module rest Q store
      { afterResultCount with values := tail } env) :
    Wasm.wp module (checkedCarryResultCountProgram sumCarryIndex ++ rest)
      Q store { initial with values := tail } env := by
  have carryUpdate := FirTalos.Correctness.localUpdate_of_set? carrySet
  have initialAt (index : Nat) (value : Wasm.Value)
      (found : initial.get index = some value) (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get index = some value := by
    simpa using found
  have afterCarryAt (index : Nat) (value : Wasm.Value)
      (different : index ≠ 15) (found : initial.get index = some value)
      (values : List Wasm.Value) :
      ({ afterCarry with values } : Wasm.Locals).get index = some value := by
    change afterCarry.get index = some value
    rw [carryUpdate.2 different]
    simpa using found
  have carryAt (values : List Wasm.Value) :
      ({ afterCarry with values } : Wasm.Locals).get 15 =
        some (.i32 carry) := by
    simpa using carryUpdate.1
  unfold checkedCarryResultCountProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    initialAt 0 (.i32 leftWord) leftLocal,
    initialAt 5 (.i32 leftFlavor) leftFlavorLocal,
    initialAt 1 (.i32 rightWord) rightLocal,
    initialAt 6 (.i32 rightFlavor) rightFlavorLocal,
    Wasm.wp_const_cons, initialAt 9 (.i32 count) countLocal]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 count, .i32 0, .i32 rightFlavor,
        .i32 rightWord, .i32 leftFlavor, .i32 leftWord])
      (tail := tail)
      (locals := { initial with values := .i32 carry :: tail })
      (updated := afterCarry) (physicalResult := .i32 carry)
      (callRun := sumCarryRun) (targetSet := carrySet)
  simp only [Wasm.wp_localGet_cons,
    afterCarryAt 9 (.i32 count) (by decide) countLocal,
    carryAt, Wasm.wp_add_cons, Wasm.wp_localSet_cons, resultCountSet]
  exact continued

/-- Validation and per-operand magnitude-count prefix before maximum/count
arithmetic. -/
def checkedNatAddSetupProgram
    (validateNaturalIndex magnitudeCountIndex : Nat) : Wasm.Program := [
  .const 0, .localSet 5,
  .const 0, .localSet 6,
  .localGet 0, .call validateNaturalIndex,
  .localGet 1, .call validateNaturalIndex,
  .localGet 0, .localGet 5, .call magnitudeCountIndex, .localSet 7,
  .localGet 1, .localGet 6, .call magnitudeCountIndex, .localSet 8]

/-- The full checked prefix is exactly setup, count maximum, and carry scan. -/
theorem checkedNatAddPrefixProgram_factor
    (validateNaturalIndex magnitudeCountIndex sumCarryIndex : Nat) :
    checkedNatAddPrefixProgram validateNaturalIndex magnitudeCountIndex
        sumCarryIndex =
      checkedNatAddSetupProgram validateNaturalIndex magnitudeCountIndex ++
        checkedMaxCountProgram ++
        checkedCarryResultCountProgram sumCarryIndex := by
  rfl

/-- Valid operand contracts compose through the exact validation/count setup.
Since each validator runs before its corresponding magnitude accessor,
malformed values retain the generated trapping order rather than acquiring a
proof-side unchecked read. -/
theorem wp_checkedNatAddSetupProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterLeftFlavor afterRightFlavor afterLeftCount afterRightCount :
      Wasm.Locals}
    {validateNaturalIndex magnitudeCountIndex : Nat}
    {leftWord rightWord leftCount rightCount : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorSet :
      ({ initial with values := .i32 0 :: tail }).set? 5 (.i32 0) =
        some afterLeftFlavor)
    (rightFlavorSet :
      ({ afterLeftFlavor with values := .i32 0 :: tail }).set? 6 (.i32 0) =
        some afterRightFlavor)
    (leftCountSet :
      ({ afterRightFlavor with values := .i32 leftCount :: tail }).set? 7
        (.i32 leftCount) = some afterLeftCount)
    (rightCountSet :
      ({ afterLeftCount with values := .i32 rightCount :: tail }).set? 8
        (.i32 rightCount) = some afterRightCount)
    (validateLeft : Wasm.TerminatesWith env module validateNaturalIndex store
      (.i32 leftWord :: tail)
      (fun final values => final = store ∧ values = tail))
    (validateRight : Wasm.TerminatesWith env module validateNaturalIndex store
      (.i32 rightWord :: tail)
      (fun final values => final = store ∧ values = tail))
    (leftCountRun : Wasm.TerminatesWith env module magnitudeCountIndex store
      ([.i32 0, .i32 leftWord] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftCount :: tail))
    (rightCountRun : Wasm.TerminatesWith env module magnitudeCountIndex store
      ([.i32 0, .i32 rightWord] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightCount :: tail))
    (continued : Wasm.wp module rest Q store
      { afterRightCount with values := tail } env) :
    Wasm.wp module
      (checkedNatAddSetupProgram validateNaturalIndex magnitudeCountIndex ++
        rest)
      Q store { initial with values := tail } env := by
  have leftFlavorUpdate :=
    FirTalos.Correctness.localUpdate_of_set? leftFlavorSet
  have rightFlavorUpdate :=
    FirTalos.Correctness.localUpdate_of_set? rightFlavorSet
  have leftCountUpdate :=
    FirTalos.Correctness.localUpdate_of_set? leftCountSet
  have initialAt (index : Nat) (value : Wasm.Value)
      (found : initial.get index = some value) (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get index = some value := by
    simpa using found
  have afterLeftFlavorAt (index : Nat) (value : Wasm.Value)
      (different : index ≠ 5) (found : initial.get index = some value)
      (values : List Wasm.Value) :
      ({ afterLeftFlavor with values } : Wasm.Locals).get index = some value := by
    change afterLeftFlavor.get index = some value
    rw [leftFlavorUpdate.2 different]
    simpa using found
  have afterRightFlavorAt (index : Nat) (value : Wasm.Value)
      (differentRight : index ≠ 6) (differentLeft : index ≠ 5)
      (found : initial.get index = some value) (values : List Wasm.Value) :
      ({ afterRightFlavor with values } : Wasm.Locals).get index = some value := by
    change afterRightFlavor.get index = some value
    rw [rightFlavorUpdate.2 differentRight]
    exact afterLeftFlavorAt index value differentLeft found _
  have leftFlavorAt (values : List Wasm.Value) :
      ({ afterRightFlavor with values } : Wasm.Locals).get 5 =
        some (.i32 0) := by
    change afterRightFlavor.get 5 = some (.i32 0)
    rw [rightFlavorUpdate.2 (by decide)]
    exact leftFlavorUpdate.1
  have rightFlavorAt (values : List Wasm.Value) :
      ({ afterRightFlavor with values } : Wasm.Locals).get 6 =
        some (.i32 0) := by
    simpa using rightFlavorUpdate.1
  have afterLeftCountAt (index : Nat) (value : Wasm.Value)
      (different : index ≠ 7)
      (found : afterRightFlavor.get index = some value)
      (values : List Wasm.Value) :
      ({ afterLeftCount with values } : Wasm.Locals).get index = some value := by
    change afterLeftCount.get index = some value
    rw [leftCountUpdate.2 different]
    simpa using found
  have rightAfterLeftCount (values : List Wasm.Value) :
      ({ afterLeftCount with values } : Wasm.Locals).get 1 =
        some (.i32 rightWord) := by
    apply afterLeftCountAt 1 (.i32 rightWord) (by decide)
    exact afterRightFlavorAt 1 (.i32 rightWord) (by decide) (by decide)
      rightLocal _
  have rightFlavorAfterLeftCount (values : List Wasm.Value) :
      ({ afterLeftCount with values } : Wasm.Locals).get 6 =
        some (.i32 0) := by
    apply afterLeftCountAt 6 (.i32 0) (by decide)
    exact rightFlavorAt _
  unfold checkedNatAddSetupProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_const_cons,
    Wasm.wp_localSet_cons, leftFlavorSet, rightFlavorSet,
    Wasm.wp_localGet_cons,
    afterRightFlavorAt 0 (.i32 leftWord) (by decide) (by decide) leftLocal]
  apply Wasm.wp_call_tw validateLeft
  intro final values validatedLeft
  rcases validatedLeft with ⟨rfl, valuesEq⟩
  rw [valuesEq]
  simp only [Wasm.wp_localGet_cons,
    afterRightFlavorAt 1 (.i32 rightWord) (by decide) (by decide) rightLocal]
  apply Wasm.wp_call_tw validateRight
  intro final values validatedRight
  rcases validatedRight with ⟨rfl, valuesEq⟩
  rw [valuesEq]
  simp only [Wasm.wp_localGet_cons,
    afterRightFlavorAt 0 (.i32 leftWord) (by decide) (by decide) leftLocal,
    leftFlavorAt]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 leftWord]) (tail := tail)
      (locals := { afterRightFlavor with values := .i32 leftCount :: tail })
      (updated := afterLeftCount) (physicalResult := .i32 leftCount)
      (callRun := leftCountRun) (targetSet := leftCountSet)
  simp only [Wasm.wp_localGet_cons, rightAfterLeftCount,
    rightFlavorAfterLeftCount]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 rightWord]) (tail := tail)
      (locals := { afterLeftCount with values := .i32 rightCount :: tail })
      (updated := afterRightCount) (physicalResult := .i32 rightCount)
      (callRun := rightCountRun) (targetSet := rightCountSet)
  exact continued

/-- Exact execution of the entire checked `Nat.add` prefix for valid operand
helper contracts.  The theorem leaves the chosen maximum count, carry bit,
and machine result count in the actual generated local slots consumed by the
one-limb/multi-limb dispatcher. -/
theorem wp_checkedNatAddPrefixProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterLeftFlavor afterRightFlavor afterLeftCount afterRightCount
      afterCount afterCarry afterResultCount : Wasm.Locals}
    {validateNaturalIndex magnitudeCountIndex sumCarryIndex : Nat}
    {leftWord rightWord leftCount rightCount carry : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorSet :
      ({ initial with values := .i32 0 :: tail }).set? 5 (.i32 0) =
        some afterLeftFlavor)
    (rightFlavorSet :
      ({ afterLeftFlavor with values := .i32 0 :: tail }).set? 6 (.i32 0) =
        some afterRightFlavor)
    (leftCountSet :
      ({ afterRightFlavor with values := .i32 leftCount :: tail }).set? 7
        (.i32 leftCount) = some afterLeftCount)
    (rightCountSet :
      ({ afterLeftCount with values := .i32 rightCount :: tail }).set? 8
        (.i32 rightCount) = some afterRightCount)
    (countSet :
      ({ afterRightCount with values :=
          (.i32 (checkedMaxCountWord leftCount rightCount) :: tail) }).set? 9
        (.i32 (checkedMaxCountWord leftCount rightCount)) = some afterCount)
    (carrySet :
      ({ afterCount with values := .i32 carry :: tail }).set? 15
        (.i32 carry) = some afterCarry)
    (resultCountSet :
      ({ afterCarry with values :=
          (.i32 (carry + checkedMaxCountWord leftCount rightCount) :: tail) }).set?
        10 (.i32 (carry + checkedMaxCountWord leftCount rightCount)) =
          some afterResultCount)
    (validateLeft : Wasm.TerminatesWith env module validateNaturalIndex store
      (.i32 leftWord :: tail)
      (fun final values => final = store ∧ values = tail))
    (validateRight : Wasm.TerminatesWith env module validateNaturalIndex store
      (.i32 rightWord :: tail)
      (fun final values => final = store ∧ values = tail))
    (leftCountRun : Wasm.TerminatesWith env module magnitudeCountIndex store
      ([.i32 0, .i32 leftWord] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftCount :: tail))
    (rightCountRun : Wasm.TerminatesWith env module magnitudeCountIndex store
      ([.i32 0, .i32 rightWord] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightCount :: tail))
    (sumCarryRun : Wasm.TerminatesWith env module sumCarryIndex store
      ([.i32 0, .i32 (checkedMaxCountWord leftCount rightCount), .i32 0,
          .i32 0, .i32 rightWord, .i32 0, .i32 leftWord] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 carry :: tail))
    (continued : Wasm.wp module rest Q store
      { afterResultCount with values := tail } env) :
    Wasm.wp module
      (checkedNatAddPrefixProgram validateNaturalIndex magnitudeCountIndex
          sumCarryIndex ++ rest)
      Q store { initial with values := tail } env := by
  have leftFlavorUpdate :=
    FirTalos.Correctness.localUpdate_of_set? leftFlavorSet
  have rightFlavorUpdate :=
    FirTalos.Correctness.localUpdate_of_set? rightFlavorSet
  have leftCountUpdate :=
    FirTalos.Correctness.localUpdate_of_set? leftCountSet
  have rightCountUpdate :=
    FirTalos.Correctness.localUpdate_of_set? rightCountSet
  have countUpdate := FirTalos.Correctness.localUpdate_of_set? countSet
  have afterSetupPreserved {index : Nat} {value : Wasm.Value}
      (ne5 : index ≠ 5) (ne6 : index ≠ 6) (ne7 : index ≠ 7)
      (ne8 : index ≠ 8) (found : initial.get index = some value) :
      afterRightCount.get index = some value := by
    calc
      _ = ({ afterLeftCount with values := .i32 rightCount :: tail } :
          Wasm.Locals).get index := rightCountUpdate.2 ne8
      _ = afterLeftCount.get index := rfl
      _ = ({ afterRightFlavor with values := .i32 leftCount :: tail } :
          Wasm.Locals).get index := leftCountUpdate.2 ne7
      _ = afterRightFlavor.get index := rfl
      _ = ({ afterLeftFlavor with values := .i32 0 :: tail } :
          Wasm.Locals).get index := rightFlavorUpdate.2 ne6
      _ = afterLeftFlavor.get index := rfl
      _ = ({ initial with values := .i32 0 :: tail } : Wasm.Locals).get index :=
        leftFlavorUpdate.2 ne5
      _ = initial.get index := rfl
      _ = some value := found
  have leftFlavorAfterSetup : afterRightCount.get 5 = some (.i32 0) := by
    calc
      _ = ({ afterLeftCount with values := .i32 rightCount :: tail } :
          Wasm.Locals).get 5 := rightCountUpdate.2 (by decide)
      _ = afterLeftCount.get 5 := rfl
      _ = ({ afterRightFlavor with values := .i32 leftCount :: tail } :
          Wasm.Locals).get 5 := leftCountUpdate.2 (by decide)
      _ = afterRightFlavor.get 5 := rfl
      _ = ({ afterLeftFlavor with values := .i32 0 :: tail } :
          Wasm.Locals).get 5 := rightFlavorUpdate.2 (by decide)
      _ = afterLeftFlavor.get 5 := rfl
      _ = some (.i32 0) := leftFlavorUpdate.1
  have rightFlavorAfterSetup : afterRightCount.get 6 = some (.i32 0) := by
    calc
      _ = ({ afterLeftCount with values := .i32 rightCount :: tail } :
          Wasm.Locals).get 6 := rightCountUpdate.2 (by decide)
      _ = afterLeftCount.get 6 := rfl
      _ = ({ afterRightFlavor with values := .i32 leftCount :: tail } :
          Wasm.Locals).get 6 := leftCountUpdate.2 (by decide)
      _ = afterRightFlavor.get 6 := rfl
      _ = some (.i32 0) := rightFlavorUpdate.1
  have leftCountAfterSetup : afterRightCount.get 7 = some (.i32 leftCount) := by
    rw [rightCountUpdate.2 (by decide)]
    exact leftCountUpdate.1
  have rightCountAfterSetup :
      afterRightCount.get 8 = some (.i32 rightCount) := rightCountUpdate.1
  have afterCountAt (index : Nat) (value : Wasm.Value)
      (different : index ≠ 9)
      (found : afterRightCount.get index = some value) :
      afterCount.get index = some value := by
    rw [countUpdate.2 different]
    simpa using found
  have selectedCountAfter : afterCount.get 9 =
      some (.i32 (checkedMaxCountWord leftCount rightCount)) := countUpdate.1
  rw [checkedNatAddPrefixProgram_factor]
  simp only [List.append_assoc]
  apply wp_checkedNatAddSetupProgram leftLocal rightLocal leftFlavorSet
    rightFlavorSet leftCountSet rightCountSet validateLeft validateRight
    leftCountRun rightCountRun
  apply wp_checkedMaxCountProgram leftCountAfterSetup rightCountAfterSetup
    countSet
  apply wp_checkedCarryResultCountProgram
    (afterCountAt 0 (.i32 leftWord) (by decide)
      (afterSetupPreserved (by decide) (by decide) (by decide) (by decide)
        leftLocal))
    (afterCountAt 1 (.i32 rightWord) (by decide)
      (afterSetupPreserved (by decide) (by decide) (by decide) (by decide)
        rightLocal))
    (afterCountAt 5 (.i32 0) (by decide) leftFlavorAfterSetup)
    (afterCountAt 6 (.i32 0) (by decide) rightFlavorAfterSetup)
    selectedCountAfter carrySet resultCountSet sumCarryRun continued

/-- The checked prefix in the actual W7 `Nat.add` body is exactly the public
proof-side spelling above. -/
theorem natAddFunction_checkedPrefix_exact_shape :
    ∃ oneLimbProducer multiLimbProducer,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          (checkedNatAddPrefixSource
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[5]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[6]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[7]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[13]!.1 ++
            [.localGet
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1,
              .i32Const .uint32 1,
              .i32Eq,
              .ifElse
                (oneLimbProducer ++ typedNaturalReturnSource)
                (multiLimbProducer ++ typedNaturalReturnSource)]) := by
  refine ⟨_, _, rfl⟩

/-- Successful helper-index resolution adapts the complete checked prefix to
the exact fixed-local Talos program.  This pins malformed-input trapping to
the two actual validator calls and leaves no unchecked source fragment before
the result-count split. -/
theorem instructions_checkedNatAddPrefixSource
    {sourceModule : Fir.Wasm.Module}
    {validateNaturalIndex magnitudeCountIndex sumCarryIndex : Nat}
    (validateNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalName) =
        some validateNaturalIndex)
    (magnitudeCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountName) =
        some magnitudeCountIndex)
    (sumCarryFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.sumCarryFromName) =
        some sumCarryIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction []
      (checkedNatAddPrefixSource
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[5]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[6]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[7]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[13]!.1) =
      .ok (checkedNatAddPrefixProgram validateNaturalIndex magnitudeCountIndex
        sumCarryIndex) := by
  have leftFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1 =
        some 0 := by decide
  have rightFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1 =
        some 1 := by decide
  have leftFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1 =
        some 5 := by decide
  have rightFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1 =
        some 6 := by decide
  have leftCountFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[5]!.1 =
        some 7 := by decide
  have rightCountFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[6]!.1 =
        some 8 := by decide
  have countFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[7]!.1 =
        some 9 := by decide
  have resultCountFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1 =
        some 10 := by decide
  have carryFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[13]!.1 =
        some 15 := by decide
  set_option maxRecDepth 100000 in
    simp [checkedNatAddPrefixSource, checkedNatAddPrefixProgram,
      FirTalos.instructions, FirTalos.instruction,
      validateNaturalFound, magnitudeCountFound, sumCarryFound,
      leftFound, rightFound, leftFlavorFound, rightFlavorFound,
      leftCountFound, rightCountFound, countFound, resultCountFound,
      carryFound, Bind.bind, Except.bind, pure, Except.pure]

/-- A checked result count of one selects the canonical one-limb producer. -/
theorem wp_checkedResultDispatchProgram_one
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store resultStore : Wasm.Store host}
    {locals : Wasm.Locals} {oneLimb multiLimb : Wasm.Program}
    {witness : RefinementWitness} {word : Word32}
    {reference : Fir.LeanIR.Impure.ObjectRef} {tail : List Wasm.Value}
    (resultCountLocal : locals.get 10 = some (.i32 1))
    (oneLimbCorrect :
      Wasm.wp module oneLimb
        (TypedNaturalReturnPost witness word reference resultStore tail)
        store { locals with values := tail } env) :
    Wasm.wp module (checkedResultDispatchProgram oneLimb multiLimb)
      (TypedNaturalReturnPost witness word reference resultStore tail)
      store { locals with values := tail } env := by
  have resultCountAt (values : List Wasm.Value) :
      ({ locals with values } : Wasm.Locals).get 10 =
        some (.i32 1) := by simpa using resultCountLocal
  unfold checkedResultDispatchProgram
  simp only [Wasm.wp_localGet_cons, resultCountAt, Wasm.wp_const_cons,
    Wasm.wp_eq_cons]
  apply Wasm.wp_iff_cons rfl
  apply Wasm.wp.conseq (h := oneLimbCorrect)
  intro continuation correct
  rcases correct with ⟨rfl, related⟩
  exact ⟨rfl, related⟩

/-- Any other checked result count selects the allocation/writer producer. -/
theorem wp_checkedResultDispatchProgram_multi
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store resultStore : Wasm.Store host}
    {locals : Wasm.Locals} {oneLimb multiLimb : Wasm.Program}
    {resultCount : UInt32} {witness : RefinementWitness} {word : Word32}
    {reference : Fir.LeanIR.Impure.ObjectRef} {tail : List Wasm.Value}
    (resultCountLocal : locals.get 10 = some (.i32 resultCount))
    (notOne : resultCount ≠ 1)
    (multiLimbCorrect :
      Wasm.wp module multiLimb
        (TypedNaturalReturnPost witness word reference resultStore tail)
        store { locals with values := tail } env) :
    Wasm.wp module (checkedResultDispatchProgram oneLimb multiLimb)
      (TypedNaturalReturnPost witness word reference resultStore tail)
      store { locals with values := tail } env := by
  have resultCountAt (values : List Wasm.Value) :
      ({ locals with values } : Wasm.Locals).get 10 =
        some (.i32 resultCount) := by simpa using resultCountLocal
  unfold checkedResultDispatchProgram
  simp only [Wasm.wp_localGet_cons, resultCountAt, Wasm.wp_const_cons,
    Wasm.wp_eq_cons, if_neg notOne]
  apply Wasm.wp_iff_cons (c := (0 : UInt32)) (vs := tail) rfl
  apply Wasm.wp.conseq (h := multiLimbCorrect)
  intro continuation correct
  rcases correct with ⟨rfl, related⟩
  exact ⟨rfl, related⟩

/-- Exact source spelling of the checked one-limb result producer.  Operand
validation and count selection precede this fragment; its four magnitude
reads feed the resident 64-bit `naturalSum` constructor. -/
def checkedOneLimbProducerSource (left right leftFlavor rightFlavor
    leftLow leftHigh rightLow rightHigh : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet left,
  .localGet leftFlavor,
  .i32Const .uint32 0,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName),
  .localSet leftLow,
  .localGet left,
  .localGet leftFlavor,
  .i32Const .uint32 0,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName),
  .localSet leftHigh,
  .localGet right,
  .localGet rightFlavor,
  .i32Const .uint32 0,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName),
  .localSet rightLow,
  .localGet right,
  .localGet rightFlavor,
  .i32Const .uint32 0,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName),
  .localSet rightHigh,
  .localGet leftLow,
  .localGet leftHigh,
  .localGet rightLow,
  .localGet rightHigh,
  .call (.declaration Fir.Wasm.Emit.ResidentNumeric.naturalSumName)]

/-- Talos spelling of the checked one-limb producer in `natAddFunction`'s
fixed local layout. -/
def checkedOneLimbProducerProgram (magnitudeLowIndex magnitudeHighIndex
    naturalSumIndex : Nat) : Wasm.Program := [
  .localGet 0, .localGet 5, .const 0, .call magnitudeLowIndex, .localSet 11,
  .localGet 0, .localGet 5, .const 0, .call magnitudeHighIndex, .localSet 12,
  .localGet 1, .localGet 6, .const 0, .call magnitudeLowIndex, .localSet 13,
  .localGet 1, .localGet 6, .const 0, .call magnitudeHighIndex, .localSet 14,
  .localGet 11, .localGet 12, .localGet 13, .localGet 14,
  .call naturalSumIndex]

/-- The existential one-limb producer in the common checked shape is exactly
the four magnitude reads followed by `naturalSum`; only the multi-limb
producer remains abstract. -/
theorem natAddFunction_checkedOneLimb_shape :
    ∃ checkedPrefix multiLimbProducer,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          (checkedPrefix ++ [
            .localGet
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1,
            .i32Const .uint32 1,
            .i32Eq,
            .ifElse
              (checkedOneLimbProducerSource
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[9]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[10]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[11]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[12]!.1 ++
                  typedNaturalReturnSource)
              (multiLimbProducer ++ typedNaturalReturnSource)]) := by
  refine ⟨_, _, rfl⟩

/-- Successful call-index resolution adapts the concrete one-limb source
producer to its exact fixed-local Talos program. -/
theorem instructions_checkedOneLimbProducerSource
    {sourceModule : Fir.Wasm.Module}
    {magnitudeLowIndex magnitudeHighIndex naturalSumIndex : Nat}
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex)
    (naturalSumFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.naturalSumName) =
        some naturalSumIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction []
      (checkedOneLimbProducerSource
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[9]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[10]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[11]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[12]!.1) =
      .ok (checkedOneLimbProducerProgram magnitudeLowIndex magnitudeHighIndex
        naturalSumIndex) := by
  have leftFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1 =
        some 0 := by decide
  have rightFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1 =
        some 1 := by decide
  have leftFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1 =
        some 5 := by decide
  have rightFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1 =
        some 6 := by decide
  have leftLowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[9]!.1 =
        some 11 := by decide
  have leftHighFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[10]!.1 =
        some 12 := by decide
  have rightLowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[11]!.1 =
        some 13 := by decide
  have rightHighFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[12]!.1 =
        some 14 := by decide
  simp [checkedOneLimbProducerSource, checkedOneLimbProducerProgram,
    FirTalos.instructions, FirTalos.instruction, leftFound, rightFound,
    leftFlavorFound, rightFlavorFound, leftLowFound, leftHighFound,
    rightLowFound, rightHighFound, magnitudeLowFound, magnitudeHighFound,
    naturalSumFound, Bind.bind, Except.bind, pure, Except.pure]

/-- Public proof-side spelling of the emitter's repeated multiply-by-eight
address calculation.  Keeping it named makes the two carry-limb stores in the
checked `Nat.add` path explicit without exposing the generator's private
helper name. -/
def checkedScale8Source (source destination : Lean.FVarId) :
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

/-- Exact Talos spelling of `checkedScale8Source`. -/
def checkedScale8Program (sourceIndex destinationIndex : Nat) :
    Wasm.Program := [
  .localGet sourceIndex, .localGet sourceIndex, .add,
  .localSet destinationIndex,
  .localGet destinationIndex, .localGet destinationIndex, .add,
  .localSet destinationIndex,
  .localGet destinationIndex, .localGet destinationIndex, .add,
  .localSet destinationIndex]

/-- Source instructions that write one constant half of the final carry limb.
The emitter deliberately recomputes the scaled index before each half-word. -/
def checkedConstantLimbPartSource (object index scaled : Lean.FVarId)
    (value : UInt32) (offset : Nat) : List Fir.Wasm.Instruction :=
  checkedScale8Source index scaled ++ [
    .localGet object,
    .i32Const .uint32 32,
    .i32Add,
    .localGet scaled,
    .i32Add,
    .i32Const .uint32 value,
    .i32Store .uint32 (UInt32.ofNat offset)]

/-- Talos spelling of `checkedConstantLimbPartSource`. -/
def checkedConstantLimbPartProgram (objectIndex indexIndex scaledIndex : Nat)
    (value : UInt32) (offset : Nat) : Wasm.Program :=
  checkedScale8Program indexIndex scaledIndex ++ [
    .localGet objectIndex,
    .const 32,
    .add,
    .localGet scaledIndex,
    .add,
    .const value,
    .store32 (UInt32.ofNat offset)]

/-- Public proof-side spelling of one dynamic limb half store.  This is the
same address calculation as the final constant-carry writer, but obtains the
stored word from a local produced by the arithmetic step. -/
def checkedLocalLimbPartSource
    (object index scaled value : Lean.FVarId) (offset : Nat) :
    List Fir.Wasm.Instruction :=
  checkedScale8Source index scaled ++ [
    .localGet object,
    .i32Const .uint32 32,
    .i32Add,
    .localGet scaled,
    .i32Add,
    .localGet value,
    .i32Store .uint32 (UInt32.ofNat offset)]

/-- Exact Talos spelling of `checkedLocalLimbPartSource`. -/
def checkedLocalLimbPartProgram
    (objectIndex indexIndex scaledIndex valueIndex : Nat) (offset : Nat) :
    Wasm.Program :=
  checkedScale8Program indexIndex scaledIndex ++ [
    .localGet objectIndex,
    .const 32,
    .add,
    .localGet scaledIndex,
    .add,
    .localGet valueIndex,
    .store32 (UInt32.ofNat offset)]

/-- Successful local resolution adapts a dynamic half-limb store independently
of its surrounding function and label stack. -/
theorem instructions_checkedLocalLimbPartSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {object index scaled value : Lean.FVarId}
    {objectIndex indexIndex scaledIndex valueIndex offset : Nat}
    (objectFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) object =
        some objectIndex)
    (indexFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) index =
        some indexIndex)
    (scaledFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) scaled =
        some scaledIndex)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some valueIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (checkedLocalLimbPartSource object index scaled value offset) =
        .ok (checkedLocalLimbPartProgram objectIndex indexIndex scaledIndex
          valueIndex offset) := by
  simp [checkedLocalLimbPartSource, checkedLocalLimbPartProgram,
    checkedScale8Source, checkedScale8Program, FirTalos.instructions,
    FirTalos.instruction, objectFound, indexFound, scaledFound, valueFound,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Exact pair of stores used when a multi-limb addition has a final carry.
The new most-significant limb is the 64-bit value one, hence low word one and
high word zero. -/
def checkedCarryLimbWritesProgram : Wasm.Program :=
  checkedConstantLimbPartProgram 2 9 17 1 0 ++
    checkedConstantLimbPartProgram 2 9 17 0 4

/-- Machine-word result of the emitter's three successive doublings.  The
definition is intentionally modular: it is the exact `i32` address arithmetic
performed by Wasm, before a later layout theorem rules out wraparound for a
valid natural allocation. -/
def checkedScale8Word (index : UInt32) : UInt32 :=
  let twice := index + index
  let fourTimes := twice + twice
  fourTimes + fourTimes

/-- The emitter's three doublings are multiplication by eight in wasm32's
modular arithmetic. -/
theorem checkedScale8Word_eq_mul8 (index : UInt32) :
    checkedScale8Word index = 8 * index := by
  unfold checkedScale8Word
  bv_decide

/-- Effective payload base computed by a checked carry-limb store. -/
def checkedLimbBase (object index : UInt32) : UInt32 :=
  checkedScale8Word index + (UInt32.ofNat headerBytes + object)

/-- Reusable execution rule for the emitter's multiply-by-eight sequence.

The theorem exposes Talos's three checked local updates and nothing about
natural objects.  In particular, it remains useful for any resident helper
that computes a byte address from a 64-bit-limb index. -/
theorem wp_checkedScale8Program
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
      ({ afterSecond with values := .i32 (checkedScale8Word index) :: tail }).set?
          destinationIndex (.i32 (checkedScale8Word index)) = some afterThird)
    (continued :
      Wasm.wp module rest Q store { afterThird with values := tail } env) :
    Wasm.wp module (checkedScale8Program sourceIndex destinationIndex ++ rest)
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
  unfold checkedScale8Program
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    sourceAt, Wasm.wp_add_cons, Wasm.wp_localSet_cons, firstSet, firstAt,
    secondSet, secondAt]
  change
    match ({ afterSecond with values :=
        (.i32 (checkedScale8Word index) :: tail) }).set? destinationIndex
          (.i32 (checkedScale8Word index)) with
    | some updated =>
        Wasm.wp module rest Q store { updated with values := tail } env
    | none => Q (.Invalid "localSet index out of bounds")
  rw [thirdSet]
  exact continued

/-- One constant half-limb store, factored from its scale-by-eight address
calculation.  Its postcondition names the exact Wasm memory update; semantic
object validity is deliberately outside this low-level rule. -/
theorem wp_checkedConstantLimbPartProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterFirst afterSecond afterThird : Wasm.Locals}
    {objectIndex indexIndex scaledIndex : Nat}
    {object index value : UInt32} {offset : Nat}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (objectNeScaled : objectIndex ≠ scaledIndex)
    (objectLocal : initial.get objectIndex = some (.i32 object))
    (indexLocal : initial.get indexIndex = some (.i32 index))
    (firstSet :
      ({ initial with values := .i32 (index + index) :: tail }).set?
          scaledIndex (.i32 (index + index)) = some afterFirst)
    (secondSet :
      ({ afterFirst with values :=
          (.i32 (index + index + (index + index)) :: tail) }).set?
          scaledIndex (.i32 (index + index + (index + index))) =
            some afterSecond)
    (thirdSet :
      ({ afterSecond with values := .i32 (checkedScale8Word index) :: tail }).set?
          scaledIndex (.i32 (checkedScale8Word index)) = some afterThird)
    (writeInBounds :
      ¬(checkedLimbBase object index).toNat + (UInt32.ofNat offset).toNat + 4 >
        store.mem.pages * 65536)
    (continued :
      Wasm.wp module rest Q
        { store with mem := (store.mem.write32
            (checkedLimbBase object index + UInt32.ofNat offset) value) }
        { afterThird with values := tail } env) :
    Wasm.wp module
      (checkedConstantLimbPartProgram objectIndex indexIndex scaledIndex
          value offset ++ rest)
      Q store { initial with values := tail } env := by
  have firstUpdate := FirTalos.Correctness.localUpdate_of_set? firstSet
  have secondUpdate := FirTalos.Correctness.localUpdate_of_set? secondSet
  have thirdUpdate := FirTalos.Correctness.localUpdate_of_set? thirdSet
  have objectAfterThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get objectIndex =
        some (.i32 object) := by
    calc
      _ = afterThird.get objectIndex := rfl
      _ = ({ afterSecond with values := .i32 (checkedScale8Word index) :: tail } :
          Wasm.Locals).get objectIndex := thirdUpdate.2 objectNeScaled
      _ = afterSecond.get objectIndex := rfl
      _ = ({ afterFirst with values :=
          (.i32 (index + index + (index + index)) :: tail) } :
          Wasm.Locals).get objectIndex := secondUpdate.2 objectNeScaled
      _ = afterFirst.get objectIndex := rfl
      _ = ({ initial with values := .i32 (index + index) :: tail } :
          Wasm.Locals).get objectIndex := firstUpdate.2 objectNeScaled
      _ = initial.get objectIndex := rfl
      _ = some (.i32 object) := objectLocal
  have scaledAfterThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get scaledIndex =
        some (.i32 (checkedScale8Word index)) := by
    simpa using thirdUpdate.1
  unfold checkedConstantLimbPartProgram
  rw [List.append_assoc]
  apply wp_checkedScale8Program indexLocal firstSet secondSet thirdSet
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectAfterThird, Wasm.wp_const_cons, Wasm.wp_add_cons,
    scaledAfterThird, Wasm.wp_store32_cons]
  change (if (checkedLimbBase object index).toNat +
      (UInt32.ofNat offset).toNat + 4 >
      store.mem.pages * 65536 then
        Q (.Trap store "out of bounds memory access")
      else
        Wasm.wp module rest Q
          { store with mem := (store.mem.write32
              (checkedLimbBase object index + UInt32.ofNat offset) value) }
          { afterThird with values := tail } env)
  rw [if_neg writeInBounds]
  exact continued

/-- One locally sourced half-limb store, exposing the exact successor memory
while framing every local except the scale scratch destination. -/
theorem wp_checkedLocalLimbPartProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterFirst afterSecond afterThird : Wasm.Locals}
    {objectIndex indexIndex scaledIndex valueIndex : Nat}
    {object index value : UInt32} {offset : Nat}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (objectNeScaled : objectIndex ≠ scaledIndex)
    (valueNeScaled : valueIndex ≠ scaledIndex)
    (objectLocal : initial.get objectIndex = some (.i32 object))
    (indexLocal : initial.get indexIndex = some (.i32 index))
    (valueLocal : initial.get valueIndex = some (.i32 value))
    (firstSet :
      ({ initial with values := .i32 (index + index) :: tail }).set?
          scaledIndex (.i32 (index + index)) = some afterFirst)
    (secondSet :
      ({ afterFirst with values :=
          (.i32 (index + index + (index + index)) :: tail) }).set?
          scaledIndex (.i32 (index + index + (index + index))) =
            some afterSecond)
    (thirdSet :
      ({ afterSecond with values := .i32 (checkedScale8Word index) :: tail }).set?
          scaledIndex (.i32 (checkedScale8Word index)) = some afterThird)
    (writeInBounds :
      ¬(checkedLimbBase object index).toNat + (UInt32.ofNat offset).toNat + 4 >
        store.mem.pages * 65536)
    (continued :
      Wasm.wp module rest Q
        { store with mem := (store.mem.write32
            (checkedLimbBase object index + UInt32.ofNat offset) value) }
        { afterThird with values := tail } env) :
    Wasm.wp module
      (checkedLocalLimbPartProgram objectIndex indexIndex scaledIndex
          valueIndex offset ++ rest)
      Q store { initial with values := tail } env := by
  have firstUpdate := FirTalos.Correctness.localUpdate_of_set? firstSet
  have secondUpdate := FirTalos.Correctness.localUpdate_of_set? secondSet
  have thirdUpdate := FirTalos.Correctness.localUpdate_of_set? thirdSet
  have preservedAfterThird
      (preservedIndex : Nat) (preservedNeScaled : preservedIndex ≠ scaledIndex)
      (preservedValue : UInt32)
      (preservedLocal : initial.get preservedIndex = some (.i32 preservedValue))
      (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get preservedIndex =
        some (.i32 preservedValue) := by
    calc
      _ = afterThird.get preservedIndex := rfl
      _ = ({ afterSecond with values := .i32 (checkedScale8Word index) :: tail } :
          Wasm.Locals).get preservedIndex := thirdUpdate.2 preservedNeScaled
      _ = afterSecond.get preservedIndex := rfl
      _ = ({ afterFirst with values :=
          (.i32 (index + index + (index + index)) :: tail) } :
          Wasm.Locals).get preservedIndex := secondUpdate.2 preservedNeScaled
      _ = afterFirst.get preservedIndex := rfl
      _ = ({ initial with values := .i32 (index + index) :: tail } :
          Wasm.Locals).get preservedIndex := firstUpdate.2 preservedNeScaled
      _ = initial.get preservedIndex := rfl
      _ = some (.i32 preservedValue) := preservedLocal
  have objectAfterThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get objectIndex =
        some (.i32 object) :=
    preservedAfterThird objectIndex objectNeScaled object objectLocal values
  have valueAfterThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get valueIndex =
        some (.i32 value) :=
    preservedAfterThird valueIndex valueNeScaled value valueLocal values
  have scaledAfterThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get scaledIndex =
        some (.i32 (checkedScale8Word index)) := by
    simpa using thirdUpdate.1
  unfold checkedLocalLimbPartProgram
  rw [List.append_assoc]
  apply wp_checkedScale8Program indexLocal firstSet secondSet thirdSet
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectAfterThird, Wasm.wp_const_cons, Wasm.wp_add_cons,
    scaledAfterThird, valueAfterThird, Wasm.wp_store32_cons]
  change (if (checkedLimbBase object index).toNat +
      (UInt32.ofNat offset).toNat + 4 >
      store.mem.pages * 65536 then
        Q (.Trap store "out of bounds memory access")
      else
        Wasm.wp module rest Q
          { store with mem := (store.mem.write32
              (checkedLimbBase object index + UInt32.ofNat offset) value) }
          { afterThird with values := tail } env)
  rw [if_neg writeInBounds]
  exact continued

/-- Explicit local frame at the two payload stores in `writeSumFrom`. -/
def writeSumArithmeticLocals
    (left leftFlavor right rightFlavor result index count carry : UInt32)
    (leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32)
    (values : List Wasm.Value) : Wasm.Locals := {
  params := [.i32 left, .i32 leftFlavor, .i32 right, .i32 rightFlavor,
    .i32 result, .i32 index, .i32 count, .i32 carry]
  locals := [.i32 leftLow, .i32 leftHigh, .i32 rightLow, .i32 rightHigh,
    .i32 low, .i32 high, .i32 carryLocal, .i32 carryExtra, .i32 scaled]
  values := values }

/-- Arithmetic suffix of `sumStep` in `writeSumFrom`'s shifted local layout. -/
def writeSumArithmeticProgram : Wasm.Program := [
  .localGet 8, .localGet 10, .add, .localSet 12,
  .localGet 12, .localGet 8, .ltU, .localSet 14,
  .localGet 12, .localGet 7, .add, .localSet 12,
  .localGet 12, .localGet 7, .ltU, .localSet 15,
  .localGet 14, .localGet 15, .add, .localSet 14,
  .localGet 9, .localGet 11, .add, .localSet 13,
  .localGet 13, .localGet 9, .ltU, .localSet 15,
  .localGet 13, .localGet 14, .add, .localSet 13,
  .localGet 13, .localGet 14, .ltU, .localSet 14,
  .localGet 14, .localGet 15, .add, .localSet 14]

/-- Four magnitude calls plus arithmetic in `writeSumFrom`'s shifted frame. -/
def writeSumStepProgram (magnitudeLowIndex magnitudeHighIndex : Nat) :
    Wasm.Program := [
  .localGet 0, .localGet 1, .localGet 5,
  .call magnitudeLowIndex, .localSet 8,
  .localGet 0, .localGet 1, .localGet 5,
  .call magnitudeHighIndex, .localSet 9,
  .localGet 2, .localGet 3, .localGet 5,
  .call magnitudeLowIndex, .localSet 10,
  .localGet 2, .localGet 3, .localGet 5,
  .call magnitudeHighIndex, .localSet 11] ++
  writeSumArithmeticProgram

/-- The private shared `sumStep` adapts to its shifted numeric layout inside
W7's `writeSumFromFunction`. -/
theorem instructions_writeSumStepSource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction labels
      (sumCarryStepSource
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[2]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[3]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[2]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[3]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[4]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[5]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[6]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[7]!.1) =
      .ok (writeSumStepProgram magnitudeLowIndex magnitudeHighIndex) := by
  have leftFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[0]!.1 =
        some 0 := by decide
  have leftFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[1]!.1 =
        some 1 := by decide
  have rightFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[2]!.1 =
        some 2 := by decide
  have rightFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[3]!.1 =
        some 3 := by decide
  have indexFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1 =
        some 5 := by decide
  have carryFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1 =
        some 7 := by decide
  have leftLowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[0]!.1 =
        some 8 := by decide
  have leftHighFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[1]!.1 =
        some 9 := by decide
  have rightLowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[2]!.1 =
        some 10 := by decide
  have rightHighFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[3]!.1 =
        some 11 := by decide
  have lowFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[4]!.1 =
        some 12 := by decide
  have highFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[5]!.1 =
        some 13 := by decide
  have carryLocalFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[6]!.1 =
        some 14 := by decide
  have carryExtraFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[7]!.1 =
        some 15 := by decide
  set_option maxRecDepth 100000 in
    simp [sumCarryStepSource, writeSumStepProgram,
      writeSumArithmeticProgram, FirTalos.instructions, FirTalos.instruction,
      leftFound, leftFlavorFound, rightFound, rightFlavorFound, indexFound,
      carryFound, leftLowFound, leftHighFound, rightLowFound, rightHighFound,
      lowFound, highFound, carryLocalFound, carryExtraFound,
      magnitudeLowFound, magnitudeHighFound, Bind.bind, Except.bind, pure,
      Except.pure]

/-- Direct execution of the shifted arithmetic suffix realizes the same
emitted operand-order model as the carry-only scan. -/
theorem wp_writeSumArithmeticProgram_emitted
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor result index count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (continued : Wasm.wp module rest Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry leftLow leftHigh rightLow rightHigh
        (emittedLimbSumLow leftLow rightLow carry)
        (emittedLimbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (emittedLimbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        scaled tail) env) :
    Wasm.wp module (writeSumArithmeticProgram ++ rest) Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry leftLow leftHigh rightLow rightHigh low high carryLocal
        carryExtra scaled tail) env := by
  simp [writeSumArithmeticProgram, writeSumArithmeticLocals]
  exact continued

/-- The emitted-order equalities convert the shifted arithmetic suffix to the
canonical pure base-`2^64` limb operation. -/
theorem wp_writeSumArithmeticProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor result index count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (continued : Wasm.wp module rest Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry leftLow leftHigh rightLow rightHigh
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        scaled tail) env) :
    Wasm.wp module (writeSumArithmeticProgram ++ rest) Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry leftLow leftHigh rightLow rightHigh low high carryLocal
        carryExtra scaled tail) env := by
  apply wp_writeSumArithmeticProgram_emitted
  simpa using continued

/-- One complete shifted `sumStep` performs the same four read-only magnitude
calls and pure limb recurrence as the installed carry-only scan. -/
theorem wp_writeSumStepProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor result index count carry : UInt32}
    {oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high carryLocal
      carryExtra scaled : UInt32}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (leftLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftLow :: tail))
    (leftHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftHigh :: tail))
    (rightLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightLow :: tail))
    (rightHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightHigh :: tail))
    (continued : Wasm.wp module rest Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry leftLow leftHigh rightLow rightHigh
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        scaled tail) env) :
    Wasm.wp module
      (writeSumStepProgram magnitudeLowIndex magnitudeHighIndex ++ rest) Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled tail) env := by
  rw [writeSumStepProgram, List.append_assoc]
  simp [writeSumArithmeticLocals]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 index, .i32 leftFlavor, .i32 left])
      (tail := tail)
      (locals := writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry oldLeftLow oldLeftHigh oldRightLow oldRightHigh
        low high carryLocal carryExtra scaled (.i32 leftLow :: tail))
      (updated := writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry leftLow oldLeftHigh oldRightLow oldRightHigh
        low high carryLocal carryExtra scaled (.i32 leftLow :: tail))
      (physicalResult := .i32 leftLow)
      (callRun := leftLowRun) (targetSet := by rfl)
  simp [writeSumArithmeticLocals]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 index, .i32 leftFlavor, .i32 left])
      (tail := tail)
      (locals := writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry leftLow oldLeftHigh oldRightLow oldRightHigh
        low high carryLocal carryExtra scaled (.i32 leftHigh :: tail))
      (updated := writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry leftLow leftHigh oldRightLow oldRightHigh
        low high carryLocal carryExtra scaled (.i32 leftHigh :: tail))
      (physicalResult := .i32 leftHigh)
      (callRun := leftHighRun) (targetSet := by rfl)
  simp [writeSumArithmeticLocals]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 index, .i32 rightFlavor, .i32 right])
      (tail := tail)
      (locals := writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry leftLow leftHigh oldRightLow oldRightHigh
        low high carryLocal carryExtra scaled (.i32 rightLow :: tail))
      (updated := writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry leftLow leftHigh rightLow oldRightHigh
        low high carryLocal carryExtra scaled (.i32 rightLow :: tail))
      (physicalResult := .i32 rightLow)
      (callRun := rightLowRun) (targetSet := by rfl)
  simp [writeSumArithmeticLocals]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 index, .i32 rightFlavor, .i32 right])
      (tail := tail)
      (locals := writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry leftLow leftHigh rightLow oldRightHigh
        low high carryLocal carryExtra scaled (.i32 rightHigh :: tail))
      (updated := writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry leftLow leftHigh rightLow rightHigh
        low high carryLocal carryExtra scaled (.i32 rightHigh :: tail))
      (physicalResult := .i32 rightHigh)
      (callRun := rightHighRun) (targetSet := by rfl)
  exact wp_writeSumArithmeticProgram continued

/-- Exact pair of locally sourced stores in one `writeSumFrom` iteration. -/
def writeSumLimbStoresProgram : Wasm.Program :=
  checkedLocalLimbPartProgram 4 5 16 12 0 ++
    checkedLocalLimbPartProgram 4 5 16 13 4

/-- Public proof-side spelling of the two private dynamic stores embedded in
W7's `writeSumFromFunction`. -/
def writeSumLimbStoresSource : List Fir.Wasm.Instruction :=
  checkedLocalLimbPartSource
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[4]!.1
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[8]!.1
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[4]!.1 0 ++
    checkedLocalLimbPartSource
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[4]!.1
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[8]!.1
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[5]!.1 4

/-- Exact adaptation of the two private `writeSumFrom` payload stores. -/
theorem instructions_writeSumLimbStoresSource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction labels
      writeSumLimbStoresSource = .ok writeSumLimbStoresProgram := by
  unfold writeSumLimbStoresSource writeSumLimbStoresProgram
  rw [FirTalos.Correctness.instructions_append]
  rw [instructions_checkedLocalLimbPartSource
    (objectIndex := 4) (indexIndex := 5) (scaledIndex := 16)
    (valueIndex := 12) (offset := 0)
    (objectFound := by decide) (indexFound := by decide)
    (scaledFound := by decide) (valueFound := by decide)]
  rw [instructions_checkedLocalLimbPartSource
    (objectIndex := 4) (indexIndex := 5) (scaledIndex := 16)
    (valueIndex := 13) (offset := 4)
    (objectFound := by decide) (indexFound := by decide)
    (scaledFound := by decide) (valueFound := by decide)]
  rfl

/-- Exact successor store after writing one generated low word. -/
def writeSumLowStore
    (store : Wasm.Store host) (result index low : UInt32) :
    Wasm.Store host :=
  { store with mem := (store.mem.write32
      (checkedLimbBase result index + UInt32.ofNat 0) low) }

/-- Exact successor store after writing both generated words of one limb. -/
def writeSumFinalStore
    (store : Wasm.Store host) (result index low high : UInt32) :
    Wasm.Store host :=
  let lowStore := writeSumLowStore store result index low
  { lowStore with mem := (lowStore.mem.write32
      (checkedLimbBase result index + UInt32.ofNat 4) high) }

/-- The two emitted dynamic stores write exactly the generated low/high words
and otherwise preserve the store and complete arithmetic local frame. -/
theorem wp_writeSumLimbStoresProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor result index count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (lowInBounds :
      ¬(checkedLimbBase result index).toNat + 4 >
        store.mem.pages * 65536)
    (highInBounds :
      ¬(checkedLimbBase result index).toNat + 4 + 4 >
        store.mem.pages * 65536)
    (continued :
      Wasm.wp module rest Q
        (writeSumFinalStore store result index low high)
        (writeSumArithmeticLocals left leftFlavor right rightFlavor result
          index count carry leftLow leftHigh rightLow rightHigh low high
          carryLocal carryExtra (checkedScale8Word index) tail) env) :
    Wasm.wp module (writeSumLimbStoresProgram ++ rest) Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry leftLow leftHigh rightLow rightHigh low high carryLocal
        carryExtra scaled tail) env := by
  unfold writeSumLimbStoresProgram
  rw [List.append_assoc]
  apply wp_checkedLocalLimbPartProgram
    (initial := writeSumArithmeticLocals left leftFlavor right rightFlavor
      result index count carry leftLow leftHigh rightLow rightHigh low high
      carryLocal carryExtra scaled tail)
    (afterFirst := writeSumArithmeticLocals left leftFlavor right rightFlavor
      result index count carry leftLow leftHigh rightLow rightHigh low high
      carryLocal carryExtra (index + index) (.i32 (index + index) :: tail))
    (afterSecond := writeSumArithmeticLocals left leftFlavor right rightFlavor
      result index count carry leftLow leftHigh rightLow rightHigh low high
      carryLocal carryExtra (index + index + (index + index))
        (.i32 (index + index + (index + index)) :: tail))
    (afterThird := writeSumArithmeticLocals left leftFlavor right rightFlavor
      result index count carry leftLow leftHigh rightLow rightHigh low high
      carryLocal carryExtra (checkedScale8Word index)
        (.i32 (checkedScale8Word index) :: tail))
    (by decide) (by decide) (by rfl) (by rfl) (by rfl)
    (by simp [writeSumArithmeticLocals, Wasm.Locals.set?])
    (by simp [writeSumArithmeticLocals, Wasm.Locals.set?])
    (by simp [writeSumArithmeticLocals, Wasm.Locals.set?]) lowInBounds
  apply wp_checkedLocalLimbPartProgram
    (initial := writeSumArithmeticLocals left leftFlavor right rightFlavor
      result index count carry leftLow leftHigh rightLow rightHigh low high
      carryLocal carryExtra (checkedScale8Word index) tail)
    (afterFirst := writeSumArithmeticLocals left leftFlavor right rightFlavor
      result index count carry leftLow leftHigh rightLow rightHigh low high
      carryLocal carryExtra (index + index) (.i32 (index + index) :: tail))
    (afterSecond := writeSumArithmeticLocals left leftFlavor right rightFlavor
      result index count carry leftLow leftHigh rightLow rightHigh low high
      carryLocal carryExtra (index + index + (index + index))
        (.i32 (index + index + (index + index)) :: tail))
    (afterThird := writeSumArithmeticLocals left leftFlavor right rightFlavor
      result index count carry leftLow leftHigh rightLow rightHigh low high
      carryLocal carryExtra (checkedScale8Word index)
        (.i32 (checkedScale8Word index) :: tail))
    (by decide) (by decide) (by rfl) (by rfl) (by rfl)
    (by simp [writeSumArithmeticLocals, Wasm.Locals.set?])
    (by simp [writeSumArithmeticLocals, Wasm.Locals.set?])
    (by simp [writeSumArithmeticLocals, Wasm.Locals.set?])
  · simpa [writeSumLowStore, Wasm.Mem.write32] using highInBounds
  · simpa [writeSumFinalStore, writeSumLowStore,
      writeSumArithmeticLocals] using continued

/-- One complete nonterminal writer iteration before its carry/index
back-edge: read both operand limbs, compute their sum, and store its two words. -/
def writeSumStepAndStoresProgram
    (magnitudeLowIndex magnitudeHighIndex : Nat) : Wasm.Program :=
  writeSumStepProgram magnitudeLowIndex magnitudeHighIndex ++
    writeSumLimbStoresProgram

/-- The complete data-producing prefix of one writer iteration computes the
pure limb recurrence and materializes its low/high words at the selected
payload coordinate. -/
theorem wp_writeSumStepAndStoresProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor result index count carry : UInt32}
    {oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high carryLocal
      carryExtra scaled : UInt32}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (leftLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftLow :: tail))
    (leftHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftHigh :: tail))
    (rightLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightLow :: tail))
    (rightHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightHigh :: tail))
    (lowInBounds :
      ¬(checkedLimbBase result index).toNat + 4 >
        store.mem.pages * 65536)
    (highInBounds :
      ¬(checkedLimbBase result index).toNat + 4 + 4 >
        store.mem.pages * 65536)
    (continued : Wasm.wp module rest Q
      (writeSumFinalStore store result index
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry))
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry leftLow leftHigh rightLow rightHigh
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        (checkedScale8Word index) tail) env) :
    Wasm.wp module
      (writeSumStepAndStoresProgram magnitudeLowIndex magnitudeHighIndex ++
        rest) Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled tail) env := by
  unfold writeSumStepAndStoresProgram
  rw [List.append_assoc]
  apply wp_writeSumStepProgram leftLowRun leftHighRun rightLowRun rightHighRun
  exact wp_writeSumLimbStoresProgram lowInBounds highInBounds continued

/-! ### Installed natural writer loop -/

/-- Carry/index back-edge of `writeSumFrom` in its shifted local layout. -/
def writeSumContinueProgram : Wasm.Program := [
  .localGet 14, .localSet 7,
  .localGet 5, .const 1, .add, .localSet 5,
  .br 0]

/-- Exact control effect of the writer back-edge. -/
theorem wp_writeSumContinueProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor result index count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high nextCarry carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value}
    (continued : Q (.Break 0 store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result
        (sumCarryNextIndex index) count nextCarry leftLow leftHigh rightLow
        rightHigh low high nextCarry carryExtra scaled tail))) :
    Wasm.wp module writeSumContinueProgram Q store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry leftLow leftHigh rightLow rightHigh low high nextCarry
        carryExtra scaled tail) env := by
  simpa [writeSumContinueProgram, writeSumArithmeticLocals,
    sumCarryNextIndex] using continued

/-- Fixed Talos body of the installed natural writer. -/
def writeSumLoopBody (magnitudeLowIndex magnitudeHighIndex : Nat) :
    Wasm.Program := [
  .localGet 5, .localGet 6, .eq,
  .iff 0 0 [.localGet 7, .ret] []] ++
  writeSumStepAndStoresProgram magnitudeLowIndex magnitudeHighIndex ++
  writeSumContinueProgram

/-- Fixed Talos loop installed by W7's `writeSumFromFunction`. -/
def writeSumLoopProgram (magnitudeLowIndex magnitudeHighIndex : Nat) :
    Wasm.Program := [
  .loop 0 0 (writeSumLoopBody magnitudeLowIndex magnitudeHighIndex)]

/-- At the terminal index, the writer returns its current carry without
reading operands or mutating the result payload. -/
theorem wp_writeSumLoopBody_exit
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor result count carry : UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value}
    (completed : Q (.Return store (.i32 carry :: tail))) :
    Wasm.wp module (writeSumLoopBody magnitudeLowIndex magnitudeHighIndex) Q
      store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result count
        count carry leftLow leftHigh rightLow rightHigh low high carryLocal
        carryExtra scaled tail) env := by
  unfold writeSumLoopBody
  simp [writeSumArithmeticLocals]
  apply Wasm.wp_iff_cons rfl
  simpa [writeSumArithmeticLocals] using completed

/-- A nonterminal writer body executes one exact arithmetic-and-store step,
then installs the generated carry and branches back to the loop header. -/
theorem wp_writeSumLoopBody_continue
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {left leftFlavor right rightFlavor result index count carry : UInt32}
    {oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high carryLocal
      carryExtra scaled : UInt32}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {tail : List Wasm.Value}
    (notDone : index ≠ count)
    (leftLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftLow :: tail))
    (leftHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 leftHigh :: tail))
    (rightLowRun : Wasm.TerminatesWith env module magnitudeLowIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightLow :: tail))
    (rightHighRun : Wasm.TerminatesWith env module magnitudeHighIndex store
      ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 rightHigh :: tail))
    (lowInBounds :
      ¬(checkedLimbBase result index).toNat + 4 >
        store.mem.pages * 65536)
    (highInBounds :
      ¬(checkedLimbBase result index).toNat + 4 + 4 >
        store.mem.pages * 65536)
    (continued : Q (.Break 0
      (writeSumFinalStore store result index
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry))
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result
        (sumCarryNextIndex index) count
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        leftLow leftHigh rightLow rightHigh
        (limbSumLow leftLow rightLow carry)
        (limbSumHigh leftLow leftHigh rightLow rightHigh carry)
        (limbSumCarryOut leftLow leftHigh rightLow rightHigh carry)
        (if rightHigh + leftHigh < leftHigh then 1 else 0)
        (checkedScale8Word index) tail))) :
    Wasm.wp module (writeSumLoopBody magnitudeLowIndex magnitudeHighIndex) Q
      store
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result index
        count carry oldLeftLow oldLeftHigh oldRightLow oldRightHigh low high
        carryLocal carryExtra scaled tail) env := by
  unfold writeSumLoopBody
  simp [writeSumArithmeticLocals, notDone]
  apply Wasm.wp_iff_cons rfl
  simp
  apply wp_writeSumStepAndStoresProgram leftLowRun leftHighRun rightLowRun
    rightHighRun lowInBounds highInBounds
  apply wp_writeSumContinueProgram
  exact continued

/-- Machine-frame lifting of a semantic writer invariant indexed by the
current absolute limb, carry, and evolving store. -/
def writeSumLoopInvariant
    (left leftFlavor right rightFlavor result count : UInt32)
    (tail : List Wasm.Value)
    (Inv : UInt32 → UInt32 → Wasm.Store host → Prop) :
    Wasm.AssertionF host :=
  fun current locals =>
    ∃ index carry leftLow leftHigh rightLow rightHigh low high carryLocal
        carryExtra scaled,
      locals = writeSumArithmeticLocals left leftFlavor right rightFlavor
        result index count carry leftLow leftHigh rightLow rightHigh low high
        carryLocal carryExtra scaled tail ∧
      Inv index carry current

/-- Variant read from the writer's shifted absolute-index parameter. -/
def writeSumLoopMeasure (count : UInt32) :
    Wasm.Store host → Wasm.Locals → Nat :=
  fun _ locals =>
    match locals.get 5 with
    | some (.i32 index) => count.toNat - index.toNat
    | _ => 0

/-- Generic total-correctness rule for the installed natural writer.

The semantic invariant owns the growing payload-memory frame and may depend on
the evolving store. Talos control contributes only the independent
`count - index` variant. No allocation predicate, fuel, or execution
certificate is baked into this reusable loop boundary. -/
theorem wp_writeSumLoopProgram_of_invariant
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {initialStore : Wasm.Store host}
    {left leftFlavor right rightFlavor result count initialIndex initialCarry :
      UInt32}
    {leftLow leftHigh rightLow rightHigh low high carryLocal carryExtra
      scaled : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    {Inv : UInt32 → UInt32 → Wasm.Store host → Prop}
    (initialInv : Inv initialIndex initialCarry initialStore)
    (bounded : ∀ index carry current, Inv index carry current →
      index.toNat ≤ count.toNat)
    (atEnd : ∀ carry current, Inv count carry current →
      Q (.Return current (.i32 carry :: tail)))
    (step : ∀ index carry current, Inv index carry current →
      index.toNat < count.toNat →
      ∃ stepLeftLow stepLeftHigh stepRightLow stepRightHigh,
        Wasm.TerminatesWith env module magnitudeLowIndex current
          ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
          (fun final values =>
            final = current ∧ values = .i32 stepLeftLow :: tail) ∧
        Wasm.TerminatesWith env module magnitudeHighIndex current
          ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
          (fun final values =>
            final = current ∧ values = .i32 stepLeftHigh :: tail) ∧
        Wasm.TerminatesWith env module magnitudeLowIndex current
          ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
          (fun final values =>
            final = current ∧ values = .i32 stepRightLow :: tail) ∧
        Wasm.TerminatesWith env module magnitudeHighIndex current
          ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
          (fun final values =>
            final = current ∧ values = .i32 stepRightHigh :: tail) ∧
        ¬(checkedLimbBase result index).toNat + 4 >
          current.mem.pages * 65536 ∧
        ¬(checkedLimbBase result index).toNat + 4 + 4 >
          current.mem.pages * 65536 ∧
        Inv (sumCarryNextIndex index)
          (limbSumCarryOut stepLeftLow stepLeftHigh stepRightLow
            stepRightHigh carry)
          (writeSumFinalStore current result index
            (limbSumLow stepLeftLow stepRightLow carry)
            (limbSumHigh stepLeftLow stepLeftHigh stepRightLow stepRightHigh
              carry))) :
    Wasm.wp module
      (writeSumLoopProgram magnitudeLowIndex magnitudeHighIndex ++ rest) Q
      initialStore
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result
        initialIndex count initialCarry leftLow leftHigh rightLow rightHigh low
        high carryLocal carryExtra scaled tail) env := by
  unfold writeSumLoopProgram
  apply Wasm.wp_loop_cons
    (Inv := writeSumLoopInvariant left leftFlavor right rightFlavor result
      count tail Inv)
    (μ := writeSumLoopMeasure count)
  · exact ⟨initialIndex, initialCarry, leftLow, leftHigh, rightLow,
      rightHigh, low, high, carryLocal, carryExtra, scaled, rfl, initialInv⟩
  · rintro current locals
      ⟨index, carry, oldLeftLow, oldLeftHigh, oldRightLow, oldRightHigh,
        oldLow, oldHigh, oldCarryLocal, oldCarryExtra, oldScaled, rfl,
        invariant⟩
    by_cases done : index = count
    · subst index
      exact wp_writeSumLoopBody_exit (atEnd carry current invariant)
    · have beforeCount : index.toNat < count.toNat := by
        have indexBound := bounded index carry current invariant
        have differentNat : index.toNat ≠ count.toNat := by
          intro same
          exact done (UInt32.toNat.inj same)
        omega
      obtain ⟨stepLeftLow, stepLeftHigh, stepRightLow, stepRightHigh,
        leftLowRun, leftHighRun, rightLowRun, rightHighRun, lowInBounds,
        highInBounds, nextInvariant⟩ :=
        step index carry current invariant beforeCount
      apply wp_writeSumLoopBody_continue done leftLowRun leftHighRun
        rightLowRun rightHighRun lowInBounds highInBounds
      refine ⟨?_, ?_⟩
      · exact ⟨sumCarryNextIndex index,
          limbSumCarryOut stepLeftLow stepLeftHigh stepRightLow stepRightHigh
            carry,
          stepLeftLow, stepLeftHigh, stepRightLow, stepRightHigh,
          limbSumLow stepLeftLow stepRightLow carry,
          limbSumHigh stepLeftLow stepLeftHigh stepRightLow stepRightHigh carry,
          limbSumCarryOut stepLeftLow stepLeftHigh stepRightLow stepRightHigh
            carry,
          (if stepRightHigh + stepLeftHigh < stepLeftHigh then 1 else 0),
          checkedScale8Word index, rfl, nextInvariant⟩
      · simp [writeSumLoopMeasure, writeSumArithmeticLocals,
          sumCarryNextIndex_toNat beforeCount]
        omega

/-- W7's private writer loop is exactly the public proof-side assembly of its
guard, shifted arithmetic step, two payload stores, and back-edge. -/
theorem writeSumFromFunction_loop_shape :
    ∃ loopLabel,
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.body = [
        .loop loopLabel <|
          sumCarryGuardSource
              Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[6]!.1
              Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1 ++
          sumCarryStepSource
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[2]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[3]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[2]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[3]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[4]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[5]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[6]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[7]!.1 ++
          writeSumLimbStoresSource ++
          sumCarryContinueSource
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[6]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
            loopLabel] := by
  let loopLabel : Lean.FVarId :=
    match Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.body with
    | [.loop label _] => label
    | _ => ⟨`invalidWriteSumLoop⟩
  refine ⟨loopLabel, ?_⟩
  rfl

/-- Exact adaptation of the writer's terminal guard. -/
theorem instructions_writeSumGuardSource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction labels
      (sumCarryGuardSource
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[6]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1) =
      .ok [
        .localGet 5, .localGet 6, .eq,
        .iff 0 0 [.localGet 7, .ret] []] := by
  have indexFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1 =
        some 5 := by decide
  have countFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[6]!.1 =
        some 6 := by decide
  have carryFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1 =
        some 7 := by decide
  simp [sumCarryGuardSource, FirTalos.instructions, FirTalos.instruction,
    indexFound, countFound, carryFound, Bind.bind, Except.bind, pure,
    Except.pure]

/-- Exact adaptation of the writer's carry/index back-edge. -/
theorem instructions_writeSumContinueSource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId}
    {loopLabel : Lean.FVarId} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction
      (loopLabel :: labels)
      (sumCarryContinueSource
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[6]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
        loopLabel) = .ok writeSumContinueProgram := by
  have carryLocalFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[6]!.1 =
        some 14 := by decide
  have carryFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1 =
        some 7 := by decide
  have indexFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1 =
        some 5 := by decide
  simp [sumCarryContinueSource, writeSumContinueProgram,
    FirTalos.instructions, FirTalos.instruction, FirTalos.findLabel?,
    carryLocalFound, carryFound, indexFound, Bind.bind, Except.bind, pure,
    Except.pure]

/-- Exact adaptation of the complete private writer loop body. -/
theorem instructions_writeSumLoopBodySource
    {sourceModule : Fir.Wasm.Module} {labels : List Lean.FVarId}
    {loopLabel : Lean.FVarId} {magnitudeLowIndex magnitudeHighIndex : Nat}
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction
      (loopLabel :: labels)
      (sumCarryGuardSource
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[6]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1 ++
        sumCarryStepSource
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[1]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[2]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[3]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[1]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[2]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[3]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[4]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[5]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[6]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[7]!.1 ++
        writeSumLimbStoresSource ++
        sumCarryContinueSource
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals[6]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[7]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.params[5]!.1
          loopLabel) =
      .ok (writeSumLoopBody magnitudeLowIndex magnitudeHighIndex) := by
  rw [FirTalos.Correctness.instructions_append,
    FirTalos.Correctness.instructions_append,
    FirTalos.Correctness.instructions_append]
  rw [instructions_writeSumGuardSource,
    instructions_writeSumStepSource magnitudeLowFound magnitudeHighFound,
    instructions_writeSumLimbStoresSource,
    instructions_writeSumContinueSource]
  rfl

/-- W7's complete symbolic `writeSumFrom` body adapts to the fixed writer loop
consumed by the store-indexed invariant theorem. -/
theorem instructions_writeSumFromFunction
    {sourceModule : Fir.Wasm.Module}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction []
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.body =
        .ok (writeSumLoopProgram magnitudeLowIndex magnitudeHighIndex) := by
  obtain ⟨loopLabel, shape⟩ := writeSumFromFunction_loop_shape
  rw [shape]
  simp only [FirTalos.instructions, FirTalos.instruction]
  rw [instructions_writeSumLoopBodySource magnitudeLowFound
    magnitudeHighFound]
  rfl

/-- Canonical Talos function shape of the complete BigNumeric limb writer. -/
def writeSumTargetFunction (magnitudeLowIndex magnitudeHighIndex : Nat)
    (suffix : Wasm.Program := []) : Wasm.Function := {
  params := [.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32]
  locals := [.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32]
  results := [.i32]
  body := writeSumLoopProgram magnitudeLowIndex magnitudeHighIndex ++ suffix }

/-- Successful adaptation produces the complete canonical writer function,
including its parameter, local, result, and terminal-suffix conventions. -/
theorem adaptedWriteSumFromFunction_eq
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction =
        .ok targetFunction)
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    targetFunction = writeSumTargetFunction magnitudeLowIndex magnitudeHighIndex
      (FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction) := by
  unfold FirTalos.function at adapted
  rw [instructions_writeSumFromFunction magnitudeLowFound magnitudeHighFound]
    at adapted
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at adapted
  have localsEq :
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction.locals.toList.map
        (fun entry => FirTalos.abiKind entry.snd) =
          [.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32] := by
    rfl
  rw [localsEq] at adapted
  simpa [writeSumTargetFunction,
    Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction, FirTalos.abiKind,
    Fir.Wasm.AbiKind.valueType, FirTalos.valueType] using adapted.symm

/-- Successful function adaptation installs precisely the proved writer loop
followed by the adapter's unreachable terminal suffix. -/
theorem adaptedWriteSumFromFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction =
        .ok targetFunction)
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex) :
    targetFunction.body =
      writeSumLoopProgram magnitudeLowIndex magnitudeHighIndex ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction := by
  rw [adaptedWriteSumFromFunction_eq adapted magnitudeLowFound
    magnitudeHighFound]
  rfl

/-- Complete writer-loop theorem over equally sized machine limb views and an
abstract growing-memory frame.

`Frame n store` describes the first `n` result limbs already materialized in
`store`. The only memory-specific obligation is that one exact low/high store
pair extends this frame. This keeps object allocation and canonical-Nat
validity outside the structured-loop proof. -/
theorem wp_writeSumLoopProgram_of_limbWordsAndFrame
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {initialStore : Wasm.Store host}
    {left leftFlavor right rightFlavor result count initialCarry : UInt32}
    {initialLeftLow initialLeftHigh initialRightLow initialRightHigh low high
      carryLocal carryExtra scaled : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    {leftWords rightWords : List LimbWords}
    {Frame : Nat → Wasm.Store host → Prop}
    (leftLength : leftWords.length = count.toNat)
    (rightLength : rightWords.length = count.toNat)
    (initialFrame : Frame 0 initialStore)
    (leftLowRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      Frame index.toNat current →
      Wasm.TerminatesWith env module magnitudeLowIndex current
        ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
        (fun final values =>
          final = current ∧
            values = .i32 (leftWords[index.toNat]'(by omega)).1 :: tail))
    (leftHighRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      Frame index.toNat current →
      Wasm.TerminatesWith env module magnitudeHighIndex current
        ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
        (fun final values =>
          final = current ∧
            values = .i32 (leftWords[index.toNat]'(by omega)).2 :: tail))
    (rightLowRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      Frame index.toNat current →
      Wasm.TerminatesWith env module magnitudeLowIndex current
        ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
        (fun final values =>
          final = current ∧
            values = .i32 (rightWords[index.toNat]'(by omega)).1 :: tail))
    (rightHighRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      Frame index.toNat current →
      Wasm.TerminatesWith env module magnitudeHighIndex current
        ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
        (fun final values =>
          final = current ∧
            values = .i32 (rightWords[index.toNat]'(by omega)).2 :: tail))
    (writeFrame : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat) (writtenLow writtenHigh : UInt32),
      Frame index.toNat current →
      ¬(checkedLimbBase result index).toNat + 4 >
          current.mem.pages * 65536 ∧
        ¬(checkedLimbBase result index).toNat + 4 + 4 >
          current.mem.pages * 65536 ∧
        Frame (index.toNat + 1)
          (writeSumFinalStore current result index writtenLow writtenHigh))
    (completed : ∀ finalStore,
      Frame count.toNat finalStore →
      Q (.Return finalStore
        (.i32 (addLimbWords leftWords rightWords initialCarry).2 :: tail))) :
    Wasm.wp module
      (writeSumLoopProgram magnitudeLowIndex magnitudeHighIndex ++ rest) Q
      initialStore
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result 0
        count initialCarry initialLeftLow initialLeftHigh initialRightLow
        initialRightHigh low high carryLocal carryExtra scaled tail) env := by
  let expectedCarry := (addLimbWords leftWords rightWords initialCarry).2
  let Inv : UInt32 → UInt32 → Wasm.Store host → Prop :=
    fun index carry current =>
      index.toNat ≤ count.toNat ∧
      (addLimbWords (leftWords.drop index.toNat)
        (rightWords.drop index.toNat) carry).2 = expectedCarry ∧
      Frame index.toNat current
  apply wp_writeSumLoopProgram_of_invariant
    (Inv := Inv)
  · exact ⟨by simp, by simp [expectedCarry], initialFrame⟩
  · intro index carry current invariant
    exact invariant.1
  · intro carry current invariant
    have leftDrop : leftWords.drop count.toNat = [] := by
      rw [← leftLength]
      simp
    have rightDrop : rightWords.drop count.toNat = [] := by
      rw [← rightLength]
      simp
    have carryEq : carry = expectedCarry := by
      simpa [Inv, leftDrop, rightDrop, addLimbWords] using invariant.2.1
    rw [carryEq]
    simpa [expectedCarry] using completed current invariant.2.2
  · intro index carry current invariant beforeCount
    let leftLimb : LimbWords := leftWords[index.toNat]'(by omega)
    let rightLimb : LimbWords := rightWords[index.toNat]'(by omega)
    have leftLowRun' := leftLowRun index current beforeCount invariant.2.2
    have leftHighRun' := leftHighRun index current beforeCount invariant.2.2
    have rightLowRun' := rightLowRun index current beforeCount invariant.2.2
    have rightHighRun' := rightHighRun index current beforeCount invariant.2.2
    obtain ⟨lowInBounds, highInBounds, nextFrame⟩ :=
      writeFrame index current beforeCount
        (limbSumLow leftLimb.1 rightLimb.1 carry)
        (limbSumHigh leftLimb.1 leftLimb.2 rightLimb.1 rightLimb.2 carry)
        invariant.2.2
    refine ⟨leftLimb.1, leftLimb.2, rightLimb.1, rightLimb.2,
      leftLowRun', leftHighRun', rightLowRun', rightHighRun', lowInBounds,
      highInBounds, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [sumCarryNextIndex_toNat beforeCount]
      omega
    · have leftDrop := List.drop_eq_getElem_cons
          (l := leftWords) (i := index.toNat) (by omega)
      have rightDrop := List.drop_eq_getElem_cons
          (l := rightWords) (i := index.toNat) (by omega)
      have carryResult := invariant.2.1
      rw [leftDrop, rightDrop] at carryResult
      simp only [addLimbWords] at carryResult
      rw [sumCarryNextIndex_toNat beforeCount]
      simpa [Inv, leftLimb, rightLimb] using carryResult
    · rw [sumCarryNextIndex_toNat beforeCount]
      exact nextFrame

/-- Exact materialization history for the first `n` limbs of a result payload.

The relation deliberately records the generated Talos stores, rather than
assuming a decoder theorem up front.  Its later memory projection therefore
has a small, explicit obligation: later, disjoint limb stores preserve every
earlier low/high word. -/
inductive WrittenLimbPrefix
    (initial : Wasm.Store host) (result : UInt32) (words : List LimbWords) :
    Nat → Wasm.Store host → Prop where
  | zero : WrittenLimbPrefix initial result words 0 initial
  | step {index : Nat} {current : Wasm.Store host} {low high : UInt32}
      (written : WrittenLimbPrefix initial result words index current)
      (wordAt : words[index]? = some (low, high)) :
      WrittenLimbPrefix initial result words (index + 1)
        (writeSumFinalStore current result (UInt32.ofNat index) low high)

/-- Extend an exact written prefix at a wasm32 index without leaking an
`ofNat` round trip into the loop invariant. -/
theorem WrittenLimbPrefix.next
    {initial current : Wasm.Store host} {result index low high : UInt32}
    {words : List LimbWords}
    (written : WrittenLimbPrefix initial result words index.toNat current)
    (wordAt : words[index.toNat]? = some (low, high)) :
    WrittenLimbPrefix initial result words (index.toNat + 1)
      (writeSumFinalStore current result index low high) := by
  have indexRoundtrip : UInt32.ofNat index.toNat = index := by
    apply UInt32.toNat.inj
    simp
  simpa [indexRoundtrip] using WrittenLimbPrefix.step written wordAt

/-- Extending the specification list after the already-written prefix does
not change its exact store history. -/
theorem WrittenLimbPrefix.appendWords
    {initial current : Wasm.Store host} {result : UInt32}
    {words : List LimbWords} {count : Nat}
    (written : WrittenLimbPrefix initial result words count current)
    (suffix : List LimbWords) :
    WrittenLimbPrefix initial result (words ++ suffix) count current := by
  induction written with
  | zero => exact .zero
  | step written wordAt inductionHypothesis =>
      apply WrittenLimbPrefix.step inductionHypothesis
      rw [List.getElem?_append_left]
      · exact wordAt
      · exact (List.getElem?_eq_some_iff.mp wordAt).1

/-- Exact payload writes never grow resident memory. -/
theorem WrittenLimbPrefix.pages_eq
    {initial current : Wasm.Store host} {result : UInt32}
    {words : List LimbWords} {count : Nat}
    (written : WrittenLimbPrefix initial result words count current) :
    current.mem.pages = initial.mem.pages := by
  induction written with
  | zero => rfl
  | step written wordAt ih => exact ih

/-- Address of one low/high wasm32 half in a materialized Natural payload. -/
def writtenLimbHalfAddress
    (result : UInt32) (index : Nat) (high : Bool) : UInt32 :=
  checkedLimbBase result (UInt32.ofNat index) +
    UInt32.ofNat (if high then 4 else 0)

/-- Every distinct half-limb coordinate in the written prefix occupies a
disjoint four-byte lane.  Because the comparison uses `toNat`, this predicate
also records the required absence of modular address wraparound. -/
def WrittenLimbAddressesDisjoint (result : UInt32) (count : Nat) : Prop :=
  ∀ i j highI highJ,
    i < count → j < count → (i ≠ j ∨ highI ≠ highJ) →
    (writtenLimbHalfAddress result i highI).toNat + 3 <
        (writtenLimbHalfAddress result j highJ).toNat ∨
      (writtenLimbHalfAddress result j highJ).toNat + 3 <
        (writtenLimbHalfAddress result i highI).toNat

/-- The generated address is the canonical wasm32 encoding of its ordinary
base-plus-eight-times-index coordinate.  This equality is modular and needs
no allocation premise. -/
theorem writtenLimbHalfAddress_eq_ofNat
    (result : UInt32) (index : Nat) (high : Bool) :
    writtenLimbHalfAddress result index high = UInt32.ofNat
      (result.toNat + headerBytes + 8 * index + if high then 4 else 0) := by
  rw [writtenLimbHalfAddress, checkedLimbBase, checkedScale8Word_eq_mul8]
  have resultRoundtrip : UInt32.ofNat result.toNat = result := by
    apply UInt32.toNat.inj
    simp
  nth_rewrite 1 [← resultRoundtrip]
  simp only [UInt32.ofNat_add, UInt32.ofNat_mul]
  ac_rfl

/-- A payload-wide address-space bound removes the modular reduction from
every generated half-limb coordinate in the prefix. -/
theorem writtenLimbHalfAddress_toNat_of_payloadFits
    {result : UInt32} {count index : Nat} {high : Bool}
    (payloadFits : result.toNat + headerBytes + 8 * count ≤ UInt32.size)
    (indexInPrefix : index < count) :
    (writtenLimbHalfAddress result index high).toNat =
      result.toNat + headerBytes + 8 * index + if high then 4 else 0 := by
  rw [writtenLimbHalfAddress_eq_ofNat]
  apply UInt32.toNat_ofNat_of_lt'
  cases high
  · change result.toNat + headerBytes + 8 * index + 0 < UInt32.size
    omega
  · change result.toNat + headerBytes + 8 * index + 4 < UInt32.size
    omega

/-- A nonwrapping contiguous Natural payload has pairwise-disjoint generated
four-byte lanes. -/
theorem writtenLimbAddressesDisjoint_of_payloadFits
    {result : UInt32} {count : Nat}
    (payloadFits : result.toNat + headerBytes + 8 * count ≤ UInt32.size) :
    WrittenLimbAddressesDisjoint result count := by
  intro i j highI highJ iInPrefix jInPrefix different
  rw [writtenLimbHalfAddress_toNat_of_payloadFits payloadFits iInPrefix,
    writtenLimbHalfAddress_toNat_of_payloadFits payloadFits jInPrefix]
  rcases Nat.lt_trichotomy i j with before | same | after
  · left
    cases highI <;> cases highJ <;> simp_all <;> omega
  · subst j
    rcases different with impossible | different
    · exact (impossible rfl).elim
    · cases highI <;> cases highJ <;> simp_all
  · right
    cases highI <;> cases highJ <;> simp_all <;> omega

/-- A successful raw Natural-object reservation provides the exact
nonwrapping payload bound used by both the writer projection and its header
frame.  Header fields are irrelevant here; only the allocated eight-byte limb
extent matters. -/
theorem writtenLimbPayloadFits_of_allocateObject
    {state allocated : MemoryState} {count : Nat}
    {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * count) persistent aux0 aux1 aux2 aux3 =
        .ok (allocated, address)) :
    (UInt32.ofNat address.value).toNat + headerBytes + 8 * count ≤
      UInt32.size := by
  obtain ⟨raw, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state allocated .natural
      (target.semanticSlotBytes * count) persistent aux0 aux1 aux2 aux3 address
      allocation
  have post := MemoryState.allocate_spec state raw
    (align8 (headerBytes + target.semanticSlotBytes * count)) address
    rawAllocation
  have addressToNat : (UInt32.ofNat address.value).toNat = address.value := by
    apply UInt32.toNat_ofNat_of_lt'
    simpa [wordModulus, UInt32.size] using address.isLt
  rw [addressToNat]
  have unaligned := align8_ge
    (headerBytes + target.semanticSlotBytes * count)
  have within := post.endWithinAddressSpace
  simp only [align8_align8] at within
  simpa [target, wordModulus, UInt32.size, Nat.add_assoc] using
    (Nat.le_trans (Nat.add_le_add_left unaligned address.value) within)

/-- A successful raw Natural-object reservation provides exactly the
pairwise lane separation needed by the writer projection. -/
theorem writtenLimbAddressesDisjoint_of_allocateObject
    {state allocated : MemoryState} {count : Nat}
    {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * count) persistent aux0 aux1 aux2 aux3 =
        .ok (allocated, address)) :
    WrittenLimbAddressesDisjoint (UInt32.ofNat address.value) count :=
  writtenLimbAddressesDisjoint_of_payloadFits
    (writtenLimbPayloadFits_of_allocateObject allocation)

/-- The ordinary W6 heap-Natural allocation discharges the writer's complete
lane-separation premise for its canonical limb count. -/
theorem writtenLimbAddressesDisjoint_of_allocateNatural
    {state result : MemoryState} {value : Nat} {address : Word32}
    (large : Fir.LeanIR.Impure.maxTaggedPayload < value)
    (allocation : allocateNatural state value = .ok (result, address)) :
    WrittenLimbAddressesDisjoint (UInt32.ofNat address.value)
      (naturalLimbs value).length := by
  obtain ⟨_, middle, _, objectAllocation, _, _⟩ :=
    allocateNatural_heap_decompose state result value address large allocation
  exact writtenLimbAddressesDisjoint_of_allocateObject objectAllocation

/-- Exact resident payload stores preserve every byte of the preceding common
header.  This is a Talos-memory statement; a later refinement step transports
it to W6 `Header.read` without re-proving the writer loop. -/
theorem WrittenLimbPrefix.headerBytesFrame
    {initial current : Wasm.Store host} {result : UInt32}
    {words : List LimbWords} {count : Nat}
    (written : WrittenLimbPrefix initial result words count current)
    (payloadFits : result.toNat + headerBytes + 8 * count ≤ UInt32.size)
    (offset : Nat) (offsetInHeader : offset < headerBytes) :
    current.mem.bytes (result.toNat + offset) =
      initial.mem.bytes (result.toNat + offset) := by
  induction written with
  | zero => rfl
  | @step index previous low high written wordAt ih =>
      have previousFits :
          result.toNat + headerBytes + 8 * index ≤ UInt32.size := by
        omega
      have lowAddress :
          (checkedLimbBase result (UInt32.ofNat index) + UInt32.ofNat 0).toNat =
            result.toNat + headerBytes + 8 * index := by
        simpa [writtenLimbHalfAddress] using
          (writtenLimbHalfAddress_toNat_of_payloadFits payloadFits
            (Nat.lt_succ_self index) (high := false))
      have highAddress :
          (checkedLimbBase result (UInt32.ofNat index) + UInt32.ofNat 4).toNat =
            result.toNat + headerBytes + 8 * index + 4 := by
        simpa [writtenLimbHalfAddress] using
          (writtenLimbHalfAddress_toNat_of_payloadFits payloadFits
            (Nat.lt_succ_self index) (high := true))
      calc
        (writeSumFinalStore previous result (UInt32.ofNat index) low high).mem.bytes
            (result.toNat + offset) =
            (writeSumLowStore previous result (UInt32.ofNat index) low).mem.bytes
              (result.toNat + offset) := by
                apply ResidentMemoryRel.bytes_write32_of_disjoint
                left
                rw [highAddress]
                omega
        _ = previous.mem.bytes (result.toNat + offset) := by
              apply ResidentMemoryRel.bytes_write32_of_disjoint
              left
              rw [lowAddress]
              omega
        _ = initial.mem.bytes (result.toNat + offset) :=
          ih previousFits

/-- Transport a byte-for-byte common-header frame between two resident-memory
relations into the checked W6 live-header reader.  The theorem is independent
of Natural payload arithmetic and can be reused by other resident writers. -/
theorem ResidentMemoryRel.readLiveHeader_of_headerBytesFrame
    {before after : MemoryState} {beforeMemory afterMemory : Wasm.Mem}
    {address : Word32} {header : Header}
    (beforeRelated : ResidentMemoryRel before beforeMemory)
    (afterRelated : ResidentMemoryRel after afterMemory)
    (pagesEq : afterMemory.pages = beforeMemory.pages)
    (headerFrame : ∀ offset, offset < headerBytes →
      afterMemory.bytes (address.value + offset) =
        beforeMemory.bytes (address.value + offset))
    (headerRead : before.readLiveHeader address = .ok header) :
    after.readLiveHeader address = .ok header := by
  obtain ⟨addressHeap, rawHeaderRead, headerLive, headerMinimum,
      headerAligned, headerExtent⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts before address header
      headerRead
  have sizeEq : after.memory.size = before.memory.size := by
    rw [afterRelated.size_eq, beforeRelated.size_eq, pagesEq]
  have readUInt32Eq : ∀ offset, offset + 3 < headerBytes →
      after.memory.readUInt32 (address.value + offset) =
        before.memory.readUInt32 (address.value + offset) := by
    intro offset offsetInHeader
    have beforeInBounds :
        address.value + offset + 3 < before.memory.size := by
      omega
    have afterInBounds :
        address.value + offset + 3 < after.memory.size := by
      rw [sizeEq]
      exact beforeInBounds
    rw [afterRelated.readUInt32_eq_read32 afterInBounds,
      beforeRelated.readUInt32_eq_read32 beforeInBounds]
    have addressRoundtrip :
        (UInt32.ofNat (address.value + offset)).toNat =
          address.value + offset :=
      beforeRelated.address_roundtrip beforeInBounds
    have byte0 := headerFrame offset (by omega)
    have byte1 :
        afterMemory.bytes (address.value + offset + 1) =
          beforeMemory.bytes (address.value + offset + 1) := by
      simpa [Nat.add_assoc] using headerFrame (offset + 1) (by omega)
    have byte2 :
        afterMemory.bytes (address.value + offset + 2) =
          beforeMemory.bytes (address.value + offset + 2) := by
      simpa [Nat.add_assoc] using headerFrame (offset + 2) (by omega)
    have byte3 :
        afterMemory.bytes (address.value + offset + 3) =
          beforeMemory.bytes (address.value + offset + 3) := by
      simpa [Nat.add_assoc] using headerFrame (offset + 3) (by omega)
    unfold Wasm.Mem.read32
    rw [addressRoundtrip]
    rw [byte0, byte1, byte2, byte3]
  have rawHeaderReadAfter : Header.read after.memory address = .ok header := by
    unfold Header.read
    dsimp only
    rw [readUInt32Eq headerKindOffset (by simp [headerKindOffset, headerBytes]),
      readUInt32Eq headerFlagsOffset (by simp [headerFlagsOffset, headerBytes]),
      readUInt32Eq headerRefCountOffset
        (by simp [headerRefCountOffset, headerBytes]),
      readUInt32Eq headerAllocationBytesOffset
        (by simp [headerAllocationBytesOffset, headerBytes]),
      readUInt32Eq headerAux0Offset (by simp [headerAux0Offset, headerBytes]),
      readUInt32Eq headerAux1Offset (by simp [headerAux1Offset, headerBytes]),
      readUInt32Eq headerAux2Offset (by simp [headerAux2Offset, headerBytes]),
      readUInt32Eq headerAux3Offset (by simp [headerAux3Offset, headerBytes])]
    exact rawHeaderRead
  have finalExtent :
      address.value + header.allocationBytes.toNat ≤ after.memory.size := by
    rw [sizeEq]
    exact headerExtent
  simp [MemoryState.readLiveHeader, addressHeap, rawHeaderReadAfter, headerLive,
    headerMinimum, headerAligned, finalExtent, Bind.bind, Except.bind, pure,
    Except.pure]

/-- A checked 32-bit write at or beyond a retained prefix preserves that
prefix.  This is the state-level companion to `ResidentMemoryRel.writeUInt32`
used when replaying exact resident payload histories in W6 memory. -/
theorem prefixExtension_writeUInt32After
    {before current : MemoryState} {memory : LinearMemory}
    {offset : Nat} {value : UInt32}
    (extension : before.PrefixExtension current)
    (inBounds : offset + 3 < current.memory.size)
    (written : current.memory.writeUInt32 offset value = .ok memory)
    (afterPrefix : before.heapCursor ≤ offset) :
    before.PrefixExtension ({ current with memory } : MemoryState) := by
  obtain ⟨actual, actualWrite, actualSize, _, _, _, _, byteFrame⟩ :=
    LinearMemory.writeUInt32_spec current.memory offset value inBounds
  rw [actualWrite] at written
  cases written
  refine {
    cursor := extension.cursor
    memorySize := by simpa [actualSize] using extension.memorySize
    readByte := ?_ }
  intro address beforeCursor
  rw [byteFrame address (by omega) (by omega) (by omega) (by omega)]
  exact extension.readByte address beforeCursor

/-- Replay an exact resident limb prefix in checked W6 memory.

Each Talos `write32` is paired with `LinearMemory.writeUInt32` through the
common memory relation.  The constructed W6 state preserves the original
pre-allocation prefix, the frontier invariant, and the allocator cursor. -/
theorem WrittenLimbPrefix.refineMemory_of_allocateObject
    {initial current : Wasm.Store host} {resultWord : UInt32}
    {words : List LimbWords} {index capacity : Nat}
    {before allocated : MemoryState} {address : Word32}
    {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32}
    (written : WrittenLimbPrefix initial resultWord words index current)
    (resultWordEq : resultWord = UInt32.ofNat address.value)
    (indexWithinCapacity : index ≤ capacity)
    (valid : before.FrontierInvariant)
    (allocation : before.allocateObject .natural
      (target.semanticSlotBytes * capacity) persistent aux0 aux1 aux2 aux3 =
        .ok (allocated, address))
    (initialRelated : ResidentMemoryRel allocated initial.mem) :
    ∃ heap,
      before.PrefixExtension heap ∧
      heap.FrontierInvariant ∧
      heap.heapCursor = allocated.heapCursor ∧
      ResidentMemoryRel heap current.mem := by
  subst resultWord
  induction written with
  | zero =>
      exact ⟨allocated,
        valid.allocateObject_prefixExtension allocation,
        valid.allocateObject allocation, rfl, initialRelated⟩
  | @step index previous low high written wordAt ih =>
      obtain ⟨previousHeap, previousExtension, previousValid,
          previousCursor, previousRelated⟩ :=
        ih (by omega)
      have indexInCapacity : index < capacity := by omega
      let lowOffset := address.value + headerBytes + 8 * index
      let highOffset := lowOffset + 4
      have addressToNat :
          (UInt32.ofNat address.value).toNat = address.value := by
        apply UInt32.toNat_ofNat_of_lt'
        simpa [wordModulus, UInt32.size] using address.isLt
      have lowAddressEq :
          checkedLimbBase (UInt32.ofNat address.value) (UInt32.ofNat index) +
              UInt32.ofNat 0 = UInt32.ofNat lowOffset := by
        simpa [lowOffset, writtenLimbHalfAddress, addressToNat] using
          (writtenLimbHalfAddress_eq_ofNat
            (UInt32.ofNat address.value) index false)
      have highAddressEq :
          checkedLimbBase (UInt32.ofNat address.value) (UInt32.ofNat index) +
              UInt32.ofNat 4 = UInt32.ofNat highOffset := by
        simpa [highOffset, lowOffset, writtenLimbHalfAddress, addressToNat,
          Nat.add_assoc] using
          (writtenLimbHalfAddress_eq_ofNat
            (UInt32.ofNat address.value) index true)
      have allocatedExtent := MemoryState.allocateObject_extent allocation
      have aligned := align8_ge
        (headerBytes + target.semanticSlotBytes * capacity)
      have lowBeforeFrontier : lowOffset + 4 ≤ previousHeap.heapCursor := by
        rw [previousCursor, allocatedExtent]
        simp only [target] at aligned ⊢
        omega
      have lowInBounds : lowOffset + 3 < previousHeap.memory.size :=
        Nat.lt_of_lt_of_le (by omega) previousValid.cursorInBounds
      obtain ⟨lowMemory, lowWrite, _, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec previousHeap.memory lowOffset low
          lowInBounds
      let lowHeap : MemoryState := { previousHeap with memory := lowMemory }
      have lowRelated : ResidentMemoryRel lowHeap
          (writeSumLowStore previous (UInt32.ofNat address.value)
            (UInt32.ofNat index) low).mem := by
        have relatedWrite := previousRelated.writeUInt32 lowInBounds lowWrite
        change ResidentMemoryRel lowHeap
          (previous.mem.write32
            (checkedLimbBase (UInt32.ofNat address.value)
              (UInt32.ofNat index) + UInt32.ofNat 0) low)
        rw [lowAddressEq]
        exact relatedWrite
      have lowValid : lowHeap.FrontierInvariant := by
        exact previousValid.writeUInt32 lowBeforeFrontier lowWrite
      have freshAddress := valid.allocateObject_address allocation
      have lowAfterPrefix : before.heapCursor ≤ lowOffset := by
        rw [← freshAddress]
        simp [lowOffset, headerBytes]
        omega
      have lowExtension : before.PrefixExtension lowHeap :=
        prefixExtension_writeUInt32After previousExtension lowInBounds lowWrite
          lowAfterPrefix
      have highBeforeFrontier : highOffset + 4 ≤ lowHeap.heapCursor := by
        change highOffset + 4 ≤ previousHeap.heapCursor
        rw [previousCursor, allocatedExtent]
        simp only [target] at aligned ⊢
        dsimp only [highOffset, lowOffset]
        omega
      have highInBounds : highOffset + 3 < lowHeap.memory.size :=
        Nat.lt_of_lt_of_le (by omega) lowValid.cursorInBounds
      obtain ⟨highMemory, highWrite, _, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec lowHeap.memory highOffset high
          highInBounds
      let highHeap : MemoryState := { lowHeap with memory := highMemory }
      have highRelated : ResidentMemoryRel highHeap
          (writeSumFinalStore previous (UInt32.ofNat address.value)
            (UInt32.ofNat index) low high).mem := by
        have relatedWrite := lowRelated.writeUInt32 highInBounds highWrite
        change ResidentMemoryRel highHeap
          ((writeSumLowStore previous (UInt32.ofNat address.value)
            (UInt32.ofNat index) low).mem.write32
              (checkedLimbBase (UInt32.ofNat address.value)
                (UInt32.ofNat index) + UInt32.ofNat 4) high)
        rw [highAddressEq]
        exact relatedWrite
      have highValid : highHeap.FrontierInvariant := by
        exact lowValid.writeUInt32 highBeforeFrontier highWrite
      have highAfterPrefix : before.heapCursor ≤ highOffset := by
        rw [← freshAddress]
        simp [highOffset, lowOffset, headerBytes]
        omega
      have highExtension : before.PrefixExtension highHeap :=
        prefixExtension_writeUInt32After lowExtension highInBounds highWrite
          highAfterPrefix
      exact ⟨highHeap, highExtension, highValid, by
        simpa [highHeap, lowHeap] using previousCursor, highRelated⟩

/-- Extensional read view of the first `count` materialized limbs. -/
def ReadableLimbPrefix
    (store : Wasm.Store host) (result : UInt32) (words : List LimbWords)
    (count : Nat) : Prop :=
  ∀ i low high, i < count → words[i]? = some (low, high) →
    store.mem.read32 (writtenLimbHalfAddress result i false) = low ∧
      store.mem.read32 (writtenLimbHalfAddress result i true) = high

/-- Both stores of a later limb preserve a read from a disjoint word lane. -/
theorem read32_writeSumFinalStore_disjoint
    (store : Wasm.Store host) (result index low high readAddress : UInt32)
    (lowDisjoint :
      (checkedLimbBase result index + UInt32.ofNat 0).toNat + 3 <
          readAddress.toNat ∨
        readAddress.toNat + 3 <
          (checkedLimbBase result index + UInt32.ofNat 0).toNat)
    (highDisjoint :
      (checkedLimbBase result index + UInt32.ofNat 4).toNat + 3 <
          readAddress.toNat ∨
        readAddress.toNat + 3 <
          (checkedLimbBase result index + UInt32.ofNat 4).toNat) :
    (writeSumFinalStore store result index low high).mem.read32 readAddress =
      store.mem.read32 readAddress := by
  unfold writeSumFinalStore writeSumLowStore
  rw [ResidentMemoryRel.read32_write32_disjoint _ _ _ _ highDisjoint]
  exact ResidentMemoryRel.read32_write32_disjoint _ _ _ _ lowDisjoint

/-- An exact store history projects to exact readable limbs once its byte
lanes are known to be pairwise disjoint.  This is the bridge from the writer
loop's execution invariant to the extensional payload view needed by the
concrete Natural decoder. -/
theorem WrittenLimbPrefix.readable
    {initial current : Wasm.Store host} {result : UInt32}
    {words : List LimbWords} {count : Nat}
    (written : WrittenLimbPrefix initial result words count current)
    (disjoint : WrittenLimbAddressesDisjoint result count) :
    ReadableLimbPrefix current result words count := by
  induction written with
  | zero =>
      intro i _ _ inPrefix _
      omega
  | @step index previous low high written wordAt ih =>
      have indexInPrefix : index < index + 1 := by omega
      have earlierDisjoint : WrittenLimbAddressesDisjoint result index := by
        intro i j highI highJ iInPrefix jInPrefix different
        exact disjoint i j highI highJ (by omega) (by omega) different
      have earlierReadable := ih earlierDisjoint
      intro i readLow readHigh iInPrefix readWordAt
      by_cases latest : i = index
      · subst i
        have wordsEqual : (low, high) = (readLow, readHigh) :=
          Option.some.inj (wordAt.symm.trans readWordAt)
        cases wordsEqual
        have highLowDisjoint := disjoint index index true false
          indexInPrefix indexInPrefix (Or.inr (by decide))
        constructor
        · unfold writeSumFinalStore writeSumLowStore
          rw [ResidentMemoryRel.read32_write32_disjoint]
          · exact ResidentMemoryRel.read32_write32_self _ _ _
          · simpa [writtenLimbHalfAddress] using highLowDisjoint
        · unfold writeSumFinalStore
          exact ResidentMemoryRel.read32_write32_self _ _ _
      · have earlierIndex : i < index := by omega
        have earlierWords := earlierReadable i readLow readHigh
          earlierIndex readWordAt
        have lowLowDisjoint := disjoint index i false false
          indexInPrefix iInPrefix (Or.inl (Ne.symm latest))
        have highLowDisjoint := disjoint index i true false
          indexInPrefix iInPrefix (Or.inl (Ne.symm latest))
        have lowHighDisjoint := disjoint index i false true
          indexInPrefix iInPrefix (Or.inl (Ne.symm latest))
        have highHighDisjoint := disjoint index i true true
          indexInPrefix iInPrefix (Or.inl (Ne.symm latest))
        constructor
        · calc
            (writeSumFinalStore previous result (UInt32.ofNat index) low high).mem.read32
                (writtenLimbHalfAddress result i false) =
                previous.mem.read32 (writtenLimbHalfAddress result i false) :=
              read32_writeSumFinalStore_disjoint _ _ _ _ _ _
                (by simpa [writtenLimbHalfAddress] using lowLowDisjoint)
                (by simpa [writtenLimbHalfAddress] using highLowDisjoint)
            _ = readLow := earlierWords.1
        · calc
            (writeSumFinalStore previous result (UInt32.ofNat index) low high).mem.read32
                (writtenLimbHalfAddress result i true) =
                previous.mem.read32 (writtenLimbHalfAddress result i true) :=
              read32_writeSumFinalStore_disjoint _ _ _ _ _ _
                (by simpa [writtenLimbHalfAddress] using lowHighDisjoint)
                (by simpa [writtenLimbHalfAddress] using highHighDisjoint)
            _ = readHigh := earlierWords.2

/-- A successful raw Natural reservation discharges the exact writer
history's layout premise, yielding final readable output words directly. -/
theorem WrittenLimbPrefix.readable_of_allocateObject
    {initial current : Wasm.Store host} {words : List LimbWords} {count : Nat}
    {state allocated : MemoryState} {persistent : Bool}
    {aux0 aux1 aux2 aux3 : UInt32} {address : Word32}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * count) persistent aux0 aux1 aux2 aux3 =
        .ok (allocated, address)) :
    ReadableLimbPrefix current (UInt32.ofNat address.value) words count :=
  written.readable (writtenLimbAddressesDisjoint_of_allocateObject allocation)

/-- In particular, an ordinary heap-Natural allocation discharges the layout
premise for an exact writer history of its canonical number of limbs. -/
theorem WrittenLimbPrefix.readable_of_allocateNatural
    {initial current : Wasm.Store host} {words : List LimbWords}
    {state result : MemoryState} {value : Nat} {address : Word32}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      (naturalLimbs value).length current)
    (large : Fir.LeanIR.Impure.maxTaggedPayload < value)
    (allocation : allocateNatural state value = .ok (result, address)) :
    ReadableLimbPrefix current (UInt32.ofNat address.value) words
      (naturalLimbs value).length :=
  written.readable
    (writtenLimbAddressesDisjoint_of_allocateNatural large allocation)

/-- Transport one exact readable resident word pair through the common memory
relation to the checked W6 linear-memory operations. -/
theorem ReadableLimbPrefix.readUInt32Pair
    {heap : MemoryState} {store : Wasm.Store host} {result : UInt32}
    {words : List LimbWords} {count index : Nat} {low high : UInt32}
    (readable : ReadableLimbPrefix store result words count)
    (related : ResidentMemoryRel heap store.mem)
    (payloadInBounds :
      result.toNat + headerBytes + 8 * count ≤ heap.memory.size)
    (indexInPrefix : index < count)
    (wordAt : words[index]? = some (low, high)) :
    heap.memory.readUInt32
          (result.toNat + headerBytes + 8 * index) = .ok low ∧
      heap.memory.readUInt32
          (result.toNat + headerBytes + 8 * index + 4) = .ok high := by
  have residentReads := readable index low high indexInPrefix wordAt
  have lowInBounds :
      result.toNat + headerBytes + 8 * index + 3 < heap.memory.size := by
    omega
  have highInBounds :
      result.toNat + headerBytes + 8 * index + 4 + 3 < heap.memory.size := by
    omega
  have residentLow : store.mem.read32 (UInt32.ofNat
      (result.toNat + headerBytes + 8 * index)) = low := by
    simpa [writtenLimbHalfAddress_eq_ofNat] using residentReads.1
  have residentHigh : store.mem.read32 (UInt32.ofNat
      (result.toNat + headerBytes + 8 * index + 4)) = high := by
    simpa [writtenLimbHalfAddress_eq_ofNat] using residentReads.2
  constructor
  · rw [related.readUInt32_eq_read32 lowInBounds, residentLow]
  · rw [related.readUInt32_eq_read32 highInBounds, residentHigh]

/-- Exact readable resident word pairs decode through W6's ordinary Natural
limb reader to their unbounded little-endian value.  No canonicality premise
is needed: `readNaturalLimbs` is intentionally an extensional decoder. -/
theorem ReadableLimbPrefix.readNaturalLimbs
    {heap : MemoryState} {store : Wasm.Store host} {result : UInt32}
    {words : List LimbWords} {count : Nat}
    (readable : ReadableLimbPrefix store result words count)
    (related : ResidentMemoryRel heap store.mem)
    (wordsLength : words.length = count)
    (payloadInBounds :
      result.toNat + headerBytes + 8 * count ≤ heap.memory.size) :
    Fir.Wasm.Concrete.readNaturalLimbs heap.memory result.toNat 0 count =
      .ok (limbWordsListValue words) := by
  have limbAt : ∀ offset limb,
      (words.map limbUInt64OfWords)[offset]? = some limb →
      heap.memory.readUInt64
          (result.toNat + headerBytes +
            target.semanticSlotBytes * (0 + offset)) = .ok limb := by
    intro offset limb mappedAt
    rw [List.getElem?_map] at mappedAt
    cases wordAt : words[offset]? with
    | none => simp [wordAt] at mappedAt
    | some word =>
        have limbEq : limbUInt64OfWords word = limb := by
          simpa [wordAt] using mappedAt
        subst limb
        have offsetInWords := (List.getElem?_eq_some_iff.mp wordAt).1
        have offsetInPrefix : offset < count := by omega
        rcases word with ⟨low, high⟩
        have reads := readable.readUInt32Pair related payloadInBounds
          offsetInPrefix wordAt
        unfold LinearMemory.readUInt64
        simp only [target, Nat.zero_add]
        rw [reads.1, reads.2]
        rfl
  have decoded := readNaturalLimbs_of_limbAt heap.memory result.toNat 0
    (words.map limbUInt64OfWords) limbAt
  simpa [wordsLength, naturalLimbsValue_map_limbUInt64OfWords] using decoded

/-- Structural Natural-object boundary after a raw reservation.

The resident execution proof need only preserve the allocator's exact header
and expose the extensional limb decoder result.  Allocation alone supplies the
object extent, aligned payload capacity, ordinary ownership metadata, and the
wasm32 round trips.  In particular, this theorem does not require the payload
bytes to equal `naturalLimbs value`. -/
theorem naturalObjectRel_of_allocateObject_and_decoded
    {state allocated heap : MemoryState} {address : Word32}
    {count value : Nat}
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * count) false bigNaturalMarker
        (UInt32.ofNat count) 0 0 = .ok (allocated, address))
    (cursorEq : heap.heapCursor = allocated.heapCursor)
    (headerRead : heap.readLiveHeader address = .ok
      (Header.forAllocation .natural
        (align8 (headerBytes + target.semanticSlotBytes * count)) false
        bigNaturalMarker (UInt32.ofNat count) 0 0))
    (decodedLimbs : Fir.Wasm.Concrete.readNaturalLimbs heap.memory
      address.value 0 count = .ok value) :
    NaturalObjectRel heap address value
      (Header.forAllocation .natural
        (align8 (headerBytes + target.semanticSlotBytes * count)) false
        bigNaturalMarker (UInt32.ofNat count) 0 0) := by
  let allocationBytes :=
    align8 (headerBytes + target.semanticSlotBytes * count)
  let header := Header.forAllocation .natural allocationBytes false
    bigNaturalMarker (UInt32.ofNat count) 0 0
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header state allocated .natural
      (target.semanticSlotBytes * count) false bigNaturalMarker
      (UInt32.ofNat count) 0 0 address allocation
  have allocationPost := MemoryState.allocate_spec state rawState
    allocationBytes address (by simpa [allocationBytes] using rawAllocation)
  have addressNonzero : address.value ≠ 0 := by
    intro zero
    have heapAddress := allocationPost.addressClass
    simp [Word32.classify, zero] at heapAddress
  have allocationLt : allocationBytes < UInt32.size := by
    have within := allocationPost.endWithinAddressSpace
    have aligned : align8 allocationBytes = allocationBytes := by
      simp [allocationBytes]
    rw [aligned] at within
    have belowWordModulus : allocationBytes < wordModulus := by omega
    simpa [wordModulus] using belowWordModulus
  have allocationToNat :
      (UInt32.ofNat allocationBytes).toNat = allocationBytes :=
    UInt32.toNat_ofNat_of_lt' allocationLt
  have countLt : count < UInt32.size := by
    have countLe : count ≤ allocationBytes := by
      dsimp only [allocationBytes]
      have aligned := align8_ge
        (headerBytes + target.semanticSlotBytes * count)
      simp only [target] at aligned ⊢
      omega
    exact Nat.lt_of_le_of_lt countLe allocationLt
  have countToNat : (UInt32.ofNat count).toNat = count :=
    UInt32.toNat_ofNat_of_lt' countLt
  have resultExtent := MemoryState.allocateObject_extent allocation
  have addressHeap : address.classify = .heap := by
    have checked := headerRead
    unfold MemoryState.readLiveHeader at checked
    split at checked
    next heapAddress => exact heapAddress
    next => contradiction
  have headerRead' : heap.readLiveHeader address = .ok header := by
    simpa [header, allocationBytes] using headerRead
  have decoded : readNatural heap address = .ok value := by
    unfold readNatural
    simp only [addressHeap, ↓reduceIte, Bind.bind, Except.bind]
    rw [headerRead']
    simp only [liftMemory]
    have accepted : header.kind == ObjectKind.natural &&
        header.aux0 == bigNaturalMarker := by
      simp [header, Header.forAllocation]
      decide
    rw [accepted]
    simp only [↓reduceIte]
    change liftMemory (Fir.Wasm.Concrete.readNaturalLimbs heap.memory
      address.value 0 header.aux1.toNat) = .ok value
    rw [show header.aux1.toNat = count by
      simp [header, Header.forAllocation, countToNat]]
    rw [decodedLimbs]
    rfl
  change NaturalObjectRel heap address value header
  refine {
    headerRead := headerRead'
    headerKind := rfl
    ordinary := rfl
    marker := rfl
    extent := ?_
    limbsFit := ?_
    decoded
    refCountOne := rfl }
  · rw [cursorEq, resultExtent]
    simp [header, Header.forAllocation, allocationBytes, allocationToNat]
  · have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * count)
    simpa [header, Header.forAllocation, allocationBytes, allocationToNat,
      countToNat] using aligned

/-- The complete writer loop materializes exactly the pure output prefix, not
merely an arbitrary sequence of in-bounds stores. -/
theorem wp_writeSumLoopProgram_of_exactPrefix
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex : Nat}
    {Q : Wasm.Assertion host} {initialStore : Wasm.Store host}
    {left leftFlavor right rightFlavor result count initialCarry : UInt32}
    {initialLeftLow initialLeftHigh initialRightLow initialRightHigh low high
      carryLocal carryExtra scaled : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    {leftWords rightWords : List LimbWords}
    (leftLength : leftWords.length = count.toNat)
    (rightLength : rightWords.length = count.toNat)
    (leftLowRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      Wasm.TerminatesWith env module magnitudeLowIndex current
        ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
        (fun final values => final = current ∧
          values = .i32 (leftWords[index.toNat]'(by omega)).1 :: tail))
    (leftHighRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      Wasm.TerminatesWith env module magnitudeHighIndex current
        ([.i32 index, .i32 leftFlavor, .i32 left] ++ tail)
        (fun final values => final = current ∧
          values = .i32 (leftWords[index.toNat]'(by omega)).2 :: tail))
    (rightLowRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      Wasm.TerminatesWith env module magnitudeLowIndex current
        ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
        (fun final values => final = current ∧
          values = .i32 (rightWords[index.toNat]'(by omega)).1 :: tail))
    (rightHighRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      Wasm.TerminatesWith env module magnitudeHighIndex current
        ([.i32 index, .i32 rightFlavor, .i32 right] ++ tail)
        (fun final values => final = current ∧
          values = .i32 (rightWords[index.toNat]'(by omega)).2 :: tail))
    (writeInBounds : ∀ (index : UInt32) (current : Wasm.Store host)
      (_beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      ¬(checkedLimbBase result index).toNat + 4 >
          current.mem.pages * 65536 ∧
        ¬(checkedLimbBase result index).toNat + 4 + 4 >
          current.mem.pages * 65536)
    (completed : ∀ finalStore,
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          count.toNat finalStore →
      Q (.Return finalStore
        (.i32 (addLimbWords leftWords rightWords initialCarry).2 :: tail))) :
    Wasm.wp module
      (writeSumLoopProgram magnitudeLowIndex magnitudeHighIndex ++ rest) Q
      initialStore
      (writeSumArithmeticLocals left leftFlavor right rightFlavor result 0
        count initialCarry initialLeftLow initialLeftHigh initialRightLow
        initialRightHigh low high carryLocal carryExtra scaled tail) env := by
  let outputWords := (addLimbWords leftWords rightWords initialCarry).1
  let expectedCarry := (addLimbWords leftWords rightWords initialCarry).2
  have sameLength : leftWords.length = rightWords.length := by
    rw [leftLength, rightLength]
  have outputLength : outputWords.length = count.toNat := by
    change (addLimbWords leftWords rightWords initialCarry).1.length =
      count.toNat
    rw [addLimbWords_length leftWords rightWords initialCarry
      sameLength, leftLength]
  let Inv : UInt32 → UInt32 → Wasm.Store host → Prop :=
    fun index carry current =>
      index.toNat ≤ count.toNat ∧
      addLimbWords (leftWords.drop index.toNat)
          (rightWords.drop index.toNat) carry =
        (outputWords.drop index.toNat, expectedCarry) ∧
      WrittenLimbPrefix initialStore result outputWords index.toNat current
  apply wp_writeSumLoopProgram_of_invariant (Inv := Inv)
  · exact ⟨by simp, by simp [outputWords, expectedCarry], .zero⟩
  · intro index carry current invariant
    exact invariant.1
  · intro carry current invariant
    have leftDrop : leftWords.drop count.toNat = [] := by
      rw [← leftLength]
      simp
    have rightDrop : rightWords.drop count.toNat = [] := by
      rw [← rightLength]
      simp
    have outputDrop : outputWords.drop count.toNat = [] := by
      rw [← outputLength]
      simp
    have carryEq : carry = expectedCarry := by
      simpa [Inv, leftDrop, rightDrop, outputDrop, addLimbWords] using
        congrArg Prod.snd invariant.2.1
    rw [carryEq]
    simpa [outputWords, expectedCarry] using completed current invariant.2.2
  · intro index carry current invariant beforeCount
    let leftLimb : LimbWords := leftWords[index.toNat]'(by omega)
    let rightLimb : LimbWords := rightWords[index.toNat]'(by omega)
    have outputBefore : index.toNat < outputWords.length := by
      rw [outputLength]
      exact beforeCount
    have leftLowRun' := leftLowRun index current beforeCount invariant.2.2
    have leftHighRun' := leftHighRun index current beforeCount invariant.2.2
    have rightLowRun' := rightLowRun index current beforeCount invariant.2.2
    have rightHighRun' := rightHighRun index current beforeCount invariant.2.2
    obtain ⟨lowInBounds, highInBounds⟩ :=
      writeInBounds index current beforeCount invariant.2.2
    refine ⟨leftLimb.1, leftLimb.2, rightLimb.1, rightLimb.2,
      leftLowRun', leftHighRun', rightLowRun', rightHighRun', lowInBounds,
      highInBounds, ?_⟩
    have leftDrop := List.drop_eq_getElem_cons
      (l := leftWords) (i := index.toNat) (by omega)
    have rightDrop := List.drop_eq_getElem_cons
      (l := rightWords) (i := index.toNat) (by omega)
    have outputDrop := List.drop_eq_getElem_cons
      (l := outputWords) (i := index.toNat) outputBefore
    have recurrence := invariant.2.1
    rw [leftDrop, rightDrop, outputDrop] at recurrence
    simp only [addLimbWords, Prod.mk.injEq, List.cons.injEq] at recurrence
    refine ⟨?_, ?_, ?_⟩
    · rw [sumCarryNextIndex_toNat beforeCount]
      omega
    · rw [sumCarryNextIndex_toNat beforeCount]
      apply Prod.ext
      · simpa [leftLimb, rightLimb] using recurrence.1.2
      · simpa [leftLimb, rightLimb] using recurrence.2
    · have outputWordAt : outputWords[index.toNat]? = some (
          limbSumLow leftLimb.1 rightLimb.1 carry,
          limbSumHigh leftLimb.1 leftLimb.2 rightLimb.1 rightLimb.2
            carry) := by
        rw [getElem?_pos outputWords index.toNat outputBefore]
        exact congrArg some (by
          simpa [leftLimb, rightLimb] using recurrence.1.1.symm)
      rw [sumCarryNextIndex_toNat beforeCount]
      exact WrittenLimbPrefix.next invariant.2.2 outputWordAt

/-- Call-level total correctness for the actual adapted BigNumeric sum writer.
The caller's operand tail is preserved exactly, while the physical result
store records precisely the pure output-limb prefix. -/
theorem terminatesWith_writeSumFromFunction_of_exactPrefix
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {targetFunction : Wasm.Function}
    {functionIndex magnitudeLowIndex magnitudeHighIndex : Nat}
    {initialStore : Wasm.Store host}
    {left leftFlavor right rightFlavor result count initialCarry : UInt32}
    {tail : List Wasm.Value} {leftWords rightWords : List LimbWords}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction =
        .ok targetFunction)
    (magnitudeLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowName) =
        some magnitudeLowIndex)
    (magnitudeHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighName) =
        some magnitudeHighIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (leftLength : leftWords.length = count.toNat)
    (rightLength : rightWords.length = count.toNat)
    (leftLowRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      Wasm.TerminatesWith env module magnitudeLowIndex current
        [.i32 index, .i32 leftFlavor, .i32 left]
        (fun final values => final = current ∧
          values = [.i32 (leftWords[index.toNat]'(by omega)).1]))
    (leftHighRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      Wasm.TerminatesWith env module magnitudeHighIndex current
        [.i32 index, .i32 leftFlavor, .i32 left]
        (fun final values => final = current ∧
          values = [.i32 (leftWords[index.toNat]'(by omega)).2]))
    (rightLowRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      Wasm.TerminatesWith env module magnitudeLowIndex current
        [.i32 index, .i32 rightFlavor, .i32 right]
        (fun final values => final = current ∧
          values = [.i32 (rightWords[index.toNat]'(by omega)).1]))
    (rightHighRun : ∀ (index : UInt32) (current : Wasm.Store host)
      (beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      Wasm.TerminatesWith env module magnitudeHighIndex current
        [.i32 index, .i32 rightFlavor, .i32 right]
        (fun final values => final = current ∧
          values = [.i32 (rightWords[index.toNat]'(by omega)).2]))
    (writeInBounds : ∀ (index : UInt32) (current : Wasm.Store host)
      (_beforeCount : index.toNat < count.toNat),
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          index.toNat current →
      ¬(checkedLimbBase result index).toNat + 4 >
          current.mem.pages * 65536 ∧
        ¬(checkedLimbBase result index).toNat + 4 + 4 >
          current.mem.pages * 65536) :
    Wasm.TerminatesWith env module functionIndex initialStore
      ([.i32 initialCarry, .i32 count, .i32 0, .i32 result,
        .i32 rightFlavor, .i32 right, .i32 leftFlavor, .i32 left] ++ tail)
      (fun final values =>
        WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          count.toNat final ∧
        values =
          .i32 (addLimbWords leftWords rightWords initialCarry).2 :: tail) := by
  let suffix := FirTalos.functionTerminal sourceModule
    Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromFunction
  let targetFunction' := writeSumTargetFunction magnitudeLowIndex
    magnitudeHighIndex suffix
  let args : List Wasm.Value :=
    [.i32 initialCarry, .i32 count, .i32 0, .i32 result,
      .i32 rightFlavor, .i32 right, .i32 leftFlavor, .i32 left] ++ tail
  have targetShape := adaptedWriteSumFromFunction_eq adapted
    magnitudeLowFound magnitudeHighFound
  rw [targetShape] at found
  refine FirTalos.Correctness.terminatesWith_of_wp_body_at
    (function := targetFunction') (args := args)
    (Post := fun final values =>
      WrittenLimbPrefix initialStore result
          (addLimbWords leftWords rightWords initialCarry).1
          count.toNat final ∧
        values =
          .i32 (addLimbWords leftWords rightWords initialCarry).2 :: tail)
    notImport (by simpa [targetFunction', suffix] using found) ?_
  change Wasm.wp module
    (writeSumLoopProgram magnitudeLowIndex magnitudeHighIndex ++ suffix) _
    initialStore
    (writeSumArithmeticLocals left leftFlavor right rightFlavor result 0
      count initialCarry 0 0 0 0 0 0 0 0 0 []) env
  apply wp_writeSumLoopProgram_of_exactPrefix
    (leftWords := leftWords) (rightWords := rightWords)
    leftLength rightLength
  · simpa using leftLowRun
  · simpa using leftHighRun
  · simpa using rightLowRun
  · simpa using rightHighRun
  · exact writeInBounds
  · intro finalStore written
    simpa [FirTalos.Correctness.FunctionBodyPost, targetFunction',
      writeSumTargetFunction, args, Wasm.Function.numParams] using written

/-- Exact successor store after materializing the low half of a carry limb. -/
def checkedCarryLowStore (store : Wasm.Store host) (object index : UInt32) :
    Wasm.Store host :=
  { store with mem := (store.mem.write32
      (checkedLimbBase object index + UInt32.ofNat 0) 1) }

/-- Exact successor store after materializing the complete 64-bit carry limb
`[low = 1, high = 0]`. -/
def checkedCarryFinalStore (store : Wasm.Store host) (object index : UInt32) :
    Wasm.Store host :=
  let lowStore := checkedCarryLowStore store object index
  { lowStore with mem := (lowStore.mem.write32
      (checkedLimbBase object index + UInt32.ofNat 4) 0) }

theorem checkedCarryFinalStore_eq_writeSumFinalStore
    (store : Wasm.Store host) (object index : UInt32) :
    checkedCarryFinalStore store object index =
      writeSumFinalStore store object index 1 0 := by
  rfl

/-- Final store selected by the producer after the writer returns its carry. -/
def completedAddStore (store : Wasm.Store host) (object : UInt32)
    (count : Nat) (carry : UInt32) : Wasm.Store host :=
  if carry = 0 then store else
    checkedCarryFinalStore store object (UInt32.ofNat count)

/-- The exact writer history extends by precisely the producer's constant
`[1, 0]` carry limb when the arithmetic carry is nonzero. -/
theorem WrittenLimbPrefix.completeWithCarry
    {initial current : Wasm.Store host} {result carry : UInt32}
    {words : List LimbWords} {count : Nat}
    (written : WrittenLimbPrefix initial result words count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1) :
    WrittenLimbPrefix initial result (completedAddLimbWords words carry)
      (count + carry.toNat) (completedAddStore current result count carry) := by
  rcases carryBit with rfl | rfl
  · simpa [completedAddLimbWords, completedAddStore] using written
  · have carryAt : (words ++ [(1, 0)])[count]? = some (1, 0) := by
      rw [← wordsLength]
      simp
    have extended := WrittenLimbPrefix.step
      (written.appendWords [(1, 0)]) carryAt
    simpa [completedAddLimbWords, completedAddStore,
      checkedCarryFinalStore_eq_writeSumFinalStore] using extended

/-- The completed writer, including its optional carry store, preserves the
allocator's entire common header byte for byte.  Successful reservation
discharges the single wasm32 nonwrap premise. -/
theorem WrittenLimbPrefix.headerBytesFrame_completeWithCarry_of_allocateObject
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count : Nat}
    {state allocated : MemoryState} {persistent : Bool}
    {aux0 aux1 aux2 aux3 : UInt32}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) persistent
        aux0 aux1 aux2 aux3 = .ok (allocated, address))
    (offset : Nat) (offsetInHeader : offset < headerBytes) :
    (completedAddStore current (UInt32.ofNat address.value) count carry).mem.bytes
        ((UInt32.ofNat address.value).toNat + offset) =
      initial.mem.bytes ((UInt32.ofNat address.value).toNat + offset) := by
  have completed := written.completeWithCarry wordsLength carryBit
  exact completed.headerBytesFrame
    (writtenLimbPayloadFits_of_allocateObject allocation) offset offsetInHeader

/-- Construct the final W6 memory state corresponding to the completed
resident writer, including its optional carry limb.  All structural heap
premises consumed by the live-heap theorem are returned explicitly. -/
theorem WrittenLimbPrefix.refineMemory_completeWithCarry_of_allocateObject
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count : Nat}
    {before allocated : MemoryState}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (valid : before.FrontierInvariant)
    (allocation : before.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0 =
          .ok (allocated, address))
    (initialRelated : ResidentMemoryRel allocated initial.mem) :
    ∃ heap,
      before.PrefixExtension heap ∧
      heap.FrontierInvariant ∧
      heap.heapCursor = allocated.heapCursor ∧
      ResidentMemoryRel heap
        (completedAddStore current (UInt32.ofNat address.value) count carry).mem ∧
      address.value + headerBytes + 8 * (count + carry.toNat) ≤
        heap.memory.size := by
  have completed := written.completeWithCarry wordsLength carryBit
  obtain ⟨heap, extension, finalValid, cursorEq, finalRelated⟩ :=
    completed.refineMemory_of_allocateObject rfl (Nat.le_refl _) valid
      allocation initialRelated
  have allocatedExtent := MemoryState.allocateObject_extent allocation
  have aligned := align8_ge
    (headerBytes + target.semanticSlotBytes * (count + carry.toNat))
  have payloadInBounds :
      address.value + headerBytes + 8 * (count + carry.toNat) ≤
        heap.memory.size := by
    calc
      address.value + headerBytes + 8 * (count + carry.toNat) ≤
          address.value + align8
            (headerBytes + target.semanticSlotBytes *
              (count + carry.toNat)) := by
            simp only [target] at aligned ⊢
            omega
      _ = allocated.heapCursor := allocatedExtent.symm
      _ = heap.heapCursor := cursorEq.symm
      _ ≤ heap.memory.size := finalValid.cursorInBounds
  exact ⟨heap, extension, finalValid, cursorEq, finalRelated, payloadInBounds⟩

/-- End-to-end payload decoder boundary for the installed writer plus its
optional carry store.  The raw reservation supplies lane separation; the
common memory relation transports exact resident reads to W6's decoder. -/
theorem WrittenLimbPrefix.readNaturalLimbs_completeWithCarry_of_allocateObject
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count : Nat}
    {state allocated heap : MemoryState} {persistent : Bool}
    {aux0 aux1 aux2 aux3 : UInt32}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) persistent
        aux0 aux1 aux2 aux3 = .ok (allocated, address))
    (related : ResidentMemoryRel heap
      (completedAddStore current (UInt32.ofNat address.value) count carry).mem)
    (payloadInBounds :
      address.value + headerBytes + 8 * (count + carry.toNat) ≤
        heap.memory.size) :
    Fir.Wasm.Concrete.readNaturalLimbs heap.memory address.value 0
        (count + carry.toNat) =
      .ok (limbWordsListValue (completedAddLimbWords words carry)) := by
  have completed := written.completeWithCarry wordsLength carryBit
  have readable := completed.readable_of_allocateObject allocation
  have completedLength := completedAddLimbWords_length words carry carryBit
  have addressToNat : (UInt32.ofNat address.value).toNat = address.value := by
    apply UInt32.toNat_ofNat_of_lt'
    simpa [wordModulus, UInt32.size] using address.isLt
  have decoded := readable.readNaturalLimbs related
    (by omega) (by simpa [addressToNat] using payloadInBounds)
  simpa [addressToNat] using decoded

/-- The exact resident writer, terminal carry store, and raw allocator facts
assemble into the complete W6 Natural object relation.

This is the reusable object-level handoff to W7.  The only execution-specific
header obligation left visible is that the disjoint payload stores preserve
the exact header installed by the allocator. -/
theorem WrittenLimbPrefix.naturalObjectRel_completeWithCarry_of_allocateObject
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count value : Nat}
    {state allocated heap : MemoryState}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0 =
          .ok (allocated, address))
    (cursorEq : heap.heapCursor = allocated.heapCursor)
    (headerRead : heap.readLiveHeader address = .ok
      (Header.forAllocation .natural
        (align8 (headerBytes +
          target.semanticSlotBytes * (count + carry.toNat))) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0))
    (related : ResidentMemoryRel heap
      (completedAddStore current (UInt32.ofNat address.value) count carry).mem)
    (payloadInBounds :
      address.value + headerBytes + 8 * (count + carry.toNat) ≤
        heap.memory.size)
    (valueEq : limbWordsListValue (completedAddLimbWords words carry) = value) :
    NaturalObjectRel heap address value
      (Header.forAllocation .natural
        (align8 (headerBytes +
          target.semanticSlotBytes * (count + carry.toNat))) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0) := by
  apply naturalObjectRel_of_allocateObject_and_decoded allocation cursorEq
    headerRead
  have decoded := written.readNaturalLimbs_completeWithCarry_of_allocateObject
    wordsLength carryBit allocation related payloadInBounds
  simpa [valueEq] using decoded

/-- Fully derived object boundary for the completed resident writer.

Unlike the preceding factoring theorem, this form does not ask W7 to provide
the final header as a separate premise.  The raw allocator's initial memory
relation, the exact writer history, and the final memory relation imply that
header through the common-header byte frame. -/
theorem WrittenLimbPrefix.naturalObjectRel_completeWithCarry_of_memoryRel
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count value : Nat}
    {state allocated heap : MemoryState}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0 =
          .ok (allocated, address))
    (cursorEq : heap.heapCursor = allocated.heapCursor)
    (initialRelated : ResidentMemoryRel allocated initial.mem)
    (finalRelated : ResidentMemoryRel heap
      (completedAddStore current (UInt32.ofNat address.value) count carry).mem)
    (payloadInBounds :
      address.value + headerBytes + 8 * (count + carry.toNat) ≤
        heap.memory.size)
    (valueEq : limbWordsListValue (completedAddLimbWords words carry) = value) :
    NaturalObjectRel heap address value
      (Header.forAllocation .natural
        (align8 (headerBytes +
          target.semanticSlotBytes * (count + carry.toNat))) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0) := by
  let header := Header.forAllocation .natural
    (align8 (headerBytes + target.semanticSlotBytes *
      (count + carry.toNat))) false bigNaturalMarker
    (UInt32.ofNat (count + carry.toNat)) 0 0
  have initialHeaderRead : allocated.readLiveHeader address = .ok header := by
    simpa [header] using
      (MemoryState.readLiveHeader_of_allocateObject_eq_ok state allocated
        .natural (target.semanticSlotBytes * (count + carry.toNat)) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0 address
        allocation)
  have completed := written.completeWithCarry wordsLength carryBit
  have headerFrameRaw :=
    written.headerBytesFrame_completeWithCarry_of_allocateObject
      wordsLength carryBit allocation
  have addressToNat : (UInt32.ofNat address.value).toNat = address.value := by
    apply UInt32.toNat_ofNat_of_lt'
    simpa [wordModulus, UInt32.size] using address.isLt
  have headerFrame : ∀ offset, offset < headerBytes →
      (completedAddStore current (UInt32.ofNat address.value) count carry).mem.bytes
          (address.value + offset) =
        initial.mem.bytes (address.value + offset) := by
    intro offset offsetInHeader
    simpa [addressToNat] using headerFrameRaw offset offsetInHeader
  have finalHeaderRead : heap.readLiveHeader address = .ok header :=
    ResidentMemoryRel.readLiveHeader_of_headerBytesFrame initialRelated
      finalRelated completed.pages_eq headerFrame initialHeaderRead
  apply written.naturalObjectRel_completeWithCarry_of_allocateObject
    wordsLength carryBit allocation cursorEq
    (by simpa [header] using finalHeaderRead) finalRelated payloadInBounds
    valueEq

/-- Insert a freshly reserved, fully decoded Natural object into the complete
live-heap refinement.

The theorem deliberately separates object representation from heap/witness
bookkeeping.  A resident helper may establish `NaturalObjectRel` by exact
execution, then discharge only prefix extension and the final frontier here;
all location, descriptor, spatial, fuel, and typed-value consequences are
derived uniformly. -/
theorem liveHeapRel_of_freshNaturalObjectRel
    {state allocated result : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState} {value payloadBytes : Nat}
    {address : Word32} {header : Header} {persistent : Bool}
    {aux0 aux1 aux2 aux3 : UInt32}
    (related : LiveHeapRel state witness runtime)
    (allocation : state.allocateObject .natural payloadBytes persistent
      aux0 aux1 aux2 aux3 = .ok (allocated, address))
    (extension : state.PrefixExtension result)
    (finalFrontier : result.FrontierInvariant)
    (objectRelated : NaturalObjectRel result address value header) :
    let nextWitness := witness.bindNatural runtime.nextLocation address value
    witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel result nextWitness (semanticNaturalResult runtime value) ∧
      ValueRel nextWitness .tobject (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  have freshAddress := related.frontier.allocateObject_address allocation
  have locationFresh :
      witness.locations.lookup? runtime.nextLocation = none := by
    cases found : witness.locations.lookup? runtime.nextLocation with
    | none => rfl
    | some oldAddress =>
        exfalso
        obtain ⟨cell, semanticFound, _⟩ :=
          related.concreteToSemantic runtime.nextLocation oldAddress found
        have beforeNext :=
          related.locationsBeforeNext runtime.nextLocation cell semanticFound
        exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    omega
  have witnessExtension := witness.bindNatural_extends runtime.nextLocation
    address value locationFresh descriptorFresh
  have locationAddressFresh : ∀ old oldAddress,
      witness.locations.lookup? old = some oldAddress → oldAddress ≠ address := by
    intro old oldAddress found equal
    obtain ⟨cell, _, cellRelated⟩ :=
      related.concreteToSemantic old oldAddress found
    have owned := cellRelated.headerOwned
    subst oldAddress
    simp [headerBytes] at owned
    omega
  have promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.Contains payload oldAddress →
      address ≠ oldAddress := by
    intro payload oldAddress found equal
    have promoted := related.promoted payload oldAddress found
    obtain ⟨oldHeader, _, _, _, _, _, extent, payloadFits⟩ := promoted.header
    subst oldAddress
    simp [headerBytes] at payloadFits extent
    omega
  obtain ⟨addressHeap, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address header
      objectRelated.headerRead
  have headerOwned : address.value + headerBytes ≤ result.heapCursor :=
    Nat.le_trans (Nat.add_le_add_left headerMinimum address.value)
      objectRelated.extent
  have witnessWellFormed := related.witnessWellFormed.bindNatural
    runtime.nextLocation address value addressHeap locationAddressFresh
      promotedAddressFresh
  have newRegion : ∃ newHeader,
      Header.read result.memory address = .ok newHeader ∧
      headerBytes ≤ newHeader.allocationBytes.toNat ∧
      newHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + newHeader.allocationBytes.toNat ≤ result.heapCursor :=
    ⟨header, rawHeaderRead, headerMinimum, headerAligned,
      objectRelated.extent⟩
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial extension address freshAddress
      (fun other different =>
        witness.lookup_bindNatural_descriptor_other runtime.nextLocation
          address other value different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindNatural runtime.nextLocation address value) address
      (semanticNaturalCell value) := by
    apply LiveCellRel.natural
      (RefinementWitness.lookup_bindNatural_descriptor witness
        runtime.nextLocation address value)
      (by rfl) objectRelated.headerRead objectRelated.headerKind
        objectRelated.marker objectRelated.extent objectRelated.limbsFit
        objectRelated.decoded
    · simpa [semanticNaturalCell] using objectRelated.refCountOne
    · simpa [semanticNaturalCell] using objectRelated.ordinary
    · rfl
  refine ⟨witnessExtension,
    ClosureAllocationsPersistent.bindNatural witness runtime.nextLocation
      address value,
    ?_, ValueRel.new_natural_result witness runtime.nextLocation address value⟩
  refine {
    frontier := finalFrontier
    witnessWellFormed
    locationsBeforeNext := ?_
    releaseFuelBound := ?_
    descriptorsOwned := ?_
    descriptorRegion
    descriptorDisjoint
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      change runtime.nextLocation < runtime.nextLocation + 1
      exact Nat.lt_succ_self runtime.nextLocation
    · have oldFound : Fir.LeanIR.Impure.findCell? runtime.heap location =
          some cell := by
        simpa [semanticNaturalResult, Fir.LeanIR.Impure.findCell?, isNew,
          Ne.symm isNew] using found
      have oldBefore := related.locationsBeforeNext location cell oldFound
      exact Nat.lt_trans oldBefore (Nat.lt_succ_self runtime.nextLocation)
  · have cursorGrowth : state.heapCursor + headerBytes ≤ result.heapCursor := by
      rw [← freshAddress]
      exact headerOwned
    have oldFuel := related.releaseFuelBound
    simp [semanticNaturalResult, headerBytes] at oldFuel cursorGrowth ⊢
    omega
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact headerOwned
    · rw [witness.lookup_bindNatural_descriptor_other runtime.nextLocation
        address other value isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticNaturalCell value := by
        simpa [semanticNaturalResult, Fir.LeanIR.Impure.findCell?] using
          found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindNatural_location witness
          runtime.nextLocation address value,
        .live newCellRelated⟩
    · have oldFound : Fir.LeanIR.Impure.findCell? runtime.heap location =
          some cell := by
        simpa [semanticNaturalResult, Fir.LeanIR.Impure.findCell?, isNew,
          Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension extension).witnessExtension
          witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindNatural, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticNaturalCell value,
        by simp [semanticNaturalResult, Fir.LeanIR.Impure.findCell?],
        .live newCellRelated⟩
    · rw [witness.lookup_bindNatural_location_other runtime.nextLocation
        location address value isNew] at mapped
      obtain ⟨cell, oldFound, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticNaturalResult, Fir.LeanIR.Impure.findCell?, isNew,
            Ne.symm isNew],
        (cellRelated.prefixExtension extension).witnessExtension
          witnessExtension⟩
  · intro payload concreteAddress mapped
    exact ((related.promoted payload concreteAddress mapped).prefixExtension
      extension).witnessExtension witnessExtension

/-- End-to-end live-heap boundary for a completed resident Natural writer.

All arithmetic, exact stores, header preservation, object decoding, witness
extension, spatial separation, and returned object typing are composed here.
The remaining helper-specific execution obligations are the raw allocation
transition, exact writer history, and preservation of the ordinary W6
frontier/prefix invariants by those physical writes. -/
theorem WrittenLimbPrefix.liveHeapRel_completeWithCarry_of_memoryRel
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count value : Nat}
    {state allocated heap : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (allocation : state.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0 =
          .ok (allocated, address))
    (heapRelated : LiveHeapRel state witness runtime)
    (extension : state.PrefixExtension heap)
    (finalFrontier : heap.FrontierInvariant)
    (cursorEq : heap.heapCursor = allocated.heapCursor)
    (initialRelated : ResidentMemoryRel allocated initial.mem)
    (finalRelated : ResidentMemoryRel heap
      (completedAddStore current (UInt32.ofNat address.value) count carry).mem)
    (payloadInBounds :
      address.value + headerBytes + 8 * (count + carry.toNat) ≤
        heap.memory.size)
    (valueEq : limbWordsListValue (completedAddLimbWords words carry) = value) :
    let nextWitness := witness.bindNatural runtime.nextLocation address value
    witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel heap nextWitness (semanticNaturalResult runtime value) ∧
      ValueRel nextWitness .tobject (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  have objectRelated :=
    written.naturalObjectRel_completeWithCarry_of_memoryRel wordsLength
      carryBit allocation cursorEq initialRelated finalRelated payloadInBounds
      valueEq
  exact liveHeapRel_of_freshNaturalObjectRel heapRelated allocation extension
    finalFrontier objectRelated

/-- Self-contained W6 heap construction for the completed resident Natural
writer.  Raw allocation, the exact writer history, the allocator memory
relation, and the mathematical value now suffice; the final heap and all of
its structural refinement facts are derived rather than assumed. -/
theorem WrittenLimbPrefix.liveHeapRel_completeWithCarry_of_allocateObject
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count value : Nat}
    {before allocated : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (allocation : before.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0 =
          .ok (allocated, address))
    (heapRelated : LiveHeapRel before witness runtime)
    (initialRelated : ResidentMemoryRel allocated initial.mem)
    (valueEq : limbWordsListValue (completedAddLimbWords words carry) = value) :
    ∃ heap,
      let nextWitness := witness.bindNatural runtime.nextLocation address value
      witness.Extends nextWitness ∧
        ClosureAllocationsPersistent witness nextWitness ∧
        LiveHeapRel heap nextWitness (semanticNaturalResult runtime value) ∧
        ResidentMemoryRel heap
          (completedAddStore current (UInt32.ofNat address.value) count carry).mem ∧
        ValueRel nextWitness .tobject (.word32 address)
          (.object (.heap runtime.nextLocation)) := by
  obtain ⟨heap, extension, finalValid, cursorEq, finalRelated,
      payloadInBounds⟩ :=
    written.refineMemory_completeWithCarry_of_allocateObject wordsLength
      carryBit heapRelated.frontier allocation initialRelated
  obtain ⟨witnessExtension, closureAllocationsPersistent, finalHeapRelated,
      valueRelated⟩ :=
    written.liveHeapRel_completeWithCarry_of_memoryRel wordsLength carryBit
      allocation heapRelated extension finalValid cursorEq initialRelated
      finalRelated payloadInBounds valueEq
  exact ⟨heap, witnessExtension, closureAllocationsPersistent,
    finalHeapRelated, finalRelated, valueRelated⟩

/-- Exact symbolic multi-limb result producer in checked `Nat.add`.

It allocates a natural object of `resultCount`, writes all common limbs,
checks that the writer observed the precomputed carry, materializes the final
carry limb when present, and leaves the allocated address on the stack. -/
def checkedMultiLimbProducerSource
    (left right leftFlavor rightFlavor count resultCount raw carry carryExtra
      scaled : Lean.FVarId) : List Fir.Wasm.Instruction := [
  .i32Const .uint32 ObjectKind.natural.code,
  .i32Const .uint32 bigNaturalMarker,
  .i32Const .uint32 0,
  .localGet resultCount,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.allocateName),
  .localSet raw,
  .localGet left,
  .localGet leftFlavor,
  .localGet right,
  .localGet rightFlavor,
  .localGet raw,
  .i32Const .uint32 0,
  .localGet count,
  .i32Const .uint32 0,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromName),
  .localSet carryExtra,
  .localGet carryExtra,
  .localGet carry,
  .i32Eq,
  .i32Const .uint32 0,
  .i32Eq,
  .ifElse [.unreachable] [],
  .localGet carry,
  .ifElse
    (checkedConstantLimbPartSource raw count scaled 1 0 ++
      checkedConstantLimbPartSource raw count scaled 0 4)
    [],
  .localGet raw]

/-- Fixed-local Talos spelling of `checkedMultiLimbProducerSource`. -/
def checkedMultiLimbProducerProgram (allocateIndex writeSumIndex : Nat) :
    Wasm.Program := [
  .const ObjectKind.natural.code,
  .const bigNaturalMarker,
  .const 0,
  .localGet 10,
  .call allocateIndex,
  .localSet 2,
  .localGet 0,
  .localGet 5,
  .localGet 1,
  .localGet 6,
  .localGet 2,
  .const 0,
  .localGet 9,
  .const 0,
  .call writeSumIndex,
  .localSet 16,
  .localGet 16,
  .localGet 15,
  .eq,
  .const 0,
  .eq,
  .iff 0 0 [.unreachable] [],
  .localGet 15,
  .iff 0 0 checkedCarryLimbWritesProgram [],
  .localGet 2]

/-- The actual W7 multi-limb branch is exactly the public producer above
followed by the typed, scratch-free return suffix. -/
theorem natAddFunction_checkedMultiLimb_exact_shape :
    ∃ checkedPrefix,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          (checkedPrefix ++ [
            .localGet
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1,
            .i32Const .uint32 1,
            .i32Eq,
            .ifElse
              (checkedOneLimbProducerSource
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[9]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[10]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[11]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[12]!.1 ++
                  typedNaturalReturnSource)
              (checkedMultiLimbProducerSource
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[7]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[0]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[13]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[14]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[15]!.1 ++
                  typedNaturalReturnSource)]) := by
  refine ⟨_, rfl⟩

/-- Successful call-index resolution adapts the complete multi-limb producer
to its exact Talos program.  In particular, the result is obtained from the
allocator and writer calls plus the two conditional stores; no arbitrary
physical `i32` is introduced at the object-return boundary. -/
theorem instructions_checkedMultiLimbProducerSource
    {sourceModule : Fir.Wasm.Module} {allocateIndex writeSumIndex : Nat}
    (allocateFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.allocateName) =
        some allocateIndex)
    (writeSumFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.writeSumFromName) =
        some writeSumIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction []
      (checkedMultiLimbProducerSource
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[7]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[13]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[14]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[15]!.1) =
      .ok (checkedMultiLimbProducerProgram allocateIndex writeSumIndex) := by
  have leftFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1 =
        some 0 := by decide
  have rightFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1 =
        some 1 := by decide
  have leftFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1 =
        some 5 := by decide
  have rightFlavorFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1 =
        some 6 := by decide
  have countFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[7]!.1 =
        some 9 := by decide
  have resultCountFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1 =
        some 10 := by decide
  have rawFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[0]!.1 =
        some 2 := by decide
  have carryFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[13]!.1 =
        some 15 := by decide
  have carryExtraFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[14]!.1 =
        some 16 := by decide
  have scaledFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[15]!.1 =
        some 17 := by decide
  set_option maxRecDepth 100000 in
    simp [checkedMultiLimbProducerSource, checkedMultiLimbProducerProgram,
      checkedCarryLimbWritesProgram,
      checkedConstantLimbPartSource, checkedConstantLimbPartProgram,
      checkedScale8Source, checkedScale8Program,
      FirTalos.instructions, FirTalos.instruction, allocateFound, writeSumFound,
      leftFound, rightFound, leftFlavorFound, rightFlavorFound, countFound,
      resultCountFound, rawFound, carryFound, carryExtraFound, scaledFound,
      Bind.bind, Except.bind, pure, Except.pure]

/-- Complete checked multi-limb result path, including the typed return. -/
def checkedMultiLimbResultProgram (allocateIndex writeSumIndex : Nat) :
    Wasm.Program :=
  checkedMultiLimbProducerProgram allocateIndex writeSumIndex ++
    typedNaturalReturnProgram

/-- Execution of the checked multi-limb producer when the precomputed carry
is zero.

The allocator result is written to the actual `raw` local, the writer must
return the same zero carry recorded by the prefix, and the writer's successor
store must already relate the allocated address to the mathematical Nat.
Under those operation contracts, the exact generated branch skips both the
trap and carry-limb stores and returns the canonical object word through the
typed round trip. -/
theorem wp_checkedMultiLimbResultProgram_noCarry
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {allocateIndex writeSumIndex : Nat}
    {store allocatedStore resultStore : Wasm.Store host}
    {initial afterRaw afterCarryExtra : Wasm.Locals}
    {leftWord rightWord leftFlavor rightFlavor count resultCount : UInt32}
    {address : Word32} {witness : RefinementWitness}
    {reference : Fir.LeanIR.Impure.ObjectRef} {tail : List Wasm.Value}
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorLocal : initial.get 5 = some (.i32 leftFlavor))
    (rightFlavorLocal : initial.get 6 = some (.i32 rightFlavor))
    (countLocal : initial.get 9 = some (.i32 count))
    (resultCountLocal : initial.get 10 = some (.i32 resultCount))
    (carryLocal : initial.get 15 = some (.i32 0))
    (rawSet :
      ({ initial with values :=
          (.i32 (UInt32.ofNat address.value) :: tail) }).set? 2
        (.i32 (UInt32.ofNat address.value)) = some afterRaw)
    (carryExtraSet :
      ({ afterRaw with values := .i32 0 :: tail }).set? 16 (.i32 0) =
        some afterCarryExtra)
    (allocateRun : Wasm.TerminatesWith env module allocateIndex store
      ([.i32 resultCount, .i32 0, .i32 bigNaturalMarker,
          .i32 ObjectKind.natural.code] ++ tail)
      (fun final values =>
        final = allocatedStore ∧
          values = .i32 (UInt32.ofNat address.value) :: tail))
    (writeSumRun : Wasm.TerminatesWith env module writeSumIndex allocatedStore
      ([.i32 0, .i32 count, .i32 0,
          .i32 (UInt32.ofNat address.value), .i32 rightFlavor,
          .i32 rightWord, .i32 leftFlavor, .i32 leftWord] ++ tail)
      (fun final values =>
        final = resultStore ∧ values = .i32 0 :: tail))
    (resultRelated :
      ValueRel witness .tobject (.word32 address) (.object reference)) :
    Wasm.wp module
      (checkedMultiLimbResultProgram allocateIndex writeSumIndex)
      (TypedNaturalReturnPost witness address reference resultStore tail)
      store { initial with values := tail } env := by
  have rawUpdate := FirTalos.Correctness.localUpdate_of_set? rawSet
  have carryExtraUpdate :=
    FirTalos.Correctness.localUpdate_of_set? carryExtraSet
  have initialAt (index : Nat) (value : Wasm.Value)
      (found : initial.get index = some value) (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get index = some value := by
    simpa using found
  have afterRawAt (index : Nat) (value : Wasm.Value)
      (different : index ≠ 2) (found : initial.get index = some value)
      (values : List Wasm.Value) :
      ({ afterRaw with values } : Wasm.Locals).get index = some value := by
    change afterRaw.get index = some value
    rw [rawUpdate.2 different]
    simpa using found
  have afterCarryAt (index : Nat) (value : Wasm.Value)
      (differentFromCarryExtra : index ≠ 16)
      (found : afterRaw.get index = some value) (values : List Wasm.Value) :
      ({ afterCarryExtra with values } : Wasm.Locals).get index = some value := by
    change afterCarryExtra.get index = some value
    rw [carryExtraUpdate.2 differentFromCarryExtra]
    simpa using found
  have rawAfter : afterRaw.get 2 =
      some (.i32 (UInt32.ofNat address.value)) := by
    simpa using rawUpdate.1
  have rawAfterAt (values : List Wasm.Value) :
      ({ afterRaw with values } : Wasm.Locals).get 2 =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa using rawAfter
  have carryExtraAfter : afterCarryExtra.get 16 = some (.i32 0) := by
    simpa using carryExtraUpdate.1
  have carryExtraAt (values : List Wasm.Value) :
      ({ afterCarryExtra with values } : Wasm.Locals).get 16 =
        some (.i32 0) := by
    simpa using carryExtraAfter
  have rawFinal : afterCarryExtra.get 2 =
      some (.i32 (UInt32.ofNat address.value)) := by
    rw [carryExtraUpdate.2 (by decide)]
    exact rawAfter
  have carryFinal : afterCarryExtra.get 15 = some (.i32 0) := by
    apply afterCarryAt 15 (.i32 0) (by decide)
    rw [rawUpdate.2 (by decide)]
    exact carryLocal
  have carryFinalAt (values : List Wasm.Value) :
      ({ afterCarryExtra with values } : Wasm.Locals).get 15 =
        some (.i32 0) := by
    simpa using carryFinal
  have rawFinalAt (values : List Wasm.Value) :
      ({ afterCarryExtra with values } : Wasm.Locals).get 2 =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa using rawFinal
  unfold checkedMultiLimbResultProgram checkedMultiLimbProducerProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_const_cons,
    Wasm.wp_localGet_cons,
    initialAt 10 (.i32 resultCount) resultCountLocal]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 resultCount, .i32 0, .i32 bigNaturalMarker,
        .i32 ObjectKind.natural.code])
      (tail := tail)
      (locals := { initial with values :=
        (.i32 (UInt32.ofNat address.value) :: tail) })
      (updated := afterRaw)
      (physicalResult := .i32 (UInt32.ofNat address.value))
      (callRun := allocateRun) (targetSet := rawSet)
  simp only [Wasm.wp_localGet_cons,
    afterRawAt 0 (.i32 leftWord) (by decide) leftLocal,
    afterRawAt 5 (.i32 leftFlavor) (by decide) leftFlavorLocal,
    afterRawAt 1 (.i32 rightWord) (by decide) rightLocal,
    afterRawAt 6 (.i32 rightFlavor) (by decide) rightFlavorLocal,
    rawAfterAt,
    Wasm.wp_const_cons,
    afterRawAt 9 (.i32 count) (by decide) countLocal]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 count, .i32 0,
        .i32 (UInt32.ofNat address.value), .i32 rightFlavor,
        .i32 rightWord, .i32 leftFlavor, .i32 leftWord])
      (tail := tail)
      (locals := { afterRaw with values := .i32 0 :: tail })
      (updated := afterCarryExtra) (physicalResult := .i32 0)
      (callRun := writeSumRun) (targetSet := carryExtraSet)
  simp only [Wasm.wp_localGet_cons, carryExtraAt, carryFinalAt,
    Wasm.wp_eq_cons, Wasm.wp_const_cons]
  apply Wasm.wp_iff_cons rfl
  simp only [if_pos True.intro,
    if_neg (by decide : (1 : UInt32) ≠ 0),
    if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  rw [Wasm.wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  simp only [Wasm.wp_localGet_cons, carryFinalAt]
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  rw [Wasm.wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  simp only [Wasm.wp_localGet_cons, rawFinalAt]
  exact wp_typedNaturalReturnProgram resultRelated

/-- Low-level postcondition of the two direct stores that materialize a final
carry limb.  It deliberately says nothing about Lean object validity: it
records only the exact successor store and preservation of the allocator's
raw address local.  The concrete allocation theorem supplies the semantic Nat
relation separately. -/
def CarryLimbWritesPost (finalStore : Wasm.Store host) (address : Word32) :
    Wasm.Assertion host :=
  fun continuation =>
    ∃ finalLocals,
      continuation = .Fallthrough finalStore finalLocals ∧
        finalLocals.get 2 = some (.i32 (UInt32.ofNat address.value))

/-- The exact two stores in the nonzero-carry branch execute without a host
call and preserve the allocator's raw address local.

The hypotheses are solely the six checked scratch-local updates and the two
ordinary Wasm bounds checks.  The result is the precise low-then-high memory
successor; it still makes no claim that those bytes form a valid Lean Nat. -/
theorem wp_checkedCarryLimbWritesProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host}
    {initial lowFirst lowSecond lowThird highFirst highSecond highThird :
      Wasm.Locals}
    {address : Word32} {count : UInt32} {tail : List Wasm.Value}
    (rawLocal : initial.get 2 =
      some (.i32 (UInt32.ofNat address.value)))
    (countLocal : initial.get 9 = some (.i32 count))
    (lowFirstSet :
      ({ initial with values := .i32 (count + count) :: tail }).set? 17
        (.i32 (count + count)) = some lowFirst)
    (lowSecondSet :
      ({ lowFirst with values :=
          (.i32 (count + count + (count + count)) :: tail) }).set? 17
        (.i32 (count + count + (count + count))) = some lowSecond)
    (lowThirdSet :
      ({ lowSecond with values := .i32 (checkedScale8Word count) :: tail }).set?
        17 (.i32 (checkedScale8Word count)) = some lowThird)
    (highFirstSet :
      ({ lowThird with values := .i32 (count + count) :: tail }).set? 17
        (.i32 (count + count)) = some highFirst)
    (highSecondSet :
      ({ highFirst with values :=
          (.i32 (count + count + (count + count)) :: tail) }).set? 17
        (.i32 (count + count + (count + count))) = some highSecond)
    (highThirdSet :
      ({ highSecond with values := .i32 (checkedScale8Word count) :: tail }).set?
        17 (.i32 (checkedScale8Word count)) = some highThird)
    (lowInBounds :
      ¬(checkedLimbBase (UInt32.ofNat address.value) count).toNat +
          (UInt32.ofNat 0).toNat + 4 > store.mem.pages * 65536)
    (highInBounds :
      ¬(checkedLimbBase (UInt32.ofNat address.value) count).toNat +
          (UInt32.ofNat 4).toNat + 4 >
        (checkedCarryLowStore store (UInt32.ofNat address.value) count).mem.pages *
          65536) :
    Wasm.wp module checkedCarryLimbWritesProgram
      (CarryLimbWritesPost
        (checkedCarryFinalStore store (UInt32.ofNat address.value) count)
        address)
      store { initial with values := tail } env := by
  have lowFirstUpdate :=
    FirTalos.Correctness.localUpdate_of_set? lowFirstSet
  have lowSecondUpdate :=
    FirTalos.Correctness.localUpdate_of_set? lowSecondSet
  have lowThirdUpdate :=
    FirTalos.Correctness.localUpdate_of_set? lowThirdSet
  have highFirstUpdate :=
    FirTalos.Correctness.localUpdate_of_set? highFirstSet
  have highSecondUpdate :=
    FirTalos.Correctness.localUpdate_of_set? highSecondSet
  have highThirdUpdate :=
    FirTalos.Correctness.localUpdate_of_set? highThirdSet
  have preservedAfterLow {index : Nat} {value : Wasm.Value}
      (different : index ≠ 17)
      (found : initial.get index = some value) :
      lowThird.get index = some value := by
    calc
      _ = ({ lowSecond with values :=
          (.i32 (checkedScale8Word count) :: tail) } : Wasm.Locals).get index :=
        lowThirdUpdate.2 different
      _ = lowSecond.get index := rfl
      _ = ({ lowFirst with values :=
          (.i32 (count + count + (count + count)) :: tail) } :
          Wasm.Locals).get index := lowSecondUpdate.2 different
      _ = lowFirst.get index := rfl
      _ = ({ initial with values := .i32 (count + count) :: tail } :
          Wasm.Locals).get index := lowFirstUpdate.2 different
      _ = initial.get index := rfl
      _ = some value := found
  have rawAfterHigh : highThird.get 2 =
      some (.i32 (UInt32.ofNat address.value)) := by
    calc
      _ = ({ highSecond with values :=
          (.i32 (checkedScale8Word count) :: tail) } : Wasm.Locals).get 2 :=
        highThirdUpdate.2 (by decide)
      _ = highSecond.get 2 := rfl
      _ = ({ highFirst with values :=
          (.i32 (count + count + (count + count)) :: tail) } :
          Wasm.Locals).get 2 := highSecondUpdate.2 (by decide)
      _ = highFirst.get 2 := rfl
      _ = ({ lowThird with values := .i32 (count + count) :: tail } :
          Wasm.Locals).get 2 := highFirstUpdate.2 (by decide)
      _ = lowThird.get 2 := rfl
      _ = some (.i32 (UInt32.ofNat address.value)) :=
        preservedAfterLow (by decide) rawLocal
  have countAfterLow : lowThird.get 9 = some (.i32 count) :=
    preservedAfterLow (by decide) countLocal
  unfold checkedCarryLimbWritesProgram
  apply wp_checkedConstantLimbPartProgram (by decide) rawLocal countLocal
    lowFirstSet lowSecondSet lowThirdSet lowInBounds
  apply wp_checkedConstantLimbPartProgram (by decide)
    (preservedAfterLow (by decide) rawLocal) countAfterLow
    highFirstSet highSecondSet highThirdSet highInBounds
  rw [Wasm.wp_nil]
  refine ⟨{ highThird with values := tail }, ?_, ?_⟩
  · simp [checkedCarryFinalStore]
  · simpa using rawAfterHigh

/-- Execution of the checked multi-limb producer when the carry scan found a
new most-significant limb.

The actual allocator and writer calls must agree on the nonzero carry.  The
remaining premise is confined to the exact two direct stores and states only
their physical store transition plus preservation of `raw`; the canonical Nat
`ValueRel` is an independent premise and is consumed only by the typed return.
Thus this composition theorem cannot type an arbitrary writer result as an
object. -/
theorem wp_checkedMultiLimbResultProgram_withCarry
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {allocateIndex writeSumIndex : Nat}
    {store allocatedStore writerStore finalStore : Wasm.Store host}
    {initial afterRaw afterCarryExtra : Wasm.Locals}
    {leftWord rightWord leftFlavor rightFlavor count resultCount carry : UInt32}
    {address : Word32} {witness : RefinementWitness}
    {reference : Fir.LeanIR.Impure.ObjectRef} {tail : List Wasm.Value}
    (carryNonzero : carry ≠ 0)
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorLocal : initial.get 5 = some (.i32 leftFlavor))
    (rightFlavorLocal : initial.get 6 = some (.i32 rightFlavor))
    (countLocal : initial.get 9 = some (.i32 count))
    (resultCountLocal : initial.get 10 = some (.i32 resultCount))
    (carryLocal : initial.get 15 = some (.i32 carry))
    (rawSet :
      ({ initial with values :=
          (.i32 (UInt32.ofNat address.value) :: tail) }).set? 2
        (.i32 (UInt32.ofNat address.value)) = some afterRaw)
    (carryExtraSet :
      ({ afterRaw with values := .i32 carry :: tail }).set? 16
        (.i32 carry) = some afterCarryExtra)
    (allocateRun : Wasm.TerminatesWith env module allocateIndex store
      ([.i32 resultCount, .i32 0, .i32 bigNaturalMarker,
          .i32 ObjectKind.natural.code] ++ tail)
      (fun final values =>
        final = allocatedStore ∧
          values = .i32 (UInt32.ofNat address.value) :: tail))
    (writeSumRun : Wasm.TerminatesWith env module writeSumIndex allocatedStore
      ([.i32 0, .i32 count, .i32 0,
          .i32 (UInt32.ofNat address.value), .i32 rightFlavor,
          .i32 rightWord, .i32 leftFlavor, .i32 leftWord] ++ tail)
      (fun final values =>
        final = writerStore ∧ values = .i32 carry :: tail))
    (carryLimbWritesRun :
      Wasm.wp module checkedCarryLimbWritesProgram
        (CarryLimbWritesPost finalStore address) writerStore
        { afterCarryExtra with values := tail } env)
    (resultRelated :
      ValueRel witness .tobject (.word32 address) (.object reference)) :
    Wasm.wp module
      (checkedMultiLimbResultProgram allocateIndex writeSumIndex)
      (TypedNaturalReturnPost witness address reference finalStore tail)
      store { initial with values := tail } env := by
  have rawUpdate := FirTalos.Correctness.localUpdate_of_set? rawSet
  have carryExtraUpdate :=
    FirTalos.Correctness.localUpdate_of_set? carryExtraSet
  have initialAt (index : Nat) (value : Wasm.Value)
      (found : initial.get index = some value) (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get index = some value := by
    simpa using found
  have afterRawAt (index : Nat) (value : Wasm.Value)
      (different : index ≠ 2) (found : initial.get index = some value)
      (values : List Wasm.Value) :
      ({ afterRaw with values } : Wasm.Locals).get index = some value := by
    change afterRaw.get index = some value
    rw [rawUpdate.2 different]
    simpa using found
  have afterCarryAt (index : Nat) (value : Wasm.Value)
      (differentFromCarryExtra : index ≠ 16)
      (found : afterRaw.get index = some value) (values : List Wasm.Value) :
      ({ afterCarryExtra with values } : Wasm.Locals).get index = some value := by
    change afterCarryExtra.get index = some value
    rw [carryExtraUpdate.2 differentFromCarryExtra]
    simpa using found
  have rawAfter : afterRaw.get 2 =
      some (.i32 (UInt32.ofNat address.value)) := by
    simpa using rawUpdate.1
  have rawAfterAt (values : List Wasm.Value) :
      ({ afterRaw with values } : Wasm.Locals).get 2 =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa using rawAfter
  have carryExtraAfter : afterCarryExtra.get 16 = some (.i32 carry) := by
    simpa using carryExtraUpdate.1
  have carryExtraAt (values : List Wasm.Value) :
      ({ afterCarryExtra with values } : Wasm.Locals).get 16 =
        some (.i32 carry) := by
    simpa using carryExtraAfter
  have carryAfterRaw : afterRaw.get 15 = some (.i32 carry) := by
    rw [rawUpdate.2 (by decide)]
    exact carryLocal
  have carryFinal : afterCarryExtra.get 15 = some (.i32 carry) := by
    apply afterCarryAt 15 (.i32 carry) (by decide)
    exact carryAfterRaw
  have carryFinalAt (values : List Wasm.Value) :
      ({ afterCarryExtra with values } : Wasm.Locals).get 15 =
        some (.i32 carry) := by
    simpa using carryFinal
  unfold checkedMultiLimbResultProgram checkedMultiLimbProducerProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_const_cons,
    Wasm.wp_localGet_cons,
    initialAt 10 (.i32 resultCount) resultCountLocal]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 resultCount, .i32 0, .i32 bigNaturalMarker,
        .i32 ObjectKind.natural.code])
      (tail := tail)
      (locals := { initial with values :=
        (.i32 (UInt32.ofNat address.value) :: tail) })
      (updated := afterRaw)
      (physicalResult := .i32 (UInt32.ofNat address.value))
      (callRun := allocateRun) (targetSet := rawSet)
  simp only [Wasm.wp_localGet_cons,
    afterRawAt 0 (.i32 leftWord) (by decide) leftLocal,
    afterRawAt 5 (.i32 leftFlavor) (by decide) leftFlavorLocal,
    afterRawAt 1 (.i32 rightWord) (by decide) rightLocal,
    afterRawAt 6 (.i32 rightFlavor) (by decide) rightFlavorLocal,
    rawAfterAt,
    Wasm.wp_const_cons,
    afterRawAt 9 (.i32 count) (by decide) countLocal]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 count, .i32 0,
        .i32 (UInt32.ofNat address.value), .i32 rightFlavor,
        .i32 rightWord, .i32 leftFlavor, .i32 leftWord])
      (tail := tail)
      (locals := { afterRaw with values := .i32 carry :: tail })
      (updated := afterCarryExtra) (physicalResult := .i32 carry)
      (callRun := writeSumRun) (targetSet := carryExtraSet)
  simp only [Wasm.wp_localGet_cons, carryExtraAt, carryFinalAt,
    Wasm.wp_eq_cons, Wasm.wp_const_cons]
  apply Wasm.wp_iff_cons rfl
  simp only [if_pos True.intro,
    if_neg (by decide : (1 : UInt32) ≠ 0),
    if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  rw [Wasm.wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  simp only [Wasm.wp_localGet_cons, carryFinalAt]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos carryNonzero]
  apply Wasm.wp.conseq (h := carryLimbWritesRun)
  intro continuation completed
  rcases completed with ⟨finalLocals, rfl, rawFinal⟩
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons]
  have rawFinalAt :
      ({ finalLocals with values := tail } : Wasm.Locals).get 2 =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa using rawFinal
  rw [rawFinalAt]
  exact wp_typedNaturalReturnProgram resultRelated

/-- Concrete canonical-result closure of the carry-producing multi-limb
branch.

The two direct carry stores are discharged by
`wp_checkedCarryLimbWritesProgram`; the semantic result is independently
derived from `allocateNatural_heap_liveHeapRel`.  This is the complete
physical/semantic composition boundary for this branch: successful Wasm
writes alone never justify an object value. -/
theorem wp_checkedMultiLimbResultProgram_withCarry_of_allocateNatural
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {allocateIndex writeSumIndex : Nat}
    {store allocatedStore writerStore : Wasm.Store host}
    {initial afterRaw afterCarryExtra : Wasm.Locals}
    {lowFirst lowSecond lowThird highFirst highSecond highThird : Wasm.Locals}
    {leftWord rightWord leftFlavor rightFlavor count resultCount carry : UInt32}
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState} {value : Nat}
    {address : Word32} {tail : List Wasm.Value}
    (carryNonzero : carry ≠ 0)
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorLocal : initial.get 5 = some (.i32 leftFlavor))
    (rightFlavorLocal : initial.get 6 = some (.i32 rightFlavor))
    (countLocal : initial.get 9 = some (.i32 count))
    (resultCountLocal : initial.get 10 = some (.i32 resultCount))
    (carryLocal : initial.get 15 = some (.i32 carry))
    (rawSet :
      ({ initial with values :=
          (.i32 (UInt32.ofNat address.value) :: tail) }).set? 2
        (.i32 (UInt32.ofNat address.value)) = some afterRaw)
    (carryExtraSet :
      ({ afterRaw with values := .i32 carry :: tail }).set? 16
        (.i32 carry) = some afterCarryExtra)
    (allocateRun : Wasm.TerminatesWith env module allocateIndex store
      ([.i32 resultCount, .i32 0, .i32 bigNaturalMarker,
          .i32 ObjectKind.natural.code] ++ tail)
      (fun final values =>
        final = allocatedStore ∧
          values = .i32 (UInt32.ofNat address.value) :: tail))
    (writeSumRun : Wasm.TerminatesWith env module writeSumIndex allocatedStore
      ([.i32 0, .i32 count, .i32 0,
          .i32 (UInt32.ofNat address.value), .i32 rightFlavor,
          .i32 rightWord, .i32 leftFlavor, .i32 leftWord] ++ tail)
      (fun final values =>
        final = writerStore ∧ values = .i32 carry :: tail))
    (lowFirstSet :
      ({ afterCarryExtra with values := .i32 (count + count) :: tail }).set? 17
        (.i32 (count + count)) = some lowFirst)
    (lowSecondSet :
      ({ lowFirst with values :=
          (.i32 (count + count + (count + count)) :: tail) }).set? 17
        (.i32 (count + count + (count + count))) = some lowSecond)
    (lowThirdSet :
      ({ lowSecond with values := .i32 (checkedScale8Word count) :: tail }).set?
        17 (.i32 (checkedScale8Word count)) = some lowThird)
    (highFirstSet :
      ({ lowThird with values := .i32 (count + count) :: tail }).set? 17
        (.i32 (count + count)) = some highFirst)
    (highSecondSet :
      ({ highFirst with values :=
          (.i32 (count + count + (count + count)) :: tail) }).set? 17
        (.i32 (count + count + (count + count))) = some highSecond)
    (highThirdSet :
      ({ highSecond with values := .i32 (checkedScale8Word count) :: tail }).set?
        17 (.i32 (checkedScale8Word count)) = some highThird)
    (lowInBounds :
      ¬(checkedLimbBase (UInt32.ofNat address.value) count).toNat +
          (UInt32.ofNat 0).toNat + 4 > writerStore.mem.pages * 65536)
    (highInBounds :
      ¬(checkedLimbBase (UInt32.ofNat address.value) count).toNat +
          (UInt32.ofNat 4).toNat + 4 >
        (checkedCarryLowStore writerStore (UInt32.ofNat address.value)
          count).mem.pages * 65536)
    (heapRelated : LiveHeapRel before witness runtime)
    (large : Fir.LeanIR.Impure.maxTaggedPayload < value)
    (allocated : allocateNatural before value = .ok (after, address))
    (memoryRelated : ResidentMemoryRel after
      (checkedCarryFinalStore writerStore (UInt32.ofNat address.value)
        count).mem) :
    let nextWitness :=
      witness.bindNatural runtime.nextLocation address value
    LiveHeapRel after nextWitness (semanticNaturalResult runtime value) ∧
      ResidentMemoryRel after
        (checkedCarryFinalStore writerStore (UInt32.ofNat address.value)
          count).mem ∧
      Wasm.wp module
        (checkedMultiLimbResultProgram allocateIndex writeSumIndex)
        (TypedNaturalReturnPost nextWitness address
          (.heap runtime.nextLocation)
          (checkedCarryFinalStore writerStore
            (UInt32.ofNat address.value) count) tail)
        store { initial with values := tail } env := by
  dsimp only
  have rawUpdate := FirTalos.Correctness.localUpdate_of_set? rawSet
  have carryExtraUpdate :=
    FirTalos.Correctness.localUpdate_of_set? carryExtraSet
  have rawAfterRaw : afterRaw.get 2 =
      some (.i32 (UInt32.ofNat address.value)) := by
    simpa using rawUpdate.1
  have rawAfterCarry : afterCarryExtra.get 2 =
      some (.i32 (UInt32.ofNat address.value)) := by
    rw [carryExtraUpdate.2 (by decide)]
    exact rawAfterRaw
  have countAfterRaw : afterRaw.get 9 = some (.i32 count) := by
    rw [rawUpdate.2 (by decide)]
    simpa using countLocal
  have countAfterCarry : afterCarryExtra.get 9 = some (.i32 count) := by
    rw [carryExtraUpdate.2 (by decide)]
    exact countAfterRaw
  have carryWrites := wp_checkedCarryLimbWritesProgram
    (module := module) (env := env) (store := writerStore)
    (initial := afterCarryExtra) (address := address) (count := count)
    (tail := tail) rawAfterCarry countAfterCarry lowFirstSet lowSecondSet
    lowThirdSet highFirstSet highSecondSet highThirdSet lowInBounds highInBounds
  obtain ⟨nextHeapRelated, valueRelated⟩ :=
    allocateNatural_heap_liveHeapRel before after witness runtime value address
      heapRelated large allocated
  refine ⟨nextHeapRelated, memoryRelated, ?_⟩
  exact wp_checkedMultiLimbResultProgram_withCarry carryNonzero leftLocal
    rightLocal leftFlavorLocal rightFlavorLocal countLocal resultCountLocal
    carryLocal rawSet carryExtraSet allocateRun writeSumRun carryWrites
    valueRelated

/-- Concrete canonical-result closure of the zero-carry multi-limb branch.

The physical allocator/writer calls still expose their exact Talos stores,
but the returned object's type is derived from the ordinary W6
`allocateNatural` transition.  For a genuinely large value this fixes the
semantic reference to the fresh heap location and proves the final heap live;
there is no independent object-typing premise. -/
theorem wp_checkedMultiLimbResultProgram_noCarry_of_allocateNatural
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {allocateIndex writeSumIndex : Nat}
    {store allocatedStore resultStore : Wasm.Store host}
    {initial afterRaw afterCarryExtra : Wasm.Locals}
    {leftWord rightWord leftFlavor rightFlavor count resultCount : UInt32}
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState} {value : Nat}
    {address : Word32} {tail : List Wasm.Value}
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorLocal : initial.get 5 = some (.i32 leftFlavor))
    (rightFlavorLocal : initial.get 6 = some (.i32 rightFlavor))
    (countLocal : initial.get 9 = some (.i32 count))
    (resultCountLocal : initial.get 10 = some (.i32 resultCount))
    (carryLocal : initial.get 15 = some (.i32 0))
    (rawSet :
      ({ initial with values :=
          (.i32 (UInt32.ofNat address.value) :: tail) }).set? 2
        (.i32 (UInt32.ofNat address.value)) = some afterRaw)
    (carryExtraSet :
      ({ afterRaw with values := .i32 0 :: tail }).set? 16 (.i32 0) =
        some afterCarryExtra)
    (allocateRun : Wasm.TerminatesWith env module allocateIndex store
      ([.i32 resultCount, .i32 0, .i32 bigNaturalMarker,
          .i32 ObjectKind.natural.code] ++ tail)
      (fun final values =>
        final = allocatedStore ∧
          values = .i32 (UInt32.ofNat address.value) :: tail))
    (writeSumRun : Wasm.TerminatesWith env module writeSumIndex allocatedStore
      ([.i32 0, .i32 count, .i32 0,
          .i32 (UInt32.ofNat address.value), .i32 rightFlavor,
          .i32 rightWord, .i32 leftFlavor, .i32 leftWord] ++ tail)
      (fun final values =>
        final = resultStore ∧ values = .i32 0 :: tail))
    (heapRelated : LiveHeapRel before witness runtime)
    (large : Fir.LeanIR.Impure.maxTaggedPayload < value)
    (allocated : allocateNatural before value = .ok (after, address))
    (memoryRelated : ResidentMemoryRel after resultStore.mem) :
    let nextWitness :=
      witness.bindNatural runtime.nextLocation address value
    LiveHeapRel after nextWitness (semanticNaturalResult runtime value) ∧
      ResidentMemoryRel after resultStore.mem ∧
      Wasm.wp module
        (checkedMultiLimbResultProgram allocateIndex writeSumIndex)
        (TypedNaturalReturnPost nextWitness address
          (.heap runtime.nextLocation) resultStore tail)
        store { initial with values := tail } env := by
  dsimp only
  obtain ⟨nextHeapRelated, valueRelated⟩ :=
    allocateNatural_heap_liveHeapRel before after witness runtime value address
      heapRelated large allocated
  refine ⟨nextHeapRelated, memoryRelated, ?_⟩
  exact wp_checkedMultiLimbResultProgram_noCarry leftLocal rightLocal
    leftFlavorLocal rightFlavorLocal countLocal resultCountLocal carryLocal
    rawSet carryExtraSet allocateRun writeSumRun valueRelated

/-- Complete checked one-limb result path, including the typed return suffix. -/
def checkedOneLimbResultProgram (magnitudeLowIndex magnitudeHighIndex
    naturalSumIndex : Nat) : Wasm.Program :=
  checkedOneLimbProducerProgram magnitudeLowIndex magnitudeHighIndex
    naturalSumIndex ++ typedNaturalReturnProgram

/-- The checked one-limb path is not an arbitrary physical cast.  Four
read-only magnitude calls establish the exact 64-bit inputs; the semantically
typed `naturalSum` call supplies a related canonical Nat word in its successor
store; only then may the word cross the scratch-free object return suffix. -/
theorem wp_checkedOneLimbResultProgram
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {magnitudeLowIndex magnitudeHighIndex naturalSumIndex : Nat}
    {store resultStore : Wasm.Store host}
    {initial afterLeftLow afterLeftHigh afterRightLow afterRightHigh :
      Wasm.Locals}
    {leftWord rightWord leftFlavor rightFlavor : UInt32}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {resultWitness : RefinementWitness} {resultWord : Word32}
    {resultReference : Fir.LeanIR.Impure.ObjectRef}
    {tail : List Wasm.Value}
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorLocal : initial.get 5 = some (.i32 leftFlavor))
    (rightFlavorLocal : initial.get 6 = some (.i32 rightFlavor))
    (leftLowSet :
      ({ initial with values := .i32 leftLow :: tail }).set? 11
        (.i32 leftLow) = some afterLeftLow)
    (leftHighSet :
      ({ afterLeftLow with values := .i32 leftHigh :: tail }).set? 12
        (.i32 leftHigh) = some afterLeftHigh)
    (rightLowSet :
      ({ afterLeftHigh with values := .i32 rightLow :: tail }).set? 13
        (.i32 rightLow) = some afterRightLow)
    (rightHighSet :
      ({ afterRightLow with values := .i32 rightHigh :: tail }).set? 14
        (.i32 rightHigh) = some afterRightHigh)
    (leftLowRun : ∀ callTail,
      Wasm.TerminatesWith env module magnitudeLowIndex store
        ([.i32 0, .i32 leftFlavor, .i32 leftWord] ++ callTail)
        (fun final values =>
          final = store ∧ values = .i32 leftLow :: callTail))
    (leftHighRun : ∀ callTail,
      Wasm.TerminatesWith env module magnitudeHighIndex store
        ([.i32 0, .i32 leftFlavor, .i32 leftWord] ++ callTail)
        (fun final values =>
          final = store ∧ values = .i32 leftHigh :: callTail))
    (rightLowRun : ∀ callTail,
      Wasm.TerminatesWith env module magnitudeLowIndex store
        ([.i32 0, .i32 rightFlavor, .i32 rightWord] ++ callTail)
        (fun final values =>
          final = store ∧ values = .i32 rightLow :: callTail))
    (rightHighRun : ∀ callTail,
      Wasm.TerminatesWith env module magnitudeHighIndex store
        ([.i32 0, .i32 rightFlavor, .i32 rightWord] ++ callTail)
        (fun final values =>
          final = store ∧ values = .i32 rightHigh :: callTail))
    (naturalSumRun : ∀ callTail,
      Wasm.TerminatesWith env module naturalSumIndex store
        ([.i32 rightHigh, .i32 rightLow, .i32 leftHigh, .i32 leftLow] ++
          callTail)
        (fun final values =>
          final = resultStore ∧
            values = .i32 (UInt32.ofNat resultWord.value) :: callTail))
    (resultRelated :
      ValueRel resultWitness .tobject (.word32 resultWord)
        (.object resultReference)) :
    Wasm.wp module
      (checkedOneLimbResultProgram magnitudeLowIndex magnitudeHighIndex
        naturalSumIndex)
      (TypedNaturalReturnPost resultWitness resultWord resultReference
        resultStore tail)
      store { initial with values := tail } env := by
  have leftLowUpdate :=
    FirTalos.Correctness.localUpdate_of_set? leftLowSet
  have leftHighUpdate :=
    FirTalos.Correctness.localUpdate_of_set? leftHighSet
  have rightLowUpdate :=
    FirTalos.Correctness.localUpdate_of_set? rightLowSet
  have rightHighUpdate :=
    FirTalos.Correctness.localUpdate_of_set? rightHighSet
  have leftAtInitial (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get 0 =
        some (.i32 leftWord) := by simpa using leftLocal
  have leftFlavorAtInitial (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get 5 =
        some (.i32 leftFlavor) := by simpa using leftFlavorLocal
  have leftAtAfterLow (values : List Wasm.Value) :
      ({ afterLeftLow with values } : Wasm.Locals).get 0 =
        some (.i32 leftWord) := by
    rw [show ({ afterLeftLow with values } : Wasm.Locals).get 0 =
      afterLeftLow.get 0 by rfl, leftLowUpdate.2 (by decide)]
    simpa using leftLocal
  have leftFlavorAtAfterLow (values : List Wasm.Value) :
      ({ afterLeftLow with values } : Wasm.Locals).get 5 =
        some (.i32 leftFlavor) := by
    rw [show ({ afterLeftLow with values } : Wasm.Locals).get 5 =
      afterLeftLow.get 5 by rfl, leftLowUpdate.2 (by decide)]
    simpa using leftFlavorLocal
  have rightAtAfterLeftHigh (values : List Wasm.Value) :
      ({ afterLeftHigh with values } : Wasm.Locals).get 1 =
        some (.i32 rightWord) := by
    calc
      _ = afterLeftHigh.get 1 := rfl
      _ = ({ afterLeftLow with values := .i32 leftHigh :: tail } :
          Wasm.Locals).get 1 := leftHighUpdate.2 (by decide)
      _ = afterLeftLow.get 1 := rfl
      _ = ({ initial with values := .i32 leftLow :: tail } :
          Wasm.Locals).get 1 := leftLowUpdate.2 (by decide)
      _ = initial.get 1 := rfl
      _ = some (.i32 rightWord) := rightLocal
  have rightFlavorAtAfterLeftHigh (values : List Wasm.Value) :
      ({ afterLeftHigh with values } : Wasm.Locals).get 6 =
        some (.i32 rightFlavor) := by
    calc
      _ = afterLeftHigh.get 6 := rfl
      _ = ({ afterLeftLow with values := .i32 leftHigh :: tail } :
          Wasm.Locals).get 6 := leftHighUpdate.2 (by decide)
      _ = afterLeftLow.get 6 := rfl
      _ = ({ initial with values := .i32 leftLow :: tail } :
          Wasm.Locals).get 6 := leftLowUpdate.2 (by decide)
      _ = initial.get 6 := rfl
      _ = some (.i32 rightFlavor) := rightFlavorLocal
  have rightAtAfterRightLow (values : List Wasm.Value) :
      ({ afterRightLow with values } : Wasm.Locals).get 1 =
        some (.i32 rightWord) := by
    calc
      _ = afterRightLow.get 1 := rfl
      _ = ({ afterLeftHigh with values := .i32 rightLow :: tail } :
          Wasm.Locals).get 1 := rightLowUpdate.2 (by decide)
      _ = afterLeftHigh.get 1 := rfl
      _ = ({ afterLeftLow with values := .i32 leftHigh :: tail } :
          Wasm.Locals).get 1 := leftHighUpdate.2 (by decide)
      _ = afterLeftLow.get 1 := rfl
      _ = ({ initial with values := .i32 leftLow :: tail } :
          Wasm.Locals).get 1 := leftLowUpdate.2 (by decide)
      _ = initial.get 1 := rfl
      _ = some (.i32 rightWord) := rightLocal
  have rightFlavorAtAfterRightLow (values : List Wasm.Value) :
      ({ afterRightLow with values } : Wasm.Locals).get 6 =
        some (.i32 rightFlavor) := by
    calc
      _ = afterRightLow.get 6 := rfl
      _ = ({ afterLeftHigh with values := .i32 rightLow :: tail } :
          Wasm.Locals).get 6 := rightLowUpdate.2 (by decide)
      _ = afterLeftHigh.get 6 := rfl
      _ = ({ afterLeftLow with values := .i32 leftHigh :: tail } :
          Wasm.Locals).get 6 := leftHighUpdate.2 (by decide)
      _ = afterLeftLow.get 6 := rfl
      _ = ({ initial with values := .i32 leftLow :: tail } :
          Wasm.Locals).get 6 := leftLowUpdate.2 (by decide)
      _ = initial.get 6 := rfl
      _ = some (.i32 rightFlavor) := rightFlavorLocal
  have leftLowAtEnd (values : List Wasm.Value) :
      ({ afterRightHigh with values } : Wasm.Locals).get 11 =
        some (.i32 leftLow) := by
    calc
      _ = afterRightHigh.get 11 := rfl
      _ = ({ afterRightLow with values := .i32 rightHigh :: tail } :
          Wasm.Locals).get 11 := rightHighUpdate.2 (by decide)
      _ = afterRightLow.get 11 := rfl
      _ = ({ afterLeftHigh with values := .i32 rightLow :: tail } :
          Wasm.Locals).get 11 := rightLowUpdate.2 (by decide)
      _ = afterLeftHigh.get 11 := rfl
      _ = ({ afterLeftLow with values := .i32 leftHigh :: tail } :
          Wasm.Locals).get 11 := leftHighUpdate.2 (by decide)
      _ = afterLeftLow.get 11 := rfl
      _ = some (.i32 leftLow) := leftLowUpdate.1
  have leftHighAtEnd (values : List Wasm.Value) :
      ({ afterRightHigh with values } : Wasm.Locals).get 12 =
        some (.i32 leftHigh) := by
    calc
      _ = afterRightHigh.get 12 := rfl
      _ = ({ afterRightLow with values := .i32 rightHigh :: tail } :
          Wasm.Locals).get 12 := rightHighUpdate.2 (by decide)
      _ = afterRightLow.get 12 := rfl
      _ = ({ afterLeftHigh with values := .i32 rightLow :: tail } :
          Wasm.Locals).get 12 := rightLowUpdate.2 (by decide)
      _ = afterLeftHigh.get 12 := rfl
      _ = some (.i32 leftHigh) := leftHighUpdate.1
  have rightLowAtEnd (values : List Wasm.Value) :
      ({ afterRightHigh with values } : Wasm.Locals).get 13 =
        some (.i32 rightLow) := by
    calc
      _ = afterRightHigh.get 13 := rfl
      _ = ({ afterRightLow with values := .i32 rightHigh :: tail } :
          Wasm.Locals).get 13 := rightHighUpdate.2 (by decide)
      _ = afterRightLow.get 13 := rfl
      _ = some (.i32 rightLow) := rightLowUpdate.1
  have rightHighAtEnd (values : List Wasm.Value) :
      ({ afterRightHigh with values } : Wasm.Locals).get 14 =
        some (.i32 rightHigh) := by
    simpa using rightHighUpdate.1
  unfold checkedOneLimbResultProgram checkedOneLimbProducerProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    leftAtInitial, leftFlavorAtInitial, Wasm.wp_const_cons]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 leftFlavor, .i32 leftWord])
      (tail := tail)
      (locals := { initial with values := .i32 leftLow :: tail })
      (updated := afterLeftLow) (physicalResult := .i32 leftLow)
      (callRun := leftLowRun tail) (targetSet := leftLowSet)
  simp only [Wasm.wp_localGet_cons, leftAtAfterLow,
    leftFlavorAtAfterLow, Wasm.wp_const_cons]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 leftFlavor, .i32 leftWord])
      (tail := tail)
      (locals := { afterLeftLow with values := .i32 leftHigh :: tail })
      (updated := afterLeftHigh) (physicalResult := .i32 leftHigh)
      (callRun := leftHighRun tail) (targetSet := leftHighSet)
  simp only [Wasm.wp_localGet_cons, rightAtAfterLeftHigh,
    rightFlavorAtAfterLeftHigh, Wasm.wp_const_cons]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 rightFlavor, .i32 rightWord])
      (tail := tail)
      (locals := { afterLeftHigh with values := .i32 rightLow :: tail })
      (updated := afterRightLow) (physicalResult := .i32 rightLow)
      (callRun := rightLowRun tail) (targetSet := rightLowSet)
  simp only [Wasm.wp_localGet_cons, rightAtAfterRightLow,
    rightFlavorAtAfterRightLow, Wasm.wp_const_cons]
  apply ResidentPrimitives.wp_definedCallResultSet
      (arguments := [.i32 0, .i32 rightFlavor, .i32 rightWord])
      (tail := tail)
      (locals := { afterRightLow with values := .i32 rightHigh :: tail })
      (updated := afterRightHigh) (physicalResult := .i32 rightHigh)
      (callRun := rightHighRun tail) (targetSet := rightHighSet)
  simp only [Wasm.wp_localGet_cons, leftLowAtEnd, leftHighAtEnd,
    rightLowAtEnd, rightHighAtEnd]
  apply Wasm.wp_call_tw (naturalSumRun tail)
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  exact wp_typedNaturalReturnProgram resultRelated

/-- Concrete-allocation closure of the checked one-limb path.

The four accessor calls still describe the already-validated operands, but
the result is no longer supplied as a separately typed machine word.  The
actual adapted `naturalSum` arithmetic calls `makeNatural` with its computed
low/high pair; that call is required to realize the ordinary concrete
`allocateNatural` transition.  The allocation theorem then constructs the
extended witness and canonical Nat relation consumed by the typed return. -/
theorem wp_checkedOneLimbResult_of_concreteAllocation
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetNaturalSum : Wasm.Function}
    {magnitudeLowIndex magnitudeHighIndex naturalSumIndex makeNaturalIndex : Nat}
    {store resultStore : Wasm.Store host}
    {initial afterLeftLow afterLeftHigh afterRightLow afterRightHigh :
      Wasm.Locals}
    {leftWord rightWord leftFlavor rightFlavor : UInt32}
    {leftLow leftHigh rightLow rightHigh : UInt32}
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {value : Nat} {address : Word32} {tail : List Wasm.Value}
    (leftLocal : initial.get 0 = some (.i32 leftWord))
    (rightLocal : initial.get 1 = some (.i32 rightWord))
    (leftFlavorLocal : initial.get 5 = some (.i32 leftFlavor))
    (rightFlavorLocal : initial.get 6 = some (.i32 rightFlavor))
    (leftLowSet :
      ({ initial with values := .i32 leftLow :: tail }).set? 11
        (.i32 leftLow) = some afterLeftLow)
    (leftHighSet :
      ({ afterLeftLow with values := .i32 leftHigh :: tail }).set? 12
        (.i32 leftHigh) = some afterLeftHigh)
    (rightLowSet :
      ({ afterLeftHigh with values := .i32 rightLow :: tail }).set? 13
        (.i32 rightLow) = some afterRightLow)
    (rightHighSet :
      ({ afterRightLow with values := .i32 rightHigh :: tail }).set? 14
        (.i32 rightHigh) = some afterRightHigh)
    (leftLowRun : ∀ callTail,
      Wasm.TerminatesWith env module magnitudeLowIndex store
        ([.i32 0, .i32 leftFlavor, .i32 leftWord] ++ callTail)
        (fun final values =>
          final = store ∧ values = .i32 leftLow :: callTail))
    (leftHighRun : ∀ callTail,
      Wasm.TerminatesWith env module magnitudeHighIndex store
        ([.i32 0, .i32 leftFlavor, .i32 leftWord] ++ callTail)
        (fun final values =>
          final = store ∧ values = .i32 leftHigh :: callTail))
    (rightLowRun : ∀ callTail,
      Wasm.TerminatesWith env module magnitudeLowIndex store
        ([.i32 0, .i32 rightFlavor, .i32 rightWord] ++ callTail)
        (fun final values =>
          final = store ∧ values = .i32 rightLow :: callTail))
    (rightHighRun : ∀ callTail,
      Wasm.TerminatesWith env module magnitudeHighIndex store
        ([.i32 0, .i32 rightFlavor, .i32 rightWord] ++ callTail)
        (fun final values =>
          final = store ∧ values = .i32 rightHigh :: callTail))
    (naturalSumAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction =
        .ok targetNaturalSum)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (naturalSumNotImport : module.imports[naturalSumIndex]? = none)
    (naturalSumFound :
      module.funcs[naturalSumIndex - module.imports.length]? =
        some targetNaturalSum)
    (highBaseNoOverflow :
      ¬ unsignedSumHighBase leftHigh rightHigh < leftHigh)
    (highCarryNoOverflow :
      ¬ unsignedSumHigh leftLow leftHigh rightLow rightHigh <
        unsignedSumCarry leftLow rightLow)
    (valueEq : value = naturalWordsValue
      (unsignedSumLow leftLow rightLow)
      (unsignedSumHigh leftLow leftHigh rightLow rightHigh))
    (heapRelated : LiveHeapRel before witness runtime)
    (allocated : allocateNatural before value = .ok (after, address))
    (memoryRelated : ResidentMemoryRel after resultStore.mem)
    (makeNaturalRun : Wasm.TerminatesWith env module makeNaturalIndex store
      [.i32 (unsignedSumHigh leftLow leftHigh rightLow rightHigh),
        .i32 (unsignedSumLow leftLow rightLow)]
      (fun final values =>
        final = resultStore ∧
          values = [.i32 (UInt32.ofNat address.value)])) :
    ∃ nextWitness reference,
      witness.Extends nextWitness ∧
        ClosureAllocationsPersistent witness nextWitness ∧
        LiveHeapRel after nextWitness
          (Fir.LeanIR.Impure.literal runtime (.nat value)).1 ∧
        ResidentMemoryRel after resultStore.mem ∧
        (Fir.LeanIR.Impure.literal runtime (.nat value)).2 =
          .object reference ∧
        value = naturalWordsValue
          (unsignedSumLow leftLow rightLow)
          (unsignedSumHigh leftLow leftHigh rightLow rightHigh) ∧
        Wasm.wp module
          (checkedOneLimbResultProgram magnitudeLowIndex magnitudeHighIndex
            naturalSumIndex)
          (TypedNaturalReturnPost nextWitness address reference resultStore
            tail)
          store { initial with values := tail } env := by
  obtain ⟨nextWitness, extension, closureAllocationsPersistent,
      nextHeapRelated, valueRelated⟩ :=
    allocateNatural_liveHeapRel_extends before after witness runtime value
      address heapRelated allocated
  obtain ⟨reference, referenceEq⟩ :=
    literal_nat_objectReference runtime value
  rw [referenceEq] at valueRelated
  have naturalSumRun : ∀ callTail,
      Wasm.TerminatesWith env module naturalSumIndex store
        ([.i32 rightHigh, .i32 rightLow, .i32 leftHigh, .i32 leftLow] ++
          callTail)
        (fun final values =>
          final = resultStore ∧
            values = .i32 (UInt32.ofNat address.value) :: callTail) := by
    intro callTail
    exact (terminatesWith_naturalSumRelated_of_adapted
      (tail := callTail) naturalSumAdapted makeNaturalFound
      naturalSumNotImport naturalSumFound highBaseNoOverflow
      highCarryNoOverflow makeNaturalRun valueRelated).1
  refine ⟨nextWitness, reference, extension, closureAllocationsPersistent,
    nextHeapRelated, memoryRelated, referenceEq, valueEq, ?_⟩
  apply wp_checkedOneLimbResultProgram leftLocal rightLocal leftFlavorLocal
    rightFlavorLocal leftLowSet leftHighSet rightLowSet rightHighSet
    leftLowRun leftHighRun rightLowRun rightHighRun naturalSumRun
  exact valueRelated

/-- Source suffix of the checked multi-limb branch after allocation and limb
writing have established the result in `raw`. -/
def checkedAllocatedNaturalReturnSource (raw : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  [.localGet raw] ++ typedNaturalReturnSource

/-- Talos suffix of the checked multi-limb branch. -/
def checkedAllocatedNaturalReturnProgram (rawIndex : Nat) : Wasm.Program :=
  [.localGet rawIndex] ++ typedNaturalReturnProgram

/-- The actual multi-limb branch factors into the allocator/writer producer
and the exact local-get plus typed return suffix. -/
theorem natAddFunction_checkedMultiLimb_shape :
    ∃ checkedPrefix multiLimbProducer,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          (checkedPrefix ++ [
            .localGet
              Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[8]!.1,
            .i32Const .uint32 1,
            .i32Eq,
            .ifElse
              (checkedOneLimbProducerSource
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[3]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[4]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[9]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[10]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[11]!.1
                Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[12]!.1 ++
                  typedNaturalReturnSource)
              ((multiLimbProducer ++ [.localGet
                  Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[0]!.1]) ++
                typedNaturalReturnSource)]) := by
  refine ⟨_, _, rfl⟩

/-- Adapter preservation for the multi-limb result suffix. -/
theorem instructions_checkedAllocatedNaturalReturnSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {raw : Lean.FVarId} {rawIndex : Nat}
    (rawFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) raw =
        some rawIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (checkedAllocatedNaturalReturnSource raw) =
        .ok (checkedAllocatedNaturalReturnProgram rawIndex) := by
  simp [checkedAllocatedNaturalReturnSource,
    checkedAllocatedNaturalReturnProgram, typedNaturalReturnSource,
    typedNaturalReturnProgram,
    ResidentPrimitives.typedObjectWordRoundTripSource,
    ResidentPrimitives.unsignedI32RoundTrip, FirTalos.instructions,
    FirTalos.instruction, rawFound, Bind.bind, Except.bind, pure,
    Except.pure]

/-- Once the allocator/writer producer has established both the raw local and
the concrete Nat relation, the exact generated suffix returns that word with
no memory access and no change to the store or stack tail. -/
theorem wp_checkedAllocatedNaturalReturnProgram
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {rawIndex : Nat} {witness : RefinementWitness} {word : Word32}
    {reference : Fir.LeanIR.Impure.ObjectRef} {tail : List Wasm.Value}
    (rawLocal : locals.get rawIndex =
      some (.i32 (UInt32.ofNat word.value)))
    (related :
      ValueRel witness .tobject (.word32 word) (.object reference)) :
    Wasm.wp module (checkedAllocatedNaturalReturnProgram rawIndex)
      (TypedNaturalReturnPost witness word reference store tail) store
      { locals with values := tail } env := by
  unfold checkedAllocatedNaturalReturnProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons]
  have rawAt (values : List Wasm.Value) :
      ({ locals with values } : Wasm.Locals).get rawIndex =
        some (.i32 (UInt32.ofNat word.value)) := by simpa using rawLocal
  rw [rawAt]
  exact wp_typedNaturalReturnProgram related

/-- Concrete allocation boundary for the checked multi-limb producer.  If the
resident allocator/writer prefix realizes the ordinary `allocateNatural`
result for the mathematical sum, W6's existing allocation theorem constructs
the fresh semantic location, live-heap relation, and exact object `ValueRel`;
the generated local-get/typed-return suffix then returns that canonical live
Natural unchanged. -/
theorem wp_checkedAllocatedNaturalReturn_of_allocateNatural
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState} {value : Nat}
    {address : Word32} {store : Wasm.Store host} {locals : Wasm.Locals}
    {rawIndex : Nat} {tail : List Wasm.Value}
    (heapRelated : LiveHeapRel before witness runtime)
    (large : Fir.LeanIR.Impure.maxTaggedPayload < value)
    (allocated : allocateNatural before value = .ok (after, address))
    (memoryRelated : ResidentMemoryRel after store.mem)
    (rawLocal : locals.get rawIndex =
      some (.i32 (UInt32.ofNat address.value))) :
    let nextWitness :=
      witness.bindNatural runtime.nextLocation address value
    LiveHeapRel after nextWitness (semanticNaturalResult runtime value) ∧
      ResidentMemoryRel after store.mem ∧
      Wasm.wp module (checkedAllocatedNaturalReturnProgram rawIndex)
        (TypedNaturalReturnPost nextWitness address
          (.heap runtime.nextLocation) store tail)
        store { locals with values := tail } env := by
  dsimp only
  obtain ⟨nextHeapRelated, valueRelated⟩ :=
    allocateNatural_heap_liveHeapRel before after witness runtime value address
      heapRelated large allocated
  exact ⟨nextHeapRelated, memoryRelated,
    wp_checkedAllocatedNaturalReturnProgram rawLocal valueRelated⟩

/-- Exact resident-writer replacement for the former `allocateNatural`
shortcut at the generated typed-return suffix.

The returned address is justified by the raw allocator, exact physical limb
history, transported header, decoded mathematical value, and full live-heap
extension.  The suffix itself remains the existing scratch-free typed object
round trip. -/
theorem wp_checkedAllocatedNaturalReturn_of_memoryRel
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count value : Nat}
    {before allocated after : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {locals : Wasm.Locals} {rawIndex : Nat} {tail : List Wasm.Value}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (allocation : before.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0 =
          .ok (allocated, address))
    (heapRelated : LiveHeapRel before witness runtime)
    (extension : before.PrefixExtension after)
    (finalFrontier : after.FrontierInvariant)
    (cursorEq : after.heapCursor = allocated.heapCursor)
    (initialRelated : ResidentMemoryRel allocated initial.mem)
    (finalRelated : ResidentMemoryRel after
      (completedAddStore current (UInt32.ofNat address.value) count carry).mem)
    (payloadInBounds :
      address.value + headerBytes + 8 * (count + carry.toNat) ≤
        after.memory.size)
    (valueEq : limbWordsListValue (completedAddLimbWords words carry) = value)
    (rawLocal : locals.get rawIndex =
      some (.i32 (UInt32.ofNat address.value))) :
    let nextWitness := witness.bindNatural runtime.nextLocation address value
    witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel after nextWitness (semanticNaturalResult runtime value) ∧
      ResidentMemoryRel after
        (completedAddStore current (UInt32.ofNat address.value) count carry).mem ∧
      Wasm.wp module (checkedAllocatedNaturalReturnProgram rawIndex)
        (TypedNaturalReturnPost nextWitness address
          (.heap runtime.nextLocation)
          (completedAddStore current (UInt32.ofNat address.value) count carry)
          tail)
        (completedAddStore current (UInt32.ofNat address.value) count carry)
        { locals with values := tail } env := by
  dsimp only
  obtain ⟨witnessExtension, closureAllocationsPersistent, nextHeapRelated,
      valueRelated⟩ :=
    written.liveHeapRel_completeWithCarry_of_memoryRel wordsLength carryBit
      allocation heapRelated extension finalFrontier cursorEq initialRelated
      finalRelated payloadInBounds valueEq
  exact ⟨witnessExtension, closureAllocationsPersistent, nextHeapRelated,
    finalRelated,
    wp_checkedAllocatedNaturalReturnProgram rawLocal valueRelated⟩

/-- Self-contained typed-return closure for the exact resident writer.

The final W6 heap is existentially constructed by replaying the resident
stores, so no final memory relation, prefix extension, frontier, cursor, or
payload-bound premise remains at this boundary. -/
theorem wp_checkedAllocatedNaturalReturn_of_allocateObject
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {initial current : Wasm.Store host} {address : Word32} {carry : UInt32}
    {words : List LimbWords} {count value : Nat}
    {before allocated : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {locals : Wasm.Locals} {rawIndex : Nat} {tail : List Wasm.Value}
    (written : WrittenLimbPrefix initial (UInt32.ofNat address.value) words
      count current)
    (wordsLength : words.length = count)
    (carryBit : carry = 0 ∨ carry = 1)
    (allocation : before.allocateObject .natural
      (target.semanticSlotBytes * (count + carry.toNat)) false
        bigNaturalMarker (UInt32.ofNat (count + carry.toNat)) 0 0 =
          .ok (allocated, address))
    (heapRelated : LiveHeapRel before witness runtime)
    (initialRelated : ResidentMemoryRel allocated initial.mem)
    (valueEq : limbWordsListValue (completedAddLimbWords words carry) = value)
    (rawLocal : locals.get rawIndex =
      some (.i32 (UInt32.ofNat address.value))) :
    ∃ heap,
      let nextWitness := witness.bindNatural runtime.nextLocation address value
      witness.Extends nextWitness ∧
        ClosureAllocationsPersistent witness nextWitness ∧
        LiveHeapRel heap nextWitness (semanticNaturalResult runtime value) ∧
        ResidentMemoryRel heap
          (completedAddStore current (UInt32.ofNat address.value) count carry).mem ∧
        Wasm.wp module (checkedAllocatedNaturalReturnProgram rawIndex)
          (TypedNaturalReturnPost nextWitness address
            (.heap runtime.nextLocation)
            (completedAddStore current (UInt32.ofNat address.value) count carry)
            tail)
          (completedAddStore current (UInt32.ofNat address.value) count carry)
          { locals with values := tail } env := by
  obtain ⟨heap, witnessExtension, closureAllocationsPersistent,
      finalHeapRelated, finalRelated, valueRelated⟩ :=
    written.liveHeapRel_completeWithCarry_of_allocateObject wordsLength
      carryBit allocation heapRelated initialRelated valueEq
  exact ⟨heap, witnessExtension, closureAllocationsPersistent,
    finalHeapRelated, finalRelated,
    wp_checkedAllocatedNaturalReturnProgram rawLocal valueRelated⟩

/-- The public resident `Nat.add` function is the common pair dispatcher with
the exact immediate arm above and an opaque checked arbitrary-precision arm. -/
theorem natAddFunction_immediate_shape :
    ∃ fallback,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          fallback := by
  refine ⟨_, rfl⟩

/-- Public cardinality fact for the generated helper's private local array.
Scratch-local validity proofs should depend on this boundary rather than the
private generator name used to assemble the remaining arithmetic locals. -/
theorem natAddFunction_locals_size :
    Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals.size = 17 := by
  rfl

/-- The adapter maps the symbolic immediate-add arm to the exact Talos
program used by its execution theorem. -/
theorem instructions_immediateAddSource
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {left right : Lean.FVarId}
    {leftIndex rightIndex naturalSumIndex : Nat}
    (leftFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) left =
        some leftIndex)
    (rightFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) right =
        some rightIndex)
    (naturalSumFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.naturalSumName) =
        some naturalSumIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (immediateAddSource left right) =
        .ok (ResidentPrimitives.immediateNaturalPayload leftIndex ++
          [.const 0] ++
          ResidentPrimitives.immediateNaturalPayload rightIndex ++ [
            .const 0,
            .call naturalSumIndex] ++
          ResidentPrimitives.unsignedI32RoundTrip ++ [.ret]) := by
  simp [immediateAddSource,
    Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload,
    ResidentPrimitives.immediateNaturalPayload,
    ResidentPrimitives.typedObjectWordRoundTripSource,
    ResidentPrimitives.unsignedI32RoundTrip,
    FirTalos.instructions, FirTalos.instruction, leftFound, rightFound,
    naturalSumFound, Bind.bind, Except.bind, pure, Except.pure]

/-- Exact adaptation of the complete public `Nat.add` body, retaining the
opaque fallback but exposing the common dispatcher and immediate arm. -/
theorem instructions_natAddFunctionBody_of_shape
    {sourceModule : Fir.Wasm.Module}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {naturalSumIndex : Nat}
    (shape :
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          sourceFallback)
    (naturalSumFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.naturalSumName) =
        some naturalSumIndex)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction [] sourceFallback =
        .ok targetFallback) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction []
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        .ok (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateAddProgram naturalSumIndex) targetFallback) := by
  rw [shape]
  apply ResidentPrimitives.instructions_withImmediateNaturalPair
      (leftIndex := 0) (rightIndex := 1)
  · decide
  · decide
  · simpa [immediateAddProgram] using
      (instructions_immediateAddSource
        (sourceModule := sourceModule)
        (sourceFunction :=
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction)
        (labels := []) (leftIndex := 0) (rightIndex := 1)
        (naturalSumIndex := naturalSumIndex)
        (by decide) (by decide) naturalSumFound)
  · exact fallbackAdapted

/-- Successful adaptation installs precisely the proved `Nat.add` dispatcher
followed by the adapter's standard physical terminal suffix. -/
theorem adaptedNatAddFunction_body_of_shape
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {naturalSumIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction = .ok targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          sourceFallback)
    (naturalSumFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.naturalSumName) =
        some naturalSumIndex)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction [] sourceFallback =
        .ok targetFallback) :
    targetFunction.body =
      ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateAddProgram naturalSumIndex) targetFallback ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction := by
  exact adaptedFunction_body_of_exact adapted
    (instructions_natAddFunctionBody_of_shape shape naturalSumFound
      fallbackAdapted)

/-- Canonical physical result of a two-immediate Nat addition whose sum is
still in the immediate range. -/
def immediateSumWord
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64}
    (_pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (sumFits : leftPayload.toNat + rightPayload.toNat ≤ maxImmediatePayload) :
    UInt32 :=
  UInt32.ofNat (Word32.encodeImmediate
    (leftPayload.toNat + rightPayload.toNat) sumFits).value

/-- The two-immediate `Nat.add` arm composes the shared decoders, the factored
natural-sum call, and the scratch-free typed word round trip.  The explicit
`ValueRel` premise is the operation-specific validity boundary omitted by the
generic physical lemma: the result may be either a tagged immediate or a live
heap representation, but it cannot be an arbitrary `i32`. -/
theorem wp_immediateAddProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {witness : RefinementWitness}
    {naturalSumIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload resultPayload : UInt64} {resultWord : Word32}
    {tail : List Wasm.Value}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (_resultRelated : ValueRel witness .tobject (.word32 resultWord)
      (.object (.tagged resultPayload)))
    (leftLocal : locals.get 0 = some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 = some (.i32 (UInt32.ofNat rightWord.value)))
    (naturalSumRun :
      Wasm.TerminatesWith env module naturalSumIndex store
        ([.i32 0, .i32 (UInt32.ofNat rightPayload.toNat),
          .i32 0, .i32 (UInt32.ofNat leftPayload.toNat)] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (UInt32.ofNat resultWord.value) :: tail))
    (returned :
      Q (.Return store (.i32 (UInt32.ofNat resultWord.value) :: tail))) :
    Wasm.wp module (immediateAddProgram naturalSumIndex) Q store
      { locals with values := tail } env := by
  unfold immediateAddProgram
  simp only [List.append_assoc]
  apply ResidentPrimitives.wp_immediateNaturalLeftPayload pair leftLocal
  simp only [List.cons_append, List.nil_append, Wasm.wp_const_cons]
  apply ResidentPrimitives.wp_immediateNaturalRightPayload pair rightLocal
  simp only [Wasm.wp_const_cons]
  apply Wasm.wp_call_tw naturalSumRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  apply ResidentPrimitives.wp_unsignedI32RoundTrip
  simpa only [Wasm.wp_ret_cons] using returned

/-- The common pair dispatcher selects the immediate-add arm for a related
pair; its checked fallback and terminal suffix remain unreachable after the
arm's explicit return. -/
theorem wp_immediateAddDispatch
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {witness : RefinementWitness}
    {naturalSumIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload resultPayload : UInt64} {resultWord : Word32}
    {tail : List Wasm.Value}
    {fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (resultRelated : ValueRel witness .tobject (.word32 resultWord)
      (.object (.tagged resultPayload)))
    (leftLocal : locals.get 0 = some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 = some (.i32 (UInt32.ofNat rightWord.value)))
    (naturalSumRun :
      Wasm.TerminatesWith env module naturalSumIndex store
        ([.i32 0, .i32 (UInt32.ofNat rightPayload.toNat),
          .i32 0, .i32 (UInt32.ofNat leftPayload.toNat)] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (UInt32.ofNat resultWord.value) :: tail))
    (returned :
      Q (.Return store (.i32 (UInt32.ofNat resultWord.value) :: tail))) :
    Wasm.wp module
      (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateAddProgram naturalSumIndex) fallback ++ rest)
      Q store { locals with values := tail } env := by
  apply ResidentPrimitives.wp_immediateNaturalPairDispatch pair leftLocal
    rightLocal
  apply wp_immediateAddProgram pair resultRelated leftLocal rightLocal
    naturalSumRun
  simpa using returned

/-- The immediate path of the actual adapted resident `Nat.add` function is a
fuel-free defined call.  Its nested `naturalSum` and `makeNatural` calls are
the actual adapted helper bodies, and the complete path preserves the store
while returning the canonical tagged mathematical sum. -/
theorem terminatesWith_natAddFunctionImmediate_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction targetNaturalSum targetMakeNatural : Wasm.Function}
    {functionIndex naturalSumIndex makeNaturalIndex : Nat}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program} {store : Wasm.Store host}
    {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction = .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (shape :
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.body =
        Fir.Wasm.Emit.ResidentBigNumeric.withImmediateNaturalPair
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
          Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
          (immediateAddSource
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1)
          sourceFallback)
    (naturalSumFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.naturalSumName) =
        some naturalSumIndex)
    (fallbackAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction [] sourceFallback =
        .ok targetFallback)
    (naturalSumAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.naturalSumFunction =
        .ok targetNaturalSum)
    (makeNaturalFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.makeNaturalName) =
        some makeNaturalIndex)
    (makeNaturalAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction =
        .ok targetMakeNatural)
    (naturalSumNotImport : module.imports[naturalSumIndex]? = none)
    (naturalSumTargetFound :
      module.funcs[naturalSumIndex - module.imports.length]? =
        some targetNaturalSum)
    (makeNaturalNotImport : module.imports[makeNaturalIndex]? = none)
    (makeNaturalTargetFound :
      module.funcs[makeNaturalIndex - module.imports.length]? =
        some targetMakeNatural)
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (sumFits : leftPayload.toNat + rightPayload.toNat ≤ maxImmediatePayload) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat rightWord.value),
        .i32 (UInt32.ofNat leftWord.value)] ++ tail)
      (fun final values =>
        final = store ∧
          values = .i32 (immediateSumWord pair sumFits) :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedNatAddFunction_body_of_shape adapted shape
    naturalSumFound fallbackAdapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let entry := targetFunction.toLocals
    (([Wasm.Value.i32 (UInt32.ofNat rightWord.value),
      Wasm.Value.i32 (UInt32.ofNat leftWord.value)] ++ tail).take
        targetFunction.numParams).reverse
  have leftLocal : entry.get 0 =
      some (.i32 (UInt32.ofNat leftWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction]
  have rightLocal : entry.get 1 =
      some (.i32 (UInt32.ofNat rightWord.value)) := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction]
  have naturalSumRun :
      Wasm.TerminatesWith env module naturalSumIndex store
        [.i32 0, .i32 (UInt32.ofNat rightPayload.toNat),
          .i32 0, .i32 (UInt32.ofNat leftPayload.toNat)]
        (fun final values =>
          final = store ∧
            values = .i32 (immediateSumWord pair sumFits) :: []) := by
    simpa [immediateSumWord] using
      (terminatesWith_naturalSumImmediate_of_adapted
        (module := module) (env := env) (store := store)
        (functionIndex := naturalSumIndex)
        (makeNaturalIndex := makeNaturalIndex)
        (left := leftPayload.toNat) (right := rightPayload.toNat) (tail := [])
        sumFits naturalSumAdapted makeNaturalFound makeNaturalAdapted
        naturalSumNotImport naturalSumTargetFound makeNaturalNotImport
        makeNaturalTargetFound)
  have sumLt : leftPayload.toNat + rightPayload.toNat < 18446744073709551616 := by
    unfold maxImmediatePayload at sumFits
    omega
  have resultRelated :
      ValueRel (default : RefinementWitness) .tobject
        (.word32 (Word32.encodeImmediate
          (leftPayload.toNat + rightPayload.toNat) sumFits))
        (.object (.tagged (UInt64.ofNat
          (leftPayload.toNat + rightPayload.toNat)))) := by
    apply ValueRel.tobject
    apply ObjectReferenceRel.tagged
    have payloadFits :
        (UInt64.ofNat
          (leftPayload.toNat + rightPayload.toNat)).toNat ≤
            maxImmediatePayload := by
      simpa [Nat.mod_eq_of_lt sumLt] using sumFits
    simpa [Nat.mod_eq_of_lt sumLt] using
      (TaggedReferenceRel.immediate
        (witness := (default : RefinementWitness))
        (UInt64.ofNat (leftPayload.toNat + rightPayload.toNat)) payloadFits)
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction
          ([.i32 (UInt32.ofNat rightWord.value),
            .i32 (UInt32.ofNat leftWord.value)] ++ tail)
          (fun final values =>
            final = store ∧
              values = .i32 (immediateSumWord pair sumFits) :: tail)
          (.Return store [.i32 (immediateSumWord pair sumFits)]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
      paramsEq, resultsEq,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction]
  simpa [entry, Wasm.Function.toLocals] using
    (wp_immediateAddDispatch
      (module := module) (env := env) (store := store) (locals := entry)
      (naturalSumIndex := naturalSumIndex) (fallback := targetFallback)
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction)
      (witness := (default : RefinementWitness))
      (resultWord := Word32.encodeImmediate
        (leftPayload.toNat + rightPayload.toNat) sumFits)
      (resultPayload := UInt64.ofNat
        (leftPayload.toNat + rightPayload.toNat))
      (tail := []) pair resultRelated leftLocal rightLocal naturalSumRun returned)

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
  have exactBody := instructions_modFunctionBody_of_shape shape
    makeNaturalFound fallbackAdapted
  exact adaptedFunction_body_of_exact adapted exactBody

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
    {targetFunction targetMakeNatural : Wasm.Function}
    {functionIndex makeNaturalIndex : Nat}
    {sourceFallback : List Fir.Wasm.Instruction}
    {targetFallback : Wasm.Program}
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
    (makeNaturalAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentNumeric.makeNaturalFunction =
        .ok targetMakeNatural)
    (makeNaturalTargetFound :
      module.funcs[makeNaturalIndex - module.imports.length]? =
        some targetMakeNatural)
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
      (terminatesWith_makeNaturalImmediate_of_adapted
        (module := module) (env := env) (store := store) (tail := [])
        makeNaturalAdapted pair.mod_fits makeNaturalNotImport
        makeNaturalTargetFound)
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
