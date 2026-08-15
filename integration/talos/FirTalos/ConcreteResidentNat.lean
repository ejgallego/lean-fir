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
payload decoder feeds zero high words to `naturalSum`, whose raw result then
crosses the common scratch-slot object cast. -/
def immediateAddProgram (naturalSumIndex : Nat) : Wasm.Program :=
  ResidentPrimitives.immediateNaturalPayload 0 ++ [.const 0] ++
    ResidentPrimitives.immediateNaturalPayload 1 ++ [
      .const 0,
      .call naturalSumIndex] ++
    retypeRawObjectResultProgram 2 3 4

/-- Symbolic source spelling of `immediateAddProgram`; the public function's
private local identifiers are supplied positionally by the shape theorem. -/
def immediateAddSource (left right raw saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload left ++ [
      .i32Const .uint32 0] ++
    Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload right ++ [
      .i32Const .uint32 0,
      .call (.declaration
        Fir.Wasm.Emit.ResidentNumeric.naturalSumName)] ++
    retypeRawObjectResultSource raw saved result

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
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[2]!.1)
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
    {labels : List Lean.FVarId} {left right raw saved result : Lean.FVarId}
    {leftIndex rightIndex rawIndex savedIndex resultIndex naturalSumIndex : Nat}
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
    (naturalSumFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentNumeric.naturalSumName) =
        some naturalSumIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (immediateAddSource left right raw saved result) =
        .ok (ResidentPrimitives.immediateNaturalPayload leftIndex ++
          [.const 0] ++
          ResidentPrimitives.immediateNaturalPayload rightIndex ++ [
            .const 0,
            .call naturalSumIndex] ++
          retypeRawObjectResultProgram rawIndex savedIndex resultIndex) := by
  simp [immediateAddSource,
    Fir.Wasm.Emit.ResidentBigNumeric.immediateNaturalPayload,
    ResidentPrimitives.immediateNaturalPayload,
    retypeRawObjectResultSource, retypeRawObjectResultProgram,
    FirTalos.instructions, FirTalos.instruction, leftFound, rightFound,
    rawFound, savedFound, resultFound, naturalSumFound,
    Bind.bind, Except.bind, pure, Except.pure]

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
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[2]!.1)
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
        (rawIndex := 2) (savedIndex := 3) (resultIndex := 4)
        (naturalSumIndex := naturalSumIndex)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        naturalSumFound)
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
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[2]!.1)
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
natural-sum call, and the common scratch-slot cast. -/
theorem wp_immediateAddProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals afterRaw afterSaved afterResult : Wasm.Locals}
    {naturalSumIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (sumFits : leftPayload.toNat + rightPayload.toNat ≤ maxImmediatePayload)
    (pagesPositive : 0 < store.mem.pages)
    (leftLocal : locals.get 0 = some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 = some (.i32 (UInt32.ofNat rightWord.value)))
    (naturalSumRun :
      Wasm.TerminatesWith env module naturalSumIndex store
        ([.i32 0, .i32 (UInt32.ofNat rightPayload.toNat),
          .i32 0, .i32 (UInt32.ofNat leftPayload.toNat)] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (immediateSumWord pair sumFits) :: tail))
    (rawSet :
      ({ locals with values := .i32 (immediateSumWord pair sumFits) :: tail
        }).set? 2 (.i32 (immediateSumWord pair sumFits)) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (store.mem.read32 0) :: tail
        }).set? 3 (.i32 (store.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 (immediateSumWord pair sumFits) :: tail
        }).set? 4 (.i32 (immediateSumWord pair sumFits)) = some afterResult)
    (returned :
      Q (.Return store (.i32 (immediateSumWord pair sumFits) :: tail))) :
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
  apply wp_retypeRawObjectResultProgram pagesPositive (by decide) (by decide)
    rawSet savedSet resultSet
  simpa using returned

/-- The common pair dispatcher selects the immediate-add arm for a related
pair; its checked fallback and terminal suffix remain unreachable after the
arm's explicit return. -/
theorem wp_immediateAddDispatch
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals afterRaw afterSaved afterResult : Wasm.Locals}
    {naturalSumIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (sumFits : leftPayload.toNat + rightPayload.toNat ≤ maxImmediatePayload)
    (pagesPositive : 0 < store.mem.pages)
    (leftLocal : locals.get 0 = some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get 1 = some (.i32 (UInt32.ofNat rightWord.value)))
    (naturalSumRun :
      Wasm.TerminatesWith env module naturalSumIndex store
        ([.i32 0, .i32 (UInt32.ofNat rightPayload.toNat),
          .i32 0, .i32 (UInt32.ofNat leftPayload.toNat)] ++ tail)
        (fun final values =>
          final = store ∧
            values = .i32 (immediateSumWord pair sumFits) :: tail))
    (rawSet :
      ({ locals with values := .i32 (immediateSumWord pair sumFits) :: tail
        }).set? 2 (.i32 (immediateSumWord pair sumFits)) = some afterRaw)
    (savedSet :
      ({ afterRaw with values := .i32 (store.mem.read32 0) :: tail
        }).set? 3 (.i32 (store.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := .i32 (immediateSumWord pair sumFits) :: tail
        }).set? 4 (.i32 (immediateSumWord pair sumFits)) = some afterResult)
    (returned :
      Q (.Return store (.i32 (immediateSumWord pair sumFits) :: tail))) :
    Wasm.wp module
      (ResidentPrimitives.immediateNaturalPairDispatch 0 1
          (immediateAddProgram naturalSumIndex) fallback ++ rest)
      Q store { locals with values := tail } env := by
  apply ResidentPrimitives.wp_immediateNaturalPairDispatch pair leftLocal
    rightLocal
  apply wp_immediateAddProgram pair sumFits pagesPositive leftLocal rightLocal
    naturalSumRun rawSet savedSet resultSet
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
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[0]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[1]!.1
            Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction.locals[2]!.1)
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
    (sumFits : leftPayload.toNat + rightPayload.toNat ≤ maxImmediatePayload)
    (pagesPositive : 0 < store.mem.pages) :
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
  have targetLocalsLength : targetFunction.locals.length = 17 := by
    rw [localsEq, List.length_map, Array.length_toList,
      natAddFunction_locals_size]
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
  have rawValid :
      ({ entry with values := [.i32 (immediateSumWord pair sumFits)]
        }).validIndex 2 := by
    simp [entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      targetLocalsLength,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction]
  obtain ⟨afterRaw, rawSet⟩ :=
    FirTalos.Correctness.locals_set?_exists rawValid
  have rawLengths := FirTalos.Correctness.locals_lengths_of_set? rawSet
  have savedValid :
      ({ afterRaw with values := [.i32 (store.mem.read32 0)]
        }).validIndex 3 := by
    simp only [Wasm.Locals.validIndex]
    simp [rawLengths.1, rawLengths.2, entry, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, targetLocalsLength,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction]
  obtain ⟨afterSaved, savedSet⟩ :=
    FirTalos.Correctness.locals_set?_exists savedValid
  have savedLengths := FirTalos.Correctness.locals_lengths_of_set? savedSet
  have resultValid :
      ({ afterSaved with values := [.i32 (immediateSumWord pair sumFits)]
        }).validIndex 4 := by
    simp only [Wasm.Locals.validIndex]
    simp [savedLengths.1, savedLengths.2, rawLengths.1, rawLengths.2,
      entry, Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      targetLocalsLength,
      Fir.Wasm.Emit.ResidentBigNumeric.natAddFunction]
  obtain ⟨afterResult, resultSet⟩ :=
    FirTalos.Correctness.locals_set?_exists resultValid
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
      (tail := []) pair sumFits pagesPositive leftLocal rightLocal
      naturalSumRun rawSet savedSet resultSet returned)

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
