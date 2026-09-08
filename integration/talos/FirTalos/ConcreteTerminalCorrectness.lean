import FirTalos.ConcreteStructuredSimulation

/-!
# Terminal return bridge for the existing structured compiler relation

The ranked simulation supplies a finite target prefix; the checked frame stack
and yielded-value relation supply its terminal completion. These helpers derive
that completion and use the adapter's existing adequacy theorem to recover an
executable `Wasm.run` result. Target paths are internal composition evidence,
not a new client certificate or a closed compiler-correctness endpoint.

This module changes no source/target relation or admission predicate. It covers
successful returns only: the structured target currently has no trap control.
-/

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- When no source continuation remains, the checked target stack contains
only administrative case labels. Returning unwinds those labels and halts
without changing the store or the returned stack. -/
theorem ConcreteStructuredSupportedFrameStack.returning_halts
    {program : Fir.LeanIR.ImpureProgram} {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {functionResult : AbiKind} {expectedResult : Option AbiKind}
    {sourceFrames : List Frame} {targetFrames : List StructuredWasmFrame}
    (related : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult sourceFrames targetFrames)
    (empty : sourceFrames = [])
    (store : Wasm.Store Host) (values : List Wasm.Value) :
    ∃ count, FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
      count ⟨store, .returning values, targetFrames⟩
      ⟨store, .halted values, []⟩ := by
  induction related with
  | nil => exact ⟨1, .single .haltReturn⟩
  | @case _ _ _ _ belowStack rest testCount tail ih =>
      obtain ⟨count, path⟩ := ih empty
      exact ⟨testCount + count,
        (structuredWasmReturnCaseLabelsFinitePath
          (belowStack := belowStack) (rest := rest) testCount).trans path⟩
  | direct => cases empty
  | saturated => cases empty
  | lazy => cases empty

/-- The existing yielded-value relation already contains the whole refined
return postcondition, not just world and external-event trace agreement. -/
theorem ConcreteStructuredYieldFocus.refinedReturnPost
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env} {sourceValue : Value}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {kind : AbiKind} {physical : Wasm.Value}
    {source : MachineState} {target : StructuredWasmState Host}
    (related : ConcreteStructuredYieldFocus context sourceFunction
      sourceRuntime sourceEnv sourceValue targetStore targetLocals witness kind
      physical source target)
    (callerTail : List Wasm.Value) :
    RefinedReturnPost sourceRuntime sourceValue kind callerTail targetStore
      (physical :: callerTail) :=
  ⟨witness, physical, related.stateRelated.1, related.stateRelated.2.1,
    related.valueRelated, rfl⟩

/-- Finish a terminal source yield using the existing checked frame stack.
The target may still be inside generated case labels; no empty-target-stack
premise or separately supplied completion path is needed. -/
theorem ConcreteStructuredYieldFocus.finitePath_halted
    {program : Fir.LeanIR.ImpureProgram} {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env} {sourceValue : Value}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {kind functionResult : AbiKind}
    {expectedResult : Option AbiKind} {physical : Wasm.Value}
    {source : MachineState} {target : StructuredWasmState Host}
    (related : ConcreteStructuredYieldFocus context sourceFunction
      sourceRuntime sourceEnv sourceValue targetStore targetLocals witness kind
      physical source target)
    (frames : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult source.frames target.frames)
    (empty : source.frames = []) :
    ∃ count, FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
      count target ⟨targetStore, .halted (physical :: targetLocals.values), []⟩ := by
  rcases target with ⟨store, control, targetFrames⟩
  have storeEq := related.targetStoreEq
  have controlEq := related.targetControlEq
  change store = targetStore at storeEq
  change control = .returning (physical :: targetLocals.values) at controlEq
  subst store control
  exact frames.returning_halts empty targetStore (physical :: targetLocals.values)

/-- Reconnect a compiler-generated function's finite structured prefix and
terminal yield to its actual Talos invocation. The suffix completion, loop
arity safety, fuel bound, result truncation, and caller-tail restoration are
all derived here. The prefix is supplied internally by finite simulation; this
is not the canonical closed export theorem.

The yielding focus need not use the entry function's context. Keeping the two
independent avoids imposing a redundant active-function identity premise on
the later global simulation assembly. -/
theorem ConcreteSupportedFunction.terminatesWith_of_structuredYield
    {program : Fir.LeanIR.ImpureProgram}
    {entryContext context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {entryFunction sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program entryContext code sourceModule
      entryFunction targetModule hosts)
    {initial targetStore : Wasm.Store Host}
    {parameters callerTail : List Wasm.Value}
    {sourceRuntime : RuntimeState} {sourceEnv : Env} {sourceValue : Value}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    {kind functionResult : AbiKind} {expectedResult : Option AbiKind}
    {physical : Wasm.Value} {source : MachineState}
    {target : StructuredWasmState Host} {count : Nat}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (targetPrefix : FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
      count (StructuredWasmState.functionEntry spec.targetFunction initial
        (parameters ++ callerTail)) target)
    (related : ConcreteStructuredYieldFocus context sourceFunction
      sourceRuntime sourceEnv sourceValue targetStore targetLocals witness kind
      physical source target)
    (frames : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult source.frames target.frames)
    (empty : source.frames = []) :
    Wasm.TerminatesWith hosts.env targetModule.wasmModule spec.targetFunctionIndex
      initial (parameters ++ callerTail)
      (RefinedReturnPost sourceRuntime sourceValue kind callerTail) := by
  obtain ⟨suffixCount, suffix⟩ := related.finitePath_halted frames empty
  obtain ⟨bound, runs⟩ := StructuredWasmStep.finitePath_run_of_adapt
    spec.adapted spec.notImport spec.targetFunctionFound (targetPrefix.trans suffix)
  have tailEq : (parameters ++ callerTail).drop spec.targetFunction.numParams =
      callerTail := by
    rw [← parameterCount]
    simp
  refine ⟨bound, ?_⟩
  intro fuel enough
  refine ⟨physical :: callerTail, targetStore, ?_, related.refinedReturnPost callerTail⟩
  simpa only [spec.singleResult, List.take_succ_cons, List.take_zero,
    List.cons_append, List.nil_append, tailEq] using runs fuel enough

/-- Export-name specialization of the terminal bridge. This consumes the
same internal finite-prefix evidence as the function lemma, and adds no
client invariant, host contract, or result-shape assumption. -/
theorem ConcreteSupportedExport.terminatesWith_of_structuredYield
    {program : Fir.LeanIR.ImpureProgram}
    {entryContext context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {entryFunction sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program entryContext code sourceModule
      entryFunction targetModule hosts exportName)
    {initial targetStore : Wasm.Store Host} {parameters : List Wasm.Value}
    {sourceRuntime : RuntimeState} {sourceEnv : Env} {sourceValue : Value}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    {kind functionResult : AbiKind} {expectedResult : Option AbiKind}
    {physical : Wasm.Value} {source : MachineState}
    {target : StructuredWasmState Host} {count : Nat}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (targetPrefix : FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
      count (StructuredWasmState.functionEntry spec.targetFunction initial parameters)
      target)
    (related : ConcreteStructuredYieldFocus context sourceFunction
      sourceRuntime sourceEnv sourceValue targetStore targetLocals witness kind
      physical source target)
    (frames : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult source.frames target.frames)
    (empty : source.frames = []) :
    ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
      initial parameters (RefinedReturnPost sourceRuntime sourceValue kind []) := by
  refine ⟨spec.targetFunctionIndex, spec.exported, ?_⟩
  simpa using spec.toConcreteSupportedFunction.terminatesWith_of_structuredYield
    (callerTail := []) parameterCount (by simpa using targetPrefix) related frames empty

end FirTalos.Concrete
