import FirTalos.ConcreteRootedSimulation
import FirTalos.ConcreteTerminalExtraction

/-!
# Exact-root executable return correctness

Successful source completion selects the precise returned constructor of the
accepted rooted companion. Its empty source continuation identifies the active
result with the original export ABI; target-only case labels may still remain.
The existing structured-yield adequacy theorem handles their unwinding.

Finite-prefix composition supplies target execution, and production export
validation constructs the initial relation. The result ABI is no longer
existential or a caller-supplied equality. Compiler admission, address-space
safety, argument arity and the existing entry/runtime contracts remain explicit.
This is a conditional successful-return theorem, not general admission closure,
fault preservation, resident linking or a correspondence to encoded bytes.
-/

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Terminal extraction preserves the actual witness and the original root ABI.
A staged external value is not terminal: its mandatory bind frame rules it out.
No empty-target-stack premise is imposed; supported case labels are retained. -/
theorem ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.terminalYield_of_control
    {program : Fir.LeanIR.ImpureProgram} {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {externals : ExternalImpl} {rootResult : AbiKind} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host} {value : Value}
    (related : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals rootResult witness source target)
    (control : source.control = .yielded value)
    (empty : source.frames = []) :
    ∃ context sourceFunction targetStore targetLocals physical
        functionResult expectedResult,
      ConcreteStructuredYieldFocus context sourceFunction source.runtime
        source.env value targetStore targetLocals witness rootResult physical source target ∧
      ConcreteStructuredSupportedFrameStack program sourceModule targetModule
        hosts functionResult expectedResult source.frames target.frames := by
  cases related with
  | code _ related _ =>
      have impossible := related.core.core.focus.sourceControlEq
      rw [control] at impossible
      cases impossible
  | directReady related _ =>
      have impossible := related.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | saturatedReady related _ =>
      have impossible := related.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | lazyReady related _ =>
      have impossible := related.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | externalReady related _ =>
      have impossible := related.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | externalBind related _ =>
      have impossible := related.core.bindFocus.sourceFramesEq
      rw [empty] at impossible
      cases impossible
  | returned related rooted =>
      have valueEq := Control.yielded.inj
        (control.symm.trans related.yielded.sourceControlEq)
      have yielded := related.yieldAtRoot_of_empty rooted empty
      rw [← related.yielded.sourceRuntimeEq, ← related.yielded.sourceEnvEq,
        ← valueEq] at yielded
      exact ⟨_, _, _, _, _, _, _, yielded, related.frames.supported⟩

/-- Compose the accepted rooted prefix with executable Talos return adequacy.
The internal function form retains an arbitrary caller operand tail. The
initial relation selects this entry function's ABI; no final-kind equation is
requested, and no target path is a premise. -/
theorem ConcreteSupportedFunction.terminatesWith_of_rootedExecSteps
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context code sourceModule
      sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    {initial : Wasm.Store Host} {parameters callerTail : List Wasm.Value}
    {initialWitness : RefinementWitness}
    {sourceInitial sourceFinal : MachineState} {count : Nat}
    {observation : Observation} {value : Value}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (initialRelated : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals spec.sourceResultKind initialWitness
      sourceInitial (StructuredWasmState.functionEntry spec.targetFunction initial
        (parameters ++ callerTail)))
    (steps : ExecSteps externals count sourceInitial sourceFinal)
    (done : executeStep externals sourceFinal = .done observation)
    (success : observation.outcome = .returned value) :
    Wasm.TerminatesWith hosts.env targetModule.wasmModule
      spec.targetFunctionIndex initial (parameters ++ callerTail)
      (RefinedReturnPost sourceFinal.runtime value spec.sourceResultKind callerTail) := by
  obtain ⟨targetCount, targetAfter, nextWitness, targetPath, terminal, _⟩ :=
    initialRelated.execSteps admission addressSpaceSafety steps
  obtain ⟨control, empty, _⟩ := sourceExecReturned_terminal done success
  obtain ⟨_, _, _, _, _, _, _, yielded, frames⟩ :=
    terminal.terminalYield_of_control control empty
  exact spec.terminatesWith_of_structuredYield parameterCount targetPath
    yielded frames empty

/-- Regression: terminal extraction supplies both real target completion and
the exact-root postcondition, even when administrative target labels remain.
The source continuation alone is required to be empty. -/
example
    {program : Fir.LeanIR.ImpureProgram} {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {externals : ExternalImpl} {rootResult : AbiKind} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host} {value : Value}
    (related : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals rootResult witness source target)
    (control : source.control = .yielded value) (empty : source.frames = []) :
    ∃ (store : Wasm.Store Host) (locals : Wasm.Locals) (physical : Wasm.Value) (count : Nat),
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) count target
        ⟨store, .halted (physical :: locals.values), []⟩ ∧
      RefinedReturnPost source.runtime value rootResult locals.values store
        (physical :: locals.values) := by
  obtain ⟨_, _, store, locals, physical, _, _, yielded, frames⟩ :=
    related.terminalYield_of_control control empty
  obtain ⟨count, path⟩ := yielded.finitePath_halted frames empty
  exact ⟨store, locals, physical, count, path, yielded.refinedReturnPost locals.values⟩

section Export

variable
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    (contextCaches : context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {initial : Wasm.Store Host} {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value} {observation : Observation} {value : Value}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (runtimeInvariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse) initialWitness)

include admission addressSpaceSafety contextCaches parameterCount runtimeInvariant

/-- A successful source evaluation implies an executable export return at the
export's exact selected ABI. The source observation, including its runtime,
is retained. Production validation derives the initial rooted relation.
There is no existential result kind, client root equality, new per-program
simulation invariant or target-execution premise. The two current-step laws
and existing entry-runtime invariant remain explicit. -/
theorem ConcreteSupportedExport.terminatesWith_of_rootedExecEvaluates
    (evaluation : ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv code) observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters
        (RefinedReturnPost resultRuntime value spec.sourceResultKind []) := by
  obtain ⟨count, sourceFinal, steps, done⟩ := evaluation
  have initialRelated : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals spec.sourceResultKind initialWitness
      (sourceCodeState context sourceRuntime sourceEnv code)
      (StructuredWasmState.functionEntry spec.targetFunction initial
        (parameters ++ [])) := by
    simpa only [List.append_nil, StructuredWasmState.functionEntry,
      concreteStructuredFunctionEntry, ← parameterCount, List.take_length] using
      spec.rootedPreciseCodeGlobalRoot contextCaches runtimeInvariant
  have execution :=
    spec.toConcreteSupportedFunction.terminatesWith_of_rootedExecSteps
      admission addressSpaceSafety parameterCount initialRelated steps done success
  refine ⟨sourceFinal.runtime, ?_, spec.targetFunctionIndex, spec.exported, ?_⟩
  · simpa only [observe, ReturnedObservation] using
      (sourceExecReturned_terminal done success).2.2
  · simpa only [List.append_nil] using execution

/-- Executable interpreter evidence reaches the same exact-root result.
Source fuel witnesses only source completion; adequate target fuel is derived
by the simulation and the existing executable adequacy theorem. -/
theorem ConcreteSupportedExport.terminatesWith_of_rootedRun
    {fuel : Nat}
    (execution : Fir.LeanIR.Impure.run fuel externals
      (sourceCodeState context sourceRuntime sourceEnv code) = .done observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters
        (RefinedReturnPost resultRuntime value spec.sourceResultKind []) :=
  spec.terminatesWith_of_rootedExecEvaluates admission addressSpaceSafety
    contextCaches parameterCount runtimeInvariant
    (run_done_sound externals observation fuel _ execution) success

/-- Regression: actual exact-root assembly entails the former existential-kind
shape. It cannot be relabelled at an arbitrary ABI without additional proof. -/
example
    (evaluation : ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv code) observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime kind,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters (RefinedReturnPost resultRuntime value kind []) := by
  obtain ⟨runtime, observationEq, execution⟩ :=
    spec.terminatesWith_of_rootedExecEvaluates admission addressSpaceSafety
      contextCaches parameterCount runtimeInvariant evaluation success
  fail_if_success
    have : ∀ arbitraryKind,
        ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
          initial parameters (RefinedReturnPost runtime value arbitraryKind []) := by
      intro arbitraryKind
      exact execution
  exact ⟨runtime, spec.sourceResultKind, observationEq, execution⟩

end Export

end FirTalos.Concrete
