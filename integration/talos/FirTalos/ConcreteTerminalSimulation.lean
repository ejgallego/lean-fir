import FirTalos.ConcreteTerminalExtraction
import FirTalos.ConcreteResumableWasm

/-!
# Successful return correctness from the existing compiler simulation

The current-step classifier constructs the ranked simulation, which supplies
the target prefix used by terminal extraction. The export theorem constructs
the initial relation from production validation and the ordinary entry frame.
Neither a target path nor a caller-chosen simulation relation is an export
premise. Source evaluation is the ordinary interpreter semantics, not a new
program-specific certificate or a claim that every execution terminates.

This is still a conditional compiler theorem: the universal classifier remains
a compiler-proof obligation, and the represented result kind is existential
rather than identified with the root export ABI. Input arity, runtime/host
contracts, and adequate resources remain explicit. No relation, admission
predicate, runtime behavior, or fault semantics is changed here.
-/

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- The existing ranked simulation supplies the finite target prefix; the
validated terminal relation supplies its executable completion. This internal
function form supports an arbitrary caller operand tail and uses exactly the
initial relation already required by the simulation. -/
theorem ConcreteSupportedFunction.terminatesWith_of_classifiedExecSteps
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context code sourceModule
      sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    (classifier : ConcreteStructuredCurrentStepClassifier program sourceModule
      targetModule hosts externals)
    {initial : Wasm.Store Host} {parameters callerTail : List Wasm.Value}
    {sourceInitial sourceFinal : MachineState} {count : Nat}
    {observation : Observation} {value : Value}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (initialRelated : ConcreteStructuredValidatedCodeGlobalOutcome program
      sourceModule targetModule hosts externals sourceInitial
      (StructuredWasmState.functionEntry spec.targetFunction initial
        (parameters ++ callerTail)))
    (steps : ExecSteps externals count sourceInitial sourceFinal)
    (done : executeStep externals sourceFinal = .done observation)
    (success : observation.outcome = .returned value) :
    ∃ kind, Wasm.TerminatesWith hosts.env targetModule.wasmModule
      spec.targetFunctionIndex initial (parameters ++ callerTail)
      (RefinedReturnPost sourceFinal.runtime value kind callerTail) := by
  obtain ⟨targetCount, targetAfter, targetPath, terminal, _⟩ :=
    classifier.toGeneratedTraceSimulation.execSteps initialRelated steps
  exact spec.terminatesWith_of_validatedReturn parameterCount targetPath
    terminal done success

/-- Successful source evaluation implies an executable refined export return,
conditional on the existing universal compiler classifier and entry contracts.
Production validation supplies the initial simulation relation; finite-prefix
composition supplies the target path. The full source observation is retained.

The result kind remains existential. Neither the root ABI provenance gap nor
the classifier obligation is hidden or discharged by this assembly theorem. -/
theorem ConcreteSupportedExport.terminatesWith_of_classifiedExecEvaluates
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : ExternalImpl}
    (classifier : ConcreteStructuredCurrentStepClassifier program sourceModule
      targetModule hosts externals)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {initial : Wasm.Store Host} {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value} {observation : Observation} {value : Value}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (runtimeInvariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (evaluation : ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv code) observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime kind,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters (RefinedReturnPost resultRuntime value kind []) := by
  obtain ⟨count, sourceFinal, steps, done⟩ := evaluation
  have initialRelated : ConcreteStructuredValidatedCodeGlobalOutcome program
      sourceModule targetModule hosts externals
      (sourceCodeState context sourceRuntime sourceEnv code)
      (StructuredWasmState.functionEntry spec.targetFunction initial
        (parameters ++ [])) := by
    simpa only [List.append_nil, StructuredWasmState.functionEntry,
      concreteStructuredFunctionEntry, ← parameterCount, List.take_length] using
      spec.validatedCodeGlobalRoot contextCaches runtimeInvariant
  obtain ⟨kind, execution⟩ :=
    spec.toConcreteSupportedFunction.terminatesWith_of_classifiedExecSteps
      classifier parameterCount initialRelated steps done success
  refine ⟨sourceFinal.runtime, kind, ?_, spec.targetFunctionIndex,
    spec.exported, ?_⟩
  · simpa only [observe, ReturnedObservation] using
      (sourceExecReturned_terminal done success).2.2
  · simpa only [List.append_nil] using execution

/-- The executable source interpreter is an alternative entry to the same
conditional result theorem. Source fuel is merely evidence of this successful
source run; target fuel and execution are derived by simulation and adequacy. -/
theorem ConcreteSupportedExport.terminatesWith_of_classifiedRun
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : ExternalImpl}
    (classifier : ConcreteStructuredCurrentStepClassifier program sourceModule
      targetModule hosts externals)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {initial : Wasm.Store Host} {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value} {observation : Observation} {value : Value}
    {fuel : Nat}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (runtimeInvariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (execution : Fir.LeanIR.Impure.run fuel externals
      (sourceCodeState context sourceRuntime sourceEnv code) = .done observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime kind,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters (RefinedReturnPost resultRuntime value kind []) := by
  exact spec.terminatesWith_of_classifiedExecEvaluates classifier contextCaches
    parameterCount runtimeInvariant
    (run_done_sound externals observation fuel _ execution) success

end FirTalos.Concrete
