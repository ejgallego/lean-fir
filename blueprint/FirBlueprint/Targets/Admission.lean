import FirTalos.ConcreteRootedTerminal

/-!
Blueprint-owned draft targets. Production modules must never import this module.
The two explicit holes are associated with nodes in Chapters/W6.lean. They are
specification/proof work, not accepted FIR results or immutable contribution tasks.
-/
set_option autoImplicit false

namespace FirBlueprint.Targets

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness
open FirTalos.Concrete

/-- Draft primitive external semantics. This must describe actual request/response
behavior (including Int/Nat/scalar responses and supported initializer effects).
It must not encode compiler admission, exclude supported source cases, or choose
future target executions. Its body is deliberately an exposed specification hole.
Review satisfiability against the intended implementations before freezing it. -/
noncomputable def externalSpec : ExternalSpec := by
  sorry

/-- Draft admission-construction target. The supported-function and recursively
validated current-outcome guards live in the conclusion's `code` field.
Finite runtime safety and primitive external semantics remain execution contracts.
The present backend relation may need revision to cover heap misses and schema
provenance; elaboration does not establish that this draft statement is provable. -/
theorem admission_of_validation
    {program : Fir.LeanIR.ImpureProgram} {sourceModule : Fir.Wasm.Module}
    {targetModule : FirTalos.AdaptedModule} {hosts : ResolvedHosts} {externals : ExternalImpl}
    (externalContract : externals.Implements externalSpec)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety program
      sourceModule targetModule hosts externals) :
    ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals := by
  sorry

section Export

variable
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : FirTalos.AdaptedModule}
    {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : ExternalImpl}
    (externalContract : externals.Implements externalSpec)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety program
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


include externalContract finiteRuntimeSafety addressSpaceSafety contextCaches parameterCount runtimeInvariant

/-- Checked assembly of the draft successful-return target. The admission premise
is supplied by the visible open theorem above. All other production endpoint
parameters and its exact observation/result ABI are preserved. -/
theorem return_of_validation
    (evaluation : ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv code) observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters
        (RefinedReturnPost resultRuntime value spec.sourceResultKind []) := by
  exact spec.terminatesWith_of_rootedExecEvaluates
    (admission_of_validation externalContract finiteRuntimeSafety)
    addressSpaceSafety contextCaches parameterCount runtimeInvariant evaluation success

end Export
end FirBlueprint.Targets
