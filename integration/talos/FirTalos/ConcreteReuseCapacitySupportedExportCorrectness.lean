import FirTalos.ConcreteReuseCapacityCacheCorrectness
import FirTalos.ConcreteSupportedExportCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- A capacity-certified generated body supplies T1's existing successful
declaration theorem by conservative erasure. -/
theorem ConcreteSupportedExport.toSuccessfulDeclarationOfReuseCapacity
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceExternals : ExternalImpl}
    {resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction []
        target.wasmModule hosts.env sourceExternals [] sourceRuntime sourceEnv
        sourceCode spec.targetBody initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        resultFacts resultRuntime resultValue resultKind resultStore
        resultWitness physical)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    SuccessfulDeclaration context sourceModule sourceFunction
      target.wasmModule hosts.env sourceExternals sourceRuntime resultRuntime
      sourceEnv sourceCode spec.targetFunction spec.targetFunctionIndex initial
      resultStore initialWitness resultWitness parameters resultKind resultValue
      physical :=
  spec.toSuccessfulDeclaration simulation.erase parameterCount

/-- The same supported-export certificate is hereditary when its
capacity-aware body simulation is retained: callers may frame arbitrary old
values and retained allocation headers across the declaration execution. -/
theorem ConcreteSupportedExport.toCapacityPreservingSuccessfulDeclarationOfReuseCapacity
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceExternals : ExternalImpl}
    {resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction []
        target.wasmModule hosts.env sourceExternals [] sourceRuntime sourceEnv
        sourceCode spec.targetBody initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        resultFacts resultRuntime resultValue resultKind resultStore
        resultWitness physical)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    CapacityPreservingSuccessfulDeclaration context sourceModule sourceFunction
      target.wasmModule hosts.env sourceExternals sourceRuntime resultRuntime
      sourceEnv sourceCode spec.targetFunction spec.targetFunctionIndex initial
      resultStore initialWitness resultWitness parameters resultKind resultValue
      physical :=
  .ofSimulation
    (spec.toSuccessfulDeclarationOfReuseCapacity simulation parameterCount)
    simulation

/-- Capacity-aware T3: the existing source/target correctness result is
retained, and the selected return state additionally realizes the final
validator fact map. -/
theorem ConcreteSupportedExport.correctOfReuseCapacity
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceExternals : ExternalImpl}
    {resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction []
        target.wasmModule hosts.env sourceExternals [] sourceRuntime sourceEnv
        sourceCode spec.targetBody initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        resultFacts resultRuntime resultValue resultKind resultStore
        resultWitness physical)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) ∧
      ∃ resultEnv resultLocals,
        ReuseCapacityStateRelated resultFacts sourceFunction resultRuntime
          resultEnv resultStore resultLocals resultWitness := by
  have ordinary :=
    spec.correct (callerTail := callerTail) simulation.erase parameterCount
  exact ⟨ordinary.1, ordinary.2, simulation.finalRelated⟩

end FirTalos.Concrete
