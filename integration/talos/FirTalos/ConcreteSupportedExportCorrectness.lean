import FirTalos.ConcreteProgramCorrectness
import FirTalos.ConcreteResolver
import Fir.Wasm.WellFormed

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- Fuel-free concrete target correctness for a function selected by exported
name rather than by a separately supplied function index. -/
def ConcreteExportTerminatesWith
    (hostEnv : Wasm.HostEnv Host)
    (module : Wasm.Module)
    (exportName : String)
    (initial : Wasm.Store Host)
    (args : List Wasm.Value)
    (Post : Wasm.Store Host → List Wasm.Value → Prop) : Prop :=
  ∃ functionIndex,
    module.findExport exportName = some functionIndex ∧
      Wasm.TerminatesWith hostEnv module functionIndex initial args Post

/-- The lowering context and the selected symbolic function assign the same
ABI kind and numeric slot to every successfully compiled local read. This is
a static invariant of `lowerDecl`; keeping it explicit here prevents dynamic
simulation evidence from standing in for compiler layout correctness. -/
def LocalLayoutAligned
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) : Prop :=
  ∀ {fvarId : FVarId} {kind : AbiKind},
    Fir.Wasm.getLocal context fvarId = .ok (.localGet fvarId, kind) →
      ∃ index,
        findFVar? (functionBindings sourceFunction) fvarId = some index ∧
          (functionBindings sourceFunction)[index]?.map Prod.snd = some kind

/-- Static whole-pipeline evidence for one concrete generated export.

`bodyAdapted` is the crucial compiler-facing equation: it ties the selected
source code to the actual generated target body through `compileCode` and the
numeric Talos adapter. Dynamic source behavior and target-state refinement are
deliberately absent from this static package. -/
structure ConcreteSupportedExport
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (code : LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (target : AdaptedModule)
    (hosts : ResolvedHosts)
    (exportName : String) where
  programSupported : Fir.Wasm.WasmSupported program
  contextProgram : context.program = program
  lowered : Fir.Wasm.lowerSupported program = .ok sourceModule
  sourceFunctionIndex : Nat
  sourceFunctionFound :
    sourceModule.functions[sourceFunctionIndex]? = some sourceFunction
  localsAligned : LocalLayoutAligned context sourceFunction
  adapted : adapt sourceModule = .ok target
  hostsResolved : resolveHosts sourceModule = .ok hosts
  hostsAligned :
    target.wasmModule.imports.length = hosts.hosts.length
  targetFunctionIndex : Nat
  targetFunction : Wasm.Function
  exported :
    target.wasmModule.findExport exportName = some targetFunctionIndex
  notImport :
    target.wasmModule.imports[targetFunctionIndex]? = none
  targetFunctionFound :
    target.wasmModule.funcs[
        targetFunctionIndex - target.wasmModule.imports.length]? =
      some targetFunction
  bodyAdapted :
    CodeAdapted context sourceModule sourceFunction [] code targetFunction.body
  singleResult : targetFunction.results.length = 1

/-- Successful concrete resolution provides the exact host contract installed
for the adapted module. -/
theorem ConcreteSupportedExport.hostsSatisfy
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName) :
    hosts.env.Satisfies target.wasmModule hosts.spec :=
  hosts.satisfies target.wasmModule spec.hostsAligned

/-- The syntax-directed proof for the statically selected generated function
constructs T1's exact successful-declaration certificate. -/
theorem ConcreteSupportedExport.toSuccessfulDeclaration
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
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction []
        target.wasmModule hosts.env sourceExternals sourceRuntime sourceEnv
        sourceCode spec.targetFunction.body initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        resultRuntime resultValue resultKind resultStore resultWitness physical)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    SuccessfulDeclaration context sourceModule sourceFunction
      target.wasmModule hosts.env sourceExternals sourceRuntime resultRuntime
      sourceEnv sourceCode spec.targetFunction spec.targetFunctionIndex initial
      resultStore initialWitness resultWitness parameters resultKind resultValue
      physical :=
  simulation.toSuccessfulDeclaration parameterCount spec.singleResult
    spec.notImport spec.targetFunctionFound

/-- T3 whole-export success. The target function and index come from the
generated module's exported-name lookup, while T2 supplies exact source
execution and concrete body correctness for that selected function. -/
theorem ConcreteSupportedExport.correct
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
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction []
        target.wasmModule hosts.env sourceExternals sourceRuntime sourceEnv
        sourceCode spec.targetFunction.body initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        resultRuntime resultValue resultKind resultStore resultWitness physical)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) := by
  have declaration :=
    spec.toSuccessfulDeclaration simulation parameterCount
  exact ⟨declaration.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    declaration.terminatesWith callerTail⟩

end FirTalos.Concrete
