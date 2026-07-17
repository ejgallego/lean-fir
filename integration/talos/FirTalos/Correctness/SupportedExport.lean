import FirTalos.Correctness.Function
import Fir.Wasm.WellFormed

namespace FirTalos.Correctness

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure

/--
Checked whole-pipeline evidence for one generated export in the initial W4
fragment. This packages the facts that are independent of the local semantic
induction: fragment admission, lowering, adaptation, host resolution, export
resolution, and the single-result ABI.
-/
structure SupportedExport
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
  adapted : adapt sourceModule = .ok target
  hostsResolved : resolveHosts sourceModule = .ok hosts
  hostsMatch : HostsMatch hosts sourceModule
  targetFunctionIndex : Nat
  targetFunction : Wasm.Function
  exported :
    target.wasmModule.findExport exportName = some targetFunctionIndex
  notImport : target.wasmModule.imports[targetFunctionIndex]? = none
  targetFunctionFound :
    target.wasmModule.funcs[
        targetFunctionIndex - target.wasmModule.imports.length]? =
      some targetFunction
  singleResult : targetFunction.results.length = 1

/-- A checked supported export carries the host-environment contract it uses. -/
theorem SupportedExport.hostsSatisfy
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    (spec : SupportedExport program context code sourceModule sourceFunction
      target hosts exportName) :
    hosts.env.Satisfies target.wasmModule hosts.spec :=
  resolvedHosts_satisfy_adapted spec.adapted spec.hostsMatch

/-- Total correctness of an export entails its fuel-free partial contract. -/
theorem ExportTerminatesWith.toPartiallyMeets
    {hostEnv : Wasm.HostEnv RuntimeHost} {module : Wasm.Module}
    {exportName : String} {initial : Wasm.Store RuntimeHost}
    {args : List Wasm.Value}
    {Post : Wasm.Store RuntimeHost → List Wasm.Value → Prop}
    (correct : ExportTerminatesWith hostEnv module exportName initial args Post) :
    ExportPartiallyMeets hostEnv module exportName initial args Post := by
  rcases correct with ⟨functionIndex, exported, terminates⟩
  exact ⟨functionIndex, exported, terminates.toPartiallyMeets⟩

/--
Reusable W4 export theorem for a closed, single-result return in the supported
fragment. The observation premise remains explicit because the comparison
policy also checks reachable-heap well-formedness and is not reflexive for
observations with dangling locations.
-/
theorem SupportedExport.terminatesWithRelated_of_return
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    (spec : SupportedExport program context code sourceModule sourceFunction
      target hosts exportName)
    {initialSourceRuntime resultSourceRuntime : RuntimeState}
    {sourceValue : Value} {kind : AbiKind}
    {initial : Wasm.Store RuntimeHost}
    (related :
      compareObservations (ReturnedObservation resultSourceRuntime sourceValue)
          (.returned sourceValue resultSourceRuntime) =
        .related (ReturnedObservation resultSourceRuntime sourceValue)
          (.returned sourceValue resultSourceRuntime))
    (correct :
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
        initialSourceRuntime [] code spec.targetFunction.body initial
        (spec.targetFunction.toLocals []) []
        (ReturnPost resultSourceRuntime sourceValue kind [])) :
    ExportTerminatesWith hosts.env target.wasmModule exportName initial []
      (RelatedPost #[kind]
        (ReturnedObservation resultSourceRuntime sourceValue)) := by
  apply CodeWP.toExportTerminatesWithRelated_of_return
    spec.exported spec.notImport spec.targetFunctionFound rfl spec.singleResult
    related
  simpa [Wasm.Function.toLocals] using correct

/-- Partial correctness is an immediate corollary of the supported export theorem. -/
theorem SupportedExport.partiallyMeetsRelated_of_return
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    (spec : SupportedExport program context code sourceModule sourceFunction
      target hosts exportName)
    {initialSourceRuntime resultSourceRuntime : RuntimeState}
    {sourceValue : Value} {kind : AbiKind}
    {initial : Wasm.Store RuntimeHost}
    (related :
      compareObservations (ReturnedObservation resultSourceRuntime sourceValue)
          (.returned sourceValue resultSourceRuntime) =
        .related (ReturnedObservation resultSourceRuntime sourceValue)
          (.returned sourceValue resultSourceRuntime))
    (correct :
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
        initialSourceRuntime [] code spec.targetFunction.body initial
        (spec.targetFunction.toLocals []) []
        (ReturnPost resultSourceRuntime sourceValue kind [])) :
    ExportPartiallyMeets hosts.env target.wasmModule exportName initial []
      (RelatedPost #[kind]
        (ReturnedObservation resultSourceRuntime sourceValue)) :=
  (spec.terminatesWithRelated_of_return related correct).toPartiallyMeets

end FirTalos.Correctness
