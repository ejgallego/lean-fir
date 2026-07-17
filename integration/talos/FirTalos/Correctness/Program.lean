import FirTalos.Correctness.SupportedExport

namespace FirTalos.Correctness

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure

/-- Successful source selection of one constructor-case branch. -/
def SourceCaseResult (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (cases : LCNF.Cases .impure) (selected : LCNF.Code .impure) : Prop :=
  ∃ discrValue tag,
    lookupValue sourceEnv cases.discr = .ok discrValue ∧
      getTag sourceRuntime discrValue = .ok tag ∧
      chooseAlt tag cases.alts.toList = some selected

/--
Big-step successful evaluation for the call-free W4 code fragment. Direct
`let` values use the same evaluator as the executable interpreter, and cases
record the branch chosen by the interpreter's tag/default policy.
-/
inductive CodeEvaluates (context : Fir.Wasm.Context) :
    RuntimeState → Env → LCNF.Code .impure → RuntimeState → Value → Prop where
  | ret
      (sourceLookup : lookup sourceEnv result = some sourceValue) :
      CodeEvaluates context sourceRuntime sourceEnv (.return result)
        sourceRuntime sourceValue
  | letValue
      (sourceStep :
        SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
          sourceValue)
      (continued :
        CodeEvaluates context nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation
          resultRuntime resultValue) :
      CodeEvaluates context sourceRuntime sourceEnv (.let decl continuation)
        resultRuntime resultValue
  | caseOf
      (sourceStep :
        SourceCaseResult sourceRuntime sourceEnv cases selected)
      (continued :
        CodeEvaluates context sourceRuntime sourceEnv selected
          resultRuntime resultValue) :
      CodeEvaluates context sourceRuntime sourceEnv (.cases cases)
        resultRuntime resultValue

/--
The case-specific W4 boundary. It records the source-selected branch and a
transformer that installs any proof of that branch beneath the generated case
chain. The transformer is where path-sensitive hit/miss and default handling
are discharged; the program-level induction remains independent of a fixture's
concrete test layout.
-/
def CasesStepSimulates
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (cases : LCNF.Cases .impure) (selected : LCNF.Code .impure)
    (target selectedTarget : Wasm.Program)
    (targetStore : Wasm.Store RuntimeHost) (targetLocals : Wasm.Locals)
    (resultRuntime : RuntimeState) (resultValue : Value) (resultKind : AbiKind) :
    Prop :=
  SourceCaseResult sourceRuntime sourceEnv cases selected ∧
    (CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv selected selectedTarget targetStore targetLocals
        [] (ReturnPost resultRuntime resultValue resultKind []) →
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv (.cases cases) target targetStore targetLocals
        [] (ReturnPost resultRuntime resultValue resultKind []))

/--
Syntax-directed semantic certificate for the current W4 fragment. Operation
rules provide one `LetStepSimulates`; case rules provide one selected-branch
transformer. The recursive structure, source evaluation, compiler composition,
and final `CodeWP` are shared by every supported program.
-/
inductive CodeSimulation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost) :
    RuntimeState → Env → LCNF.Code .impure → Wasm.Program →
      Wasm.Store RuntimeHost → Wasm.Locals → RuntimeState → Value → AbiKind →
      Prop where
  | ret
      (localCompiled :
        Fir.Wasm.getLocal context result = .ok (.localGet result, kind))
      (resultFound :
        findFVar? (functionBindings sourceFunction) result = some resultIndex)
      (kindAt :
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
      (sourceLookup : lookup sourceEnv result = some sourceValue)
      (stateRelated :
        StateRelated sourceFunction sourceRuntime sourceEnv targetStore
          targetLocals) :
      CodeSimulation context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv (.return result)
        [.localGet resultIndex, .ret] targetStore targetLocals sourceRuntime
        sourceValue kind
  | letValue
      (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        LetStepSimulates context sourceFunction module hostEnv decl targetValue
          sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
          targetLocals nextLocals resultIndex)
      (continued :
        CodeSimulation context sourceModule sourceFunction labels module hostEnv
          nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
          targetRest nextStore nextLocals resultRuntime resultValue resultKind) :
      CodeSimulation context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest) targetStore
        targetLocals resultRuntime resultValue resultKind
  | caseOf
      (step :
        CasesStepSimulates context sourceModule sourceFunction labels module
          hostEnv sourceRuntime sourceEnv cases selected target selectedTarget
          targetStore targetLocals resultRuntime resultValue resultKind)
      (continued :
        CodeSimulation context sourceModule sourceFunction labels module hostEnv
          sourceRuntime sourceEnv selected selectedTarget targetStore targetLocals
          resultRuntime resultValue resultKind) :
      CodeSimulation context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv (.cases cases) target targetStore targetLocals
        resultRuntime resultValue resultKind

/-- The shared program-level induction produces the local semantic judgment. -/
theorem CodeSimulation.toCodeWP
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {code : LCNF.Code .impure} {target : Wasm.Program}
    {targetStore : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {resultValue : Value} {resultKind : AbiKind}
    (simulation :
      CodeSimulation context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code target targetStore targetLocals
        resultRuntime resultValue resultKind) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv code target targetStore targetLocals []
      (ReturnPost resultRuntime resultValue resultKind []) := by
  induction simulation with
  | ret localCompiled resultFound kindAt sourceLookup stateRelated =>
      exact codeWP_return localCompiled resultFound kindAt sourceLookup
        stateRelated
  | letValue valueCompiled valueAdapted resultFound step continued ih =>
      exact codeWP_let valueCompiled valueAdapted resultFound step ih
  | caseOf step continued ih =>
      exact step.2 ih

/-- The same induction also yields successful source evaluation. -/
theorem CodeSimulation.sourceEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {code : LCNF.Code .impure} {target : Wasm.Program}
    {targetStore : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {resultValue : Value} {resultKind : AbiKind}
    (simulation :
      CodeSimulation context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code target targetStore targetLocals
        resultRuntime resultValue resultKind) :
    CodeEvaluates context sourceRuntime sourceEnv code resultRuntime resultValue := by
  induction simulation with
  | ret _ _ _ sourceLookup _ => exact .ret sourceLookup
  | letValue _ _ _ step _ ih => exact .letValue step.1 ih
  | caseOf step _ ih => exact .caseOf step.1 ih

/--
Full W4 theorem for one checked closed export: a syntax-directed simulation
certificate entails executable source evaluation and fuel-free total target
correctness under the shared observation policy.
-/
theorem SupportedExport.correct_of_simulation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context} {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    (spec : SupportedExport program context code sourceModule sourceFunction
      target hosts exportName)
    {initialRuntime resultRuntime : RuntimeState}
    {initial : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {resultValue : Value} {resultKind : AbiKind}
    (related :
      compareObservations (ReturnedObservation resultRuntime resultValue)
          (.returned resultValue resultRuntime) =
        .related (ReturnedObservation resultRuntime resultValue)
          (.returned resultValue resultRuntime))
    (simulation :
      CodeSimulation context sourceModule sourceFunction [] target.wasmModule
        hosts.env initialRuntime [] code spec.targetFunction.body initial
        targetLocals resultRuntime resultValue resultKind)
    (canonicalLocals : targetLocals = spec.targetFunction.toLocals []) :
    CodeEvaluates context initialRuntime [] code resultRuntime resultValue ∧
      ExportTerminatesWith hosts.env target.wasmModule exportName initial []
        (RelatedPost #[resultKind]
          (ReturnedObservation resultRuntime resultValue)) := by
  constructor
  · exact simulation.sourceEvaluates
  · apply spec.terminatesWithRelated_of_return related
    simpa [canonicalLocals] using simulation.toCodeWP

end FirTalos.Correctness
