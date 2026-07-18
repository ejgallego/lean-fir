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
  | effect
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        CodeEvaluates context nextRuntime sourceEnv continuation
          resultRuntime resultValue) :
      CodeEvaluates context sourceRuntime sourceEnv code resultRuntime resultValue

/-- Canonical executable-interpreter state for a W4 source-code node. -/
def sourceCodeState (context : Fir.Wasm.Context) (runtime : RuntimeState)
    (env : Env) (code : LCNF.Code .impure) : MachineState :=
  { program := context.program
    control := .code code
    env
    runtime }

/-- Canonical terminal control state reached after a W4 source return. -/
def sourceYieldState (context : Fir.Wasm.Context) (runtime : RuntimeState)
    (env : Env) (value : Value) : MachineState :=
  { program := context.program
    control := .yielded value
    env
    runtime }

private theorem evalLetValue_sourceCodeState_control_independent
    (context : Fir.Wasm.Context) (runtime : RuntimeState) (env : Env)
    (code : LCNF.Code .impure) (decl : LCNF.LetDecl .impure) :
    evalLetValue (sourceCodeState context runtime env code) decl =
      evalLetValue
        (sourceCodeState context runtime env (.return decl.fvarId)) decl := by
  cases decl.value <;> rfl

private theorem executeStep_source_return (externals : ExternalImpl)
    (context : Fir.Wasm.Context) (runtime : RuntimeState) (env : Env)
    (result : Lean.FVarId) (value : Value)
    (sourceLookup : lookup env result = some value) :
    executeStep externals (sourceCodeState context runtime env (.return result)) =
      .next (sourceYieldState context runtime env value) := by
  simp [executeStep, coreStep, sourceCodeState, sourceYieldState, lookupValue,
    sourceLookup]

private theorem executeStep_source_let (externals : ExternalImpl)
    (context : Fir.Wasm.Context) (runtime nextRuntime : RuntimeState)
    (env : Env) (decl : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure) (value : Value)
    (sourceStep : SourceLetResult context runtime env decl nextRuntime value) :
    executeStep externals
        (sourceCodeState context runtime env (.let decl continuation)) =
      .next (sourceCodeState context nextRuntime
        (bind env decl.fvarId value) continuation) := by
  have evaluated :
      evalLetValue
          (sourceCodeState context runtime env (.let decl continuation)) decl =
        .ok (nextRuntime, .value value) := by
    rw [evalLetValue_sourceCodeState_control_independent]
    exact sourceStep
  unfold sourceCodeState at evaluated
  simp [executeStep, coreStep, sourceCodeState, evaluated]

private theorem executeStep_source_cases (externals : ExternalImpl)
    (context : Fir.Wasm.Context) (runtime : RuntimeState) (env : Env)
    (cases : LCNF.Cases .impure) (selected : LCNF.Code .impure)
    (sourceStep : SourceCaseResult runtime env cases selected) :
    executeStep externals (sourceCodeState context runtime env (.cases cases)) =
      .next (sourceCodeState context runtime env selected) := by
  rcases sourceStep with ⟨discrValue, tag, found, tagged, chosen⟩
  simp [executeStep, coreStep, sourceCodeState, found, tagged, chosen]

private theorem executeStep_source_yield (externals : ExternalImpl)
    (context : Fir.Wasm.Context) (runtime : RuntimeState) (env : Env)
    (value : Value) :
    executeStep externals (sourceYieldState context runtime env value) =
      .done (ReturnedObservation runtime value) := by
  rfl

/--
The proof-facing W4 source evaluation is sound for the repository's executable
interpreter. Because the fragment is call-free, the result is independent of
the external implementation.
-/
theorem CodeEvaluates.execEvaluates
    {context : Fir.Wasm.Context} {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env} {code : LCNF.Code .impure} {resultValue : Value}
    (evaluation :
      CodeEvaluates context sourceRuntime sourceEnv code resultRuntime
        resultValue)
    (externals : ExternalImpl) :
    ExecEvaluates externals (sourceCodeState context sourceRuntime sourceEnv code)
      (ReturnedObservation resultRuntime resultValue) := by
  induction evaluation with
  | @ret sourceEnv result sourceValue sourceRuntime sourceLookup =>
      refine ⟨1, sourceYieldState context sourceRuntime sourceEnv sourceValue,
        .step ?_ (.refl _), ?_⟩
      · exact executeStep_source_return externals context sourceRuntime sourceEnv
          result sourceValue sourceLookup
      · exact executeStep_source_yield externals context sourceRuntime sourceEnv
          sourceValue
  | letValue sourceStep _ ih =>
      rcases ih with ⟨count, final, steps, done⟩
      exact ⟨count + 1, final,
        .step (executeStep_source_let externals context _ _ _ _ _ _ sourceStep)
          steps,
        done⟩
  | caseOf sourceStep _ ih =>
      rcases ih with ⟨count, final, steps, done⟩
      exact ⟨count + 1, final,
        .step (executeStep_source_cases externals context _ _ _ _ sourceStep)
          steps,
        done⟩
  | effect sourceStep _ ih =>
      rcases ih with ⟨count, final, steps, done⟩
      exact ⟨count + 1, final,
        .step (by simpa [sourceCodeState] using sourceStep externals) steps,
        done⟩

private theorem execSteps_compose
    {externals : ExternalImpl} {prefixCount suffixCount : Nat}
    {first middle last : MachineState}
    (firstSteps : ExecSteps externals prefixCount first middle)
    (lastSteps : ExecSteps externals suffixCount middle last) :
    ∃ count, ExecSteps externals count first last := by
  induction firstSteps with
  | refl => exact ⟨suffixCount, lastSteps⟩
  | step head _ ih =>
      obtain ⟨count, steps⟩ := ih lastSteps
      exact ⟨count + 1, .step head steps⟩

/-- An exact external-let prefix followed by a call-free `CodeEvaluates`
continuation yields a real executable source run under the same installed
external implementation. -/
theorem SourceExternalLetResult.thenCodeEvaluates
    {context : Fir.Wasm.Context} {externals : ExternalImpl}
    {sourceRuntime nextRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {sourceValue resultValue : Value}
    (sourceStep : SourceExternalLetResult context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue)
    (continued : CodeEvaluates context nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) continuation resultRuntime
      resultValue) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
      (ReturnedObservation resultRuntime resultValue) := by
  have externalSteps :
      ExecSteps externals 3
        (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
        (sourceCodeState context nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation) := by
    unfold SourceExternalLetResult at sourceStep
    simpa [sourceCodeState] using sourceStep
  rcases continued.execEvaluates externals with
    ⟨suffixCount, final, suffix, done⟩
  obtain ⟨count, steps⟩ := execSteps_compose externalSteps suffix
  exact ⟨count, final, steps, done⟩

/-- Either exact lazy-cache prefix (three-step hit or four-step miss) composes
with the existing call-free source evaluation relation. -/
theorem SourceLazyLetResult.thenCodeEvaluates
    {path : LazyCachePath} {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {sourceValue resultValue : Value}
    (sourceStep : SourceLazyLetResult path context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue)
    (continued : CodeEvaluates context nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) continuation resultRuntime
      resultValue) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
      (ReturnedObservation resultRuntime resultValue) := by
  have lazySteps :
      ExecSteps externals path.sourceSteps
        (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
        (sourceCodeState context nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation) := by
    unfold SourceLazyLetResult at sourceStep
    simpa [sourceCodeState] using sourceStep
  rcases continued.execEvaluates externals with
    ⟨suffixCount, final, suffix, done⟩
  obtain ⟨count, steps⟩ := execSteps_compose lazySteps suffix
  exact ⟨count, final, steps, done⟩

/-- A terminating internal or closure-call prefix, including a recursive
callee, composes with the existing call-free continuation semantics. -/
theorem SourceCallLetResult.thenCodeEvaluates
    {context : Fir.Wasm.Context} {externals : ExternalImpl}
    {sourceRuntime nextRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {sourceValue resultValue : Value}
    (sourceStep : SourceCallLetResult context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue)
    (continued : CodeEvaluates context nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) continuation resultRuntime
      resultValue) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
      (ReturnedObservation resultRuntime resultValue) := by
  rcases sourceStep with ⟨prefixCount, callSteps⟩
  have callSteps' :
      ExecSteps externals prefixCount
        (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
        (sourceCodeState context nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation) := by
    simpa [sourceCodeState] using callSteps
  rcases continued.execEvaluates externals with
    ⟨suffixCount, final, suffix, done⟩
  obtain ⟨count, steps⟩ := execSteps_compose callSteps' suffix
  exact ⟨count, final, steps, done⟩

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
  | effect
      (step :
        EffectStepSimulates context sourceModule sourceFunction labels module
          hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
          targetRest targetStore nextStore targetLocals)
      (continued :
        CodeSimulation context sourceModule sourceFunction labels module hostEnv
          nextRuntime sourceEnv continuation targetRest nextStore targetLocals
          resultRuntime resultValue resultKind) :
      CodeSimulation context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code target targetStore targetLocals
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
  | effect step continued ih =>
      exact ⟨step.2.1, step.2.2.1,
        step.2.2.2.2 _ [] ih.2.2⟩

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
  | effect step _ ih => exact .effect step.1 ih

/-- A simulation certificate also yields an executable source run. -/
theorem CodeSimulation.execEvaluates
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
        resultRuntime resultValue resultKind)
    (externals : ExternalImpl) :
    ExecEvaluates externals (sourceCodeState context sourceRuntime sourceEnv code)
      (ReturnedObservation resultRuntime resultValue) :=
  simulation.sourceEvaluates.execEvaluates externals

/--
Proof-facing W4 theorem for one checked closed export: a syntax-directed
simulation certificate entails source evaluation and fuel-free total target
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

/--
Full W4 theorem for one checked closed export, stated over FIR's executable
source semantics and Talos's fuel-free exported-function semantics.
-/
theorem SupportedExport.execCorrect_of_simulation
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
    (canonicalLocals : targetLocals = spec.targetFunction.toLocals [])
    (externals : ExternalImpl) :
    ExecEvaluates externals (sourceCodeState context initialRuntime [] code)
        (ReturnedObservation resultRuntime resultValue) ∧
      ExportTerminatesWith hosts.env target.wasmModule exportName initial []
        (RelatedPost #[resultKind]
          (ReturnedObservation resultRuntime resultValue)) := by
  obtain ⟨source, targetCorrect⟩ :=
    spec.correct_of_simulation related simulation canonicalLocals
  exact ⟨source.execEvaluates externals, targetCorrect⟩

/-- Whole-export W5.6 theorem for one checked external-call prefix followed by
the existing call-free program fragment.  The same implementation is read
from the initial `RuntimeHost` by both the source execution and the semantic
target host. -/
theorem SupportedExport.execCorrect_of_externalLet
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    (spec : SupportedExport program context (.let decl continuation)
      sourceModule sourceFunction target hosts exportName)
    {initialRuntime nextRuntime resultRuntime : RuntimeState}
    {initial : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {sourceValue resultValue : Value} {resultKind : AbiKind}
    (related :
      compareObservations (ReturnedObservation resultRuntime resultValue)
          (.returned resultValue resultRuntime) =
        .related (ReturnedObservation resultRuntime resultValue)
          (.returned resultValue resultRuntime))
    (sourceStep : SourceExternalLetResult context initial.host.externals
      initialRuntime [] decl continuation nextRuntime sourceValue)
    (continued : CodeEvaluates context nextRuntime
      (bind [] decl.fvarId sourceValue) continuation resultRuntime resultValue)
    (correct :
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
        initialRuntime [] (.let decl continuation) spec.targetFunction.body
        initial targetLocals []
        (ReturnPost resultRuntime resultValue resultKind []))
    (canonicalLocals : targetLocals = spec.targetFunction.toLocals []) :
    ExecEvaluates initial.host.externals
        (sourceCodeState context initialRuntime [] (.let decl continuation))
        (ReturnedObservation resultRuntime resultValue) ∧
      ExportTerminatesWith hosts.env target.wasmModule exportName initial []
        (RelatedPost #[resultKind]
          (ReturnedObservation resultRuntime resultValue)) := by
  constructor
  · exact sourceStep.thenCodeEvaluates continued
  · apply spec.terminatesWithRelated_of_return related
    simpa [canonicalLocals] using correct

/-- Whole-export W5.7 theorem for a checked lazy zero-argument call prefix.
The path records whether the source and target take the initialized-cache hit
or the miss that evaluates and records the declaration exactly once. -/
theorem SupportedExport.execCorrect_of_lazyLet
    {path : LazyCachePath} {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    (spec : SupportedExport program context (.let decl continuation)
      sourceModule sourceFunction target hosts exportName)
    {initialRuntime nextRuntime resultRuntime : RuntimeState}
    {initial : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {sourceValue resultValue : Value} {resultKind : AbiKind}
    (related :
      compareObservations (ReturnedObservation resultRuntime resultValue)
          (.returned resultValue resultRuntime) =
        .related (ReturnedObservation resultRuntime resultValue)
          (.returned resultValue resultRuntime))
    (sourceStep : SourceLazyLetResult path context initial.host.externals
      initialRuntime [] decl continuation nextRuntime sourceValue)
    (continued : CodeEvaluates context nextRuntime
      (bind [] decl.fvarId sourceValue) continuation resultRuntime resultValue)
    (correct :
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
        initialRuntime [] (.let decl continuation) spec.targetFunction.body
        initial targetLocals []
        (ReturnPost resultRuntime resultValue resultKind []))
    (canonicalLocals : targetLocals = spec.targetFunction.toLocals []) :
    ExecEvaluates initial.host.externals
        (sourceCodeState context initialRuntime [] (.let decl continuation))
        (ReturnedObservation resultRuntime resultValue) ∧
      ExportTerminatesWith hosts.env target.wasmModule exportName initial []
        (RelatedPost #[resultKind]
          (ReturnedObservation resultRuntime resultValue)) := by
  constructor
  · exact sourceStep.thenCodeEvaluates continued
  · apply spec.terminatesWithRelated_of_return related
    simpa [canonicalLocals] using correct

/-- Whole-export W5.8 theorem for a terminating direct or closure-call
prefix. Recursive calls use the exact finite source witness and ordinary
fuel-free target call WP; no host callback executes a Wasm definition. -/
theorem SupportedExport.execCorrect_of_callLet
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    (spec : SupportedExport program context (.let decl continuation)
      sourceModule sourceFunction target hosts exportName)
    {initialRuntime nextRuntime resultRuntime : RuntimeState}
    {initial : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {sourceValue resultValue : Value} {resultKind : AbiKind}
    (related :
      compareObservations (ReturnedObservation resultRuntime resultValue)
          (.returned resultValue resultRuntime) =
        .related (ReturnedObservation resultRuntime resultValue)
          (.returned resultValue resultRuntime))
    (sourceStep : SourceCallLetResult context initial.host.externals
      initialRuntime [] decl continuation nextRuntime sourceValue)
    (continued : CodeEvaluates context nextRuntime
      (bind [] decl.fvarId sourceValue) continuation resultRuntime resultValue)
    (correct :
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
        initialRuntime [] (.let decl continuation) spec.targetFunction.body
        initial targetLocals []
        (ReturnPost resultRuntime resultValue resultKind []))
    (canonicalLocals : targetLocals = spec.targetFunction.toLocals []) :
    ExecEvaluates initial.host.externals
        (sourceCodeState context initialRuntime [] (.let decl continuation))
        (ReturnedObservation resultRuntime resultValue) ∧
      ExportTerminatesWith hosts.env target.wasmModule exportName initial []
        (RelatedPost #[resultKind]
          (ReturnedObservation resultRuntime resultValue)) := by
  constructor
  · exact sourceStep.thenCodeEvaluates continued
  · apply spec.terminatesWithRelated_of_return related
    simpa [canonicalLocals] using correct

end FirTalos.Correctness
