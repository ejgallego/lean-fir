import FirTalos.ConcreteTerminalCorrectness
import FirTalos.ConcreteStructuredValidation

/-!
# Terminal extraction from the existing validated compiler relation

Successful source completion identifies a yielded value with no continuation.
Inverting the existing global relation then recovers the return refinement and
checked target frames needed by the executable return bridge. No simulation
relation, admission condition, or caller certificate is added here.

The represented result kind remains existential: deriving its equality with the
root export's selected result ABI is a separate provenance obligation.
-/

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Only an unframed yield can produce a successful final source observation.
All other terminal interpreter branches are faults. -/
theorem sourceCoreReturned_terminal
    {source : MachineState} {observation : Observation} {value : Value}
    (done : coreStep source = .done observation)
    (success : observation.outcome = .returned value) :
    source.control = .yielded value ∧ source.frames = [] ∧
      observation = observe source (.returned value) := by
  cases control : source.control with
  | yielded returned =>
      cases frames : source.frames with
      | nil =>
          simp only [coreStep, control, frames, CoreResult.done.injEq] at done
          subst observation
          simp only [observe, Outcome.returned.injEq] at success
          subst value
          exact ⟨rfl, rfl, rfl⟩
      | cons frame rest =>
          cases frame <;> simp [coreStep, control, frames] at done
  | invokeName name args =>
      simp only [coreStep, control, invokeDecl] at done
      repeat' first | (solve | cases done <;> cases success) | split at done
  | invokeValue function args =>
      simp only [coreStep, control, invokeClosure, invokeDecl] at done
      repeat' first | (solve | cases done <;> cases success) | split at done
  | code code =>
      cases code <;> simp only [coreStep, control] at done
      all_goals
        repeat' first | (solve | cases done <;> cases success) | split at done

/-- Executable external calls cannot manufacture a successful terminal
observation: a successful external response resumes the source machine. -/
theorem sourceExecReturned_terminal
    {externals : ExternalImpl} {source : MachineState}
    {observation : Observation} {value : Value}
    (done : executeStep externals source = .done observation)
    (success : observation.outcome = .returned value) :
    source.control = .yielded value ∧ source.frames = [] ∧
      observation = observe source (.returned value) := by
  cases step : coreStep source with
  | next after => simp [executeStep, step] at done
  | done result =>
      simp only [executeStep, step, ExecResult.done.injEq] at done
      subst result
      exact sourceCoreReturned_terminal step success
  | external request waiting =>
      simp only [executeStep, step] at done
      split at done
      · cases done
      · cases done
        cases success

/-- Extract only existing yield/frame evidence from the global relation.
Staged external results are excluded by their mandatory bind continuation;
all other non-return branches have non-yielded source control. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcome.terminalYield_of_control
    {program : Fir.LeanIR.ImpureProgram} {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {externals : ExternalImpl} {source : MachineState}
    {target : StructuredWasmState Host} {value : Value}
    (related : ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals source target)
    (control : source.control = .yielded value)
    (empty : source.frames = []) :
    ∃ context sourceFunction targetStore targetLocals witness kind physical
        functionResult expectedResult,
      ConcreteStructuredYieldFocus context sourceFunction source.runtime
        source.env value targetStore targetLocals witness kind physical source target ∧
      ConcreteStructuredSupportedFrameStack program sourceModule targetModule
        hosts functionResult expectedResult source.frames target.frames := by
  cases related with
  | code _ related =>
      have impossible := related.core.core.focus.sourceControlEq
      rw [control] at impossible
      cases impossible
  | directReady related =>
      have impossible := related.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | saturatedReady related =>
      have impossible := related.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | lazyReady related =>
      have impossible := related.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | externalReady related =>
      have impossible := related.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | externalBind related =>
      have impossible := related.core.bindFocus.sourceFramesEq
      rw [empty] at impossible
      cases impossible
  | returned related =>
      have valueEq := Control.yielded.inj
        (control.symm.trans related.yielded.sourceControlEq)
      have yielded := related.yielded
      rw [← related.yielded.sourceRuntimeEq, ← related.yielded.sourceEnvEq,
        ← valueEq] at yielded
      exact ⟨_, _, _, _, _, _, _, _, _, yielded, related.frames.supported⟩

/-- The maintained global relation supplies the whole terminal bridge input.
Only the finite target prefix remains for the simulation's prefix theorem to
provide. The existential kind is not claimed to be the entry result ABI. -/
theorem ConcreteSupportedFunction.terminatesWith_of_validatedReturn
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context code sourceModule
      sourceFunction targetModule hosts)
    {externals : ExternalImpl} {initial : Wasm.Store Host}
    {parameters callerTail : List Wasm.Value} {source : MachineState}
    {target : StructuredWasmState Host} {count : Nat}
    {observation : Observation} {value : Value}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (targetPrefix : FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
      count (StructuredWasmState.functionEntry spec.targetFunction initial
        (parameters ++ callerTail)) target)
    (related : ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals source target)
    (done : executeStep externals source = .done observation)
    (success : observation.outcome = .returned value) :
    ∃ kind, Wasm.TerminatesWith hosts.env targetModule.wasmModule
      spec.targetFunctionIndex initial (parameters ++ callerTail)
      (RefinedReturnPost source.runtime value kind callerTail) := by
  obtain ⟨control, empty, _⟩ := sourceExecReturned_terminal done success
  obtain ⟨_, _, _, _, _, kind, _, _, _, yielded, frames⟩ :=
    related.terminalYield_of_control control empty
  exact ⟨kind, spec.terminatesWith_of_structuredYield parameterCount
    targetPrefix yielded frames empty⟩

/-- Export specialization of successful terminal extraction. This is an
internal assembly theorem: no target path should be requested from an eventual
compiler-theorem client, and precise root-kind provenance is still open. -/
theorem ConcreteSupportedExport.terminatesWith_of_validatedReturn
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : ExternalImpl} {initial : Wasm.Store Host}
    {parameters : List Wasm.Value} {source : MachineState}
    {target : StructuredWasmState Host} {count : Nat}
    {observation : Observation} {value : Value}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (targetPrefix : FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
      count (StructuredWasmState.functionEntry spec.targetFunction initial parameters)
      target)
    (related : ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals source target)
    (done : executeStep externals source = .done observation)
    (success : observation.outcome = .returned value) :
    ∃ kind, ConcreteExportTerminatesWith hosts.env targetModule.wasmModule
      exportName initial parameters (RefinedReturnPost source.runtime value kind []) := by
  obtain ⟨kind, execution⟩ :=
    spec.toConcreteSupportedFunction.terminatesWith_of_validatedReturn
      (callerTail := []) parameterCount (by simpa using targetPrefix)
      related done success
  exact ⟨kind, spec.targetFunctionIndex, spec.exported, by simpa using execution⟩

end FirTalos.Concrete
