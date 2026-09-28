import FirTalos.ConcreteRegionCode

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- External-call control with the initializer's fixed-entry construction
scope. The represented call alone does not imply preservation of owned edges. -/
structure ConcreteStructuredRegionExternalCall
    (program : Fir.LeanIR.ImpureProgram) (context : Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule) (hosts : ResolvedHosts) (externals : ExternalImpl)
    (entryRuntime : RuntimeState) (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness) (facts : ReuseCapacityFacts) (bytes : Nat)
    {runtime nextRuntime : RuntimeState} {env : Env} {value : Value}
    {decl : Compiler.LCNF.LetDecl .impure}
    (site : ExternalCallShape context externals runtime env decl nextRuntime value)
    (operation : ExternalOperation) (kind : AbiKind) (imp : Wasm.ImportDecl)
    (labels : LabelContext) (continuation : Compiler.LCNF.Code .impure)
    (joins : JoinEnv) (sourceFrames : List Frame) (store : Wasm.Store Host)
    (locals : Wasm.Locals) (remainder : List Wasm.Value) (rest : Wasm.Program)
    (frames : List StructuredWasmFrame) (witness : RefinementWitness)
    (args : List Wasm.Value) (callIndex resultIndex : Nat)
    (source : MachineState) (target : StructuredWasmState Host) : Prop where
  control : ConcreteStructuredExternalCallControl program context sourceModule sourceFunction
    targetModule hosts externals site operation kind imp labels continuation joins sourceFrames
    store locals remainder rest frames witness args callIndex resultIndex source target
  scope : ConcreteStructuredResourceScope context sourceModule sourceFunction externals
    entryRuntime entryStore entryWitness facts bytes runtime env store locals witness
  region : HeapRegionClosed entryRuntime.nextLocation runtime.heap

/-- The external result has been produced, but not yet bound. Region evidence
describes the post-call heap; the entry anchor and saved caller locals remain. -/
structure ConcreteStructuredRegionExternalBind
    (context : Context) (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (entryRuntime : RuntimeState) (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness) (facts : ReuseCapacityFacts) (bytes : Nat)
    (labels : LabelContext) (runtime : RuntimeState) (env : Env) (value : Value)
    (result : FVarId) (continuation : Compiler.LCNF.Code .impure)
    (joins : JoinEnv) (sourceFrames : List Frame) (store : Wasm.Store Host)
    (locals : Wasm.Locals) (remainder : List Wasm.Value) (rest : Wasm.Program)
    (frames : List StructuredWasmFrame) (witness : RefinementWitness)
    (kind : AbiKind) (physical : Wasm.Value) (resultIndex : Nat)
    (source : MachineState) (target : StructuredWasmState Host) : Prop where
  focus : ConcreteStructuredExternalBindFocus context sourceModule sourceFunction labels
    runtime env value result continuation joins sourceFrames store locals remainder rest frames
    witness kind physical resultIndex source target
  scope : ConcreteStructuredResourceScope context sourceModule sourceFunction externals
    entryRuntime entryStore entryWitness facts bytes runtime env store locals witness
  region : HeapRegionClosed entryRuntime.nextLocation runtime.heap

/-- Staging leaves the heap, resources and construction cutoff unchanged.
The actual generated argument prefix and external-ready controls are derived. -/
theorem ConcreteStructuredRegionCodeCore.stageExternal
    {program : Fir.LeanIR.ImpureProgram} {context : Context}
    {rootCode : Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context rootCode sourceModule sourceFunction
      targetModule hosts)
    {externals : ExternalImpl} {entryRuntime runtime nextRuntime : RuntimeState}
    {entryStore store : Wasm.Store Host} {entryWitness witness : RefinementWitness}
    {facts : ReuseCapacityFacts} {bytes : Nat} {env : Env} {value : Value}
    {decl : Compiler.LCNF.LetDecl .impure} {continuation : Compiler.LCNF.Code .impure}
    {labels : LabelContext} {locals : Wasm.Locals} {code : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (active : ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals
      labels entryRuntime entryStore entryWitness facts bytes runtime env (.let decl continuation)
      store locals code witness source target)
    (site : ExternalCallShape context externals runtime env decl nextRuntime value) :
    ∃ args operation kind imp callIndex resultIndex,
    ∃ targetArguments rest : Wasm.Program, ∃ sourceAfter targetAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetArguments.length target targetAfter ∧
      ConcreteStructuredRegionExternalCall program context sourceModule sourceFunction
        targetModule hosts externals entryRuntime entryStore entryWitness facts bytes
        site operation kind imp labels continuation source.joins source.frames store locals
        locals.values rest target.frames witness args callIndex resultIndex sourceAfter targetAfter := by
  obtain ⟨args, operation, kind, imp, callIndex, resultIndex, targetArguments, rest,
      sourceAfter, targetAfter, step, path, control⟩ :=
    active.focus.advance_external_stage_of_shape spec site spec.localsAligned
  exact ⟨args, operation, kind, imp, callIndex, resultIndex, targetArguments, rest,
    sourceAfter, targetAfter, step, path, ⟨control, active.scope, active.region⟩⟩

/-- Cross the host operation, retaining the same entry anchor. Response evidence
provides runtime refinement; the operation producer separately proves region
preservation and residual budget. No post-call scope or target path is assumed. -/
theorem ConcreteStructuredRegionExternalCall.advance_call
    {program : Fir.LeanIR.ImpureProgram} {context : Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts} {externals : ExternalImpl}
    {entryRuntime runtime nextRuntime : RuntimeState}
    {entryStore store nextStore : Wasm.Store Host}
    {entryWitness witness nextWitness : RefinementWitness} {facts : ReuseCapacityFacts}
    {bytes cost : Nat} {env : Env} {value : Value} {decl : Compiler.LCNF.LetDecl .impure}
    {site : ExternalCallShape context externals runtime env decl nextRuntime value}
    {operation : ExternalOperation} {kind : AbiKind} {imp : Wasm.ImportDecl}
    {labels : LabelContext} {continuation : Compiler.LCNF.Code .impure}
    {joins : JoinEnv} {sourceFrames : List Frame} {locals : Wasm.Locals}
    {remainder : List Wasm.Value} {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    {args : List Wasm.Value} {callIndex resultIndex : Nat} {physical : Wasm.Value}
    {source : MachineState} {target : StructuredWasmState Host}
    (ready : ConcreteStructuredRegionExternalCall program context sourceModule sourceFunction
      targetModule hosts externals entryRuntime entryStore entryWitness facts bytes
      site operation kind imp labels continuation joins sourceFrames store locals remainder
      rest frames witness args callIndex resultIndex source target)
    (evidence : ConcreteExternalCallEvidence operation kind store args runtime nextRuntime
      value witness nextStore nextWitness physical)
    (budget : nextStore.host.runtime.heap.AddressSpaceBudget (bytes - cost))
    (preservesRegion : HeapRegionClosed entryRuntime.nextLocation runtime.heap →
      HeapRegionClosed entryRuntime.nextLocation nextRuntime.heap) :
    ∃ sourceAfter targetAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 1 target targetAfter ∧
      ConcreteStructuredRegionExternalBind context sourceModule sourceFunction externals
        entryRuntime entryStore entryWitness facts (bytes - cost) labels nextRuntime env value
        decl.fvarId continuation joins sourceFrames nextStore locals remainder rest frames
        nextWitness site.resultKind physical resultIndex sourceAfter targetAfter := by
  obtain ⟨sourceAfter, targetAfter, step, path, focus⟩ := ready.control.advance_call evidence
  have previous := ready.scope.budgetedPureExternal
  have nextFrame : ConcreteBudgetedPureExternalFrame sourceFunction externals
      (bytes - cost) nextRuntime env nextStore locals nextWitness := by
    refine ⟨⟨focus.frameAligned, budget⟩, ?_, ?_, ?_⟩
    · rw [evidence.externalsPreserved]; exact previous.2.1
    · rw [evidence.externalsPreserved]; exact previous.2.2.1
    · rw [evidence.externalsPreserved]; exact previous.2.2.2
  exact ⟨sourceAfter, targetAfter, step, path, ⟨focus,
    ready.scope.afterExternalCall nextFrame focus.stateRelated evidence,
    preservesRegion ready.region⟩⟩

/-- Binding only changes locals and erases the shadowed reuse fact. The heap,
region cutoff, entry history and exact suspended continuations are preserved. -/
theorem ConcreteStructuredRegionExternalBind.advance
    {context : Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {entryRuntime runtime : RuntimeState} {entryStore store : Wasm.Store Host}
    {entryWitness witness : RefinementWitness} {facts : ReuseCapacityFacts} {bytes : Nat}
    {labels : LabelContext} {env : Env} {value : Value} {result : FVarId}
    {continuation : Compiler.LCNF.Code .impure} {joins : JoinEnv} {sourceFrames : List Frame}
    {locals : Wasm.Locals} {remainder : List Wasm.Value} {rest : Wasm.Program}
    {frames : List StructuredWasmFrame} {kind : AbiKind} {physical : Wasm.Value}
    {resultIndex : Nat} {source : MachineState} {target : StructuredWasmState Host}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    (bound : ConcreteStructuredRegionExternalBind context sourceModule sourceFunction externals
      entryRuntime entryStore entryWitness facts bytes labels runtime env value result
      continuation joins sourceFrames store locals remainder rest frames witness kind physical
      resultIndex source target) :
    ∃ sourceAfter targetAfter updated resumedLocals,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 1 target targetAfter ∧
      locals.set? resultIndex physical = some updated ∧
      resumedLocals = { updated with values := remainder } ∧
      ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals labels
        entryRuntime entryStore entryWitness (eraseReuseCapacityFact facts result) bytes
        runtime (bind env result value) continuation store resumedLocals rest witness
        sourceAfter targetAfter ∧
      sourceAfter.joins = joins ∧ sourceAfter.frames = sourceFrames ∧
      targetAfter.frames = frames := by
  obtain ⟨sourceAfter, targetAfter, updated, resumedLocals, step, path, set, resumed,
      focus, joins, sourceFrames, targetFrames⟩ :=
    bound.focus.advance (externals := externals) (module := module) (hostEnv := hostEnv)
  have update : LocalUpdate locals resumedLocals resultIndex physical := by
    rw [resumed]
    have base := localUpdate_of_set? set
    refine ⟨?_, ?_⟩
    · simpa [Wasm.Locals.get] using base.1
    · intro other different
      simpa [Wasm.Locals.get] using base.2 different
  exact ⟨sourceAfter, targetAfter, updated, resumedLocals, step, path, set, resumed,
    ⟨focus, bound.scope.afterExternalBind focus.stateRelated focus.frameAligned
      bound.focus.resultFound update, bound.region⟩, joins, sourceFrames, targetFrames⟩

end FirTalos.Concrete
