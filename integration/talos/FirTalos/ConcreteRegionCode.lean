import FirTalos.ConcreteFreshYield

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Active initializer code with a fixed construction cutoff. No result root is
chosen yet. The surrounding source/target frames remain those of the focus;
this is not the general suspended-stack relation for nested heap lazy calls. -/
structure ConcreteStructuredRegionCodeCore
    (context : Context) (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (labels : LabelContext) (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host) (entryWitness : RefinementWitness)
    (facts : ReuseCapacityFacts) (bytes : Nat)
    (runtime : RuntimeState) (env : Env) (code : Compiler.LCNF.Code .impure)
    (store : Wasm.Store Host) (locals : Wasm.Locals) (targetCode : Wasm.Program)
    (witness : RefinementWitness) (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  focus : ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
    runtime env code store locals targetCode witness source target
  scope : ConcreteStructuredResourceScope context sourceModule sourceFunction externals
    entryRuntime entryStore entryWitness facts bytes runtime env store locals witness
  region : HeapRegionClosed entryRuntime.nextLocation runtime.heap

/-- Every represented entry heap is closed above its allocation frontier.
The producer supplies neither graph separation nor a future returned value. -/
theorem ConcreteStructuredRegionCodeCore.atEntry
    {context : Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {labels : LabelContext} {runtime : RuntimeState} {env : Env}
    {code : Compiler.LCNF.Code .impure} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {targetCode : Wasm.Program} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host}
    {facts : ReuseCapacityFacts} {bytes : Nat}
    (focus : ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
      runtime env code store locals targetCode witness source target)
    (frame : ConcreteReuseCapacityCacheAbiFrame context sourceModule sourceFunction externals
      facts bytes runtime env store locals witness) :
    ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals labels
      runtime store witness facts bytes runtime env code store locals targetCode witness
      source target :=
  ⟨focus, .root frame, HeapRegionClosed.of_liveHeapRel focus.stateRelated.1.heap⟩

/-- Transport an active construction scope through an executed body fragment.
Region preservation is a producer obligation separate from ordinaryness and
representation transport; the entry anchor is not reset to the new runtime. -/
theorem ConcreteStructuredRegionCodeCore.afterBody_withoutReuseFacts
    {context : Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {labels nextLabels : LabelContext} {entryRuntime runtime nextRuntime : RuntimeState}
    {entryStore store nextStore : Wasm.Store Host}
    {entryWitness witness nextWitness : RefinementWitness}
    {bytes nextBytes : Nat} {env nextEnv : Env} {locals nextLocals : Wasm.Locals}
    {code nextCode : Compiler.LCNF.Code .impure} {targetCode nextTargetCode : Wasm.Program}
    {source nextSource : MachineState} {target nextTarget : StructuredWasmState Host}
    (active : ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals
      labels entryRuntime entryStore entryWitness [] bytes runtime env code store locals
      targetCode witness source target)
    (transports : RuntimeStepTransports runtime nextRuntime store nextStore witness nextWitness)
    (externalsEq : nextStore.host.externals = store.host.externals)
    (focus : ConcreteStructuredCodeFocus context sourceModule sourceFunction nextLabels
      nextRuntime nextEnv nextCode nextStore nextLocals nextTargetCode nextWitness nextSource nextTarget)
    (budget : nextStore.host.runtime.heap.AddressSpaceBudget nextBytes)
    (preservesRegion : HeapRegionClosed entryRuntime.nextLocation runtime.heap →
      HeapRegionClosed entryRuntime.nextLocation nextRuntime.heap) :
    ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals nextLabels
      entryRuntime entryStore entryWitness [] nextBytes nextRuntime nextEnv nextCode
      nextStore nextLocals nextTargetCode nextWitness nextSource nextTarget :=
  ⟨focus, active.scope.afterBody_withoutReuseFacts transports externalsEq
    focus.stateRelated focus.frameAligned budget, preservesRegion active.region⟩

/-- A source return and its two target instructions retain the construction
scope and region. Freshness of the selected root is independent of its ABI;
both the precise physical representation and target path are derived. -/
theorem ConcreteStructuredRegionCodeCore.advance_return
    {context : Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {labels : LabelContext} {entryRuntime runtime : RuntimeState}
    {entryStore store : Wasm.Store Host} {entryWitness witness : RefinementWitness}
    {facts : ReuseCapacityFacts} {bytes : Nat} {env : Env} {locals : Wasm.Locals}
    {targetCode : Wasm.Program} {source : MachineState} {target : StructuredWasmState Host}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host} {result : FVarId} {root : Location}
    (active : ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals
      labels entryRuntime entryStore entryWitness facts bytes runtime env (.return result)
      store locals targetCode witness source target)
    (aligned : LocalLayoutAligned context sourceFunction)
    (lookupResult : lookup env result = some (.object (.heap root)))
    (fresh : entryRuntime.nextLocation ≤ root) :
    ∃ kind physical sourceAfter targetAfter,
      getLocal context result = .ok (.localGet result, kind) ∧
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredFreshYieldCore context sourceModule sourceFunction externals
        entryRuntime entryStore entryWitness facts bytes runtime env store locals witness
        kind root physical sourceAfter targetAfter ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  obtain ⟨kind, physical, sourceAfter, targetAfter, compiled, step, path, focus,
      joins, sourceFrames, targetFrames⟩ := active.focus.advance_return aligned lookupResult
        (module := module) (hostEnv := hostEnv) (externals := externals)
  exact ⟨kind, physical, sourceAfter, targetAfter, compiled, step, path,
    ⟨focus, active.scope, active.region, fresh⟩, joins, sourceFrames, targetFrames⟩

end FirTalos.Concrete
