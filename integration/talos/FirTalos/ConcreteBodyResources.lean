import FirTalos.ConcreteStructuredSimulation

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Compose the existing operation transports without changing the original
heap/witness boundary. This applies before cache publication; publication has
its separate, weaker retained-caller transport. -/
theorem RuntimeStepTransports.trans
    {first middle last : RuntimeState}
    {firstStore middleStore lastStore : Wasm.Store Host}
    {firstWitness middleWitness lastWitness : RefinementWitness}
    (left : RuntimeStepTransports first middle firstStore middleStore firstWitness middleWitness)
    (right : RuntimeStepTransports middle last middleStore lastStore middleWitness lastWitness) :
    RuntimeStepTransports first last firstStore lastStore firstWitness lastWitness := {
  hostDispatchPreserved := right.hostDispatchPreserved.trans left.hostDispatchPreserved
  witnessDispatchPreserved := right.witnessDispatchPreserved.trans left.witnessDispatchPreserved
  hostDescriptorsPreserved := right.hostDescriptorsPreserved.trans left.hostDescriptorsPreserved
  witnessDescriptorsPreserved := right.witnessDescriptorsPreserved.trans left.witnessDescriptorsPreserved
  witnessTransport := WitnessTransport.trans left.witnessTransport right.witnessTransport
  closureAllocationsPersistent := ClosureAllocationsPersistent.trans
    left.closureAllocationsPersistent right.closureAllocationsPersistent
  capacity := left.capacity.transAcross left.witnessTransport right.capacity
  ordinary := left.ordinary.trans right.ordinary
  sourceGlobals := right.sourceGlobals.trans left.sourceGlobals
  wasmGlobals := right.wasmGlobals.trans left.wasmGlobals
  hostStaticLayout := right.hostStaticLayout.trans left.hostStaticLayout }

/-- Imported-operation evidence already proves the reusable transport package. -/
theorem ConcreteExternalCallEvidence.transports
    {operation : ExternalOperation} {kind : AbiKind}
    {store nextStore : Wasm.Store Host} {args : List Wasm.Value}
    {runtime nextRuntime : RuntimeState} {value : Value}
    {witness nextWitness : RefinementWitness} {physical : Wasm.Value}
    (evidence : ConcreteExternalCallEvidence operation kind store args runtime
      nextRuntime value witness nextStore nextWitness physical) :
    RuntimeStepTransports runtime nextRuntime store nextStore witness nextWitness := {
  toClosureTablesTransport := evidence.closureTables
  witnessTransport := evidence.witnessTransport
  closureAllocationsPersistent := evidence.closureAllocationsPersistent
  capacity := evidence.capacityTransport
  ordinary := evidence.ordinaryTransport
  sourceGlobals := evidence.runtimeGlobals
  wasmGlobals := evidence.storeGlobals
  hostStaticLayout := evidence.hostStaticLayout }

/-- Recover a complete resource scope after a body region with no retained
reuse facts. Local values/alignment and budget come from its execution proof;
the transport package preserves caches, closures and arbitrary older callers.
No post-state resource invariant is assumed. -/
theorem ConcreteStructuredResourceScope.afterBody_withoutReuseFacts
    {context : Context} {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl} {entryRuntime runtime nextRuntime : RuntimeState}
    {entryStore store nextStore : Wasm.Store Host}
    {entryWitness witness nextWitness : RefinementWitness}
    {bytes nextBytes : Nat} {env nextEnv : Env} {locals nextLocals : Wasm.Locals}
    (scope : ConcreteStructuredResourceScope context sourceModule sourceFunction externals
      entryRuntime entryStore entryWitness [] bytes runtime env store locals witness)
    (transports : RuntimeStepTransports runtime nextRuntime store nextStore witness nextWitness)
    (externalsEq : nextStore.host.externals = store.host.externals)
    (related : StateRelated sourceFunction nextRuntime nextEnv nextStore nextLocals nextWitness)
    (aligned : ConcreteLocalFrameAligned sourceFunction nextRuntime nextEnv
      nextStore nextLocals nextWitness)
    (budget : nextStore.host.runtime.heap.AddressSpaceBudget nextBytes) :
    ConcreteStructuredResourceScope context sourceModule sourceFunction externals
      entryRuntime entryStore entryWitness [] nextBytes nextRuntime nextEnv nextStore
      nextLocals nextWitness := by
  rcases scope with ⟨⟨⟨⟨⟨⟨_reuse, _ordinary, _aligned, _budget⟩,
    integer, natural, scalar⟩, _descriptors⟩, cache, tables⟩, history⟩, abi⟩
  have nextTables := transports.toClosureTablesTransport.agree tables
  have nextReuse : ReuseCapacityStateRelated [] sourceFunction nextRuntime nextEnv
      nextStore nextLocals nextWitness := by
    refine ⟨related, ?_⟩
    intro id evidence found
    simp [findReuseCapacityEvidence?] at found
  have nextOrdinary : ReuseTokenOrdinaryRel [] nextRuntime nextEnv := by
    intro id available location cell found
    simp [findReuseCapacityEvidence?] at found
  have nextInteger : nextStore.host.externals.IntegerResultRefines externals := by
    rw [externalsEq]; exact integer
  have nextNatural : ConcreteExternalImpl.NaturalResultRefines nextStore.host.externals externals := by
    rw [externalsEq]; exact natural
  have nextScalar : ConcreteExternalImpl.ScalarResultRefines nextStore.host.externals externals := by
    rw [externalsEq]; exact scalar
  exact ⟨⟨⟨⟨⟨⟨nextReuse, nextOrdinary, aligned, budget⟩,
      nextInteger, nextNatural, nextScalar⟩, nextTables.descriptors⟩,
      cache.transport transports.witnessTransport transports.sourceGlobals
        transports.wasmGlobals transports.hostStaticLayout, nextTables⟩,
    history.step transports.witnessTransport transports.closureAllocationsPersistent
      transports.capacity transports.ordinary externalsEq transports.toClosureTablesTransport⟩,
    abi.ofPersistent transports.closureAllocationsPersistent⟩

end FirTalos.Concrete
