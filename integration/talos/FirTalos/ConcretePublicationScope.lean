import FirTalos.ConcreteStructuredSimulation
import FirTalos.ConcreteRetainedPublication

/-! Caller restoration after cache publication. The semantic publication law
is indexed by the initializer's original entry, not its result-containing
current witness. All remaining caller resources are reconstructed here. -/

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Reconstruct the suspended caller's full scope from cumulative publication
transport and the actual cache operation. This boundary works for both non-heap
and fresh heap results; it does not assume blanket ordinaryness preservation. -/
theorem ConcreteStructuredResourceScope.afterCachePublication
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {callerEntryRuntime activeEntryRuntime current : RuntimeState}
    {callerEntryStore activeEntryStore store : Wasm.Store Host}
    {callerEntryWitness activeEntryWitness witness : RefinementWitness}
    {callerFacts calleeFacts : ReuseCapacityFacts} {callerBytes remainingBytes : Nat}
    {callerEnv calleeEnv : Env} {callerLocals calleeLocals : Wasm.Locals}
    {declaration : Name} {kind : AbiKind} {physical : Wasm.Value}
    {sourceValue : Value} {cacheIndex : Nat} {runtimeAfter : ConcreteRuntimeState}
    (callerScope : ConcreteStructuredResourceScope callerContext sourceModule
      callerFunction externals callerEntryRuntime callerEntryStore callerEntryWitness
      callerFacts callerBytes activeEntryRuntime callerEnv activeEntryStore callerLocals
      activeEntryWitness)
    (currentScope : ConcreteStructuredResourceScope calleeContext sourceModule
      calleeFunction externals activeEntryRuntime activeEntryStore activeEntryWitness
      calleeFacts remainingBytes current calleeEnv store calleeLocals witness)
    (programEq : calleeContext.program = callerContext.program)
    (initializerFound : sourceModule.initializers[cacheIndex]? = some declaration)
    (signature : (sourceModule.callSignature? (.declaration declaration)).bind
      (·.results[0]?) = some kind)
    (valueRelated : PhysicalValueRel witness kind physical sourceValue)
    (operation : cacheSetStep declaration kind store [physical] =
      .Return [physical] (replaceRuntime store runtimeAfter))
    (runtimeRelated : ConcreteRuntimeRel runtimeAfter witness
      (current.setGlobal declaration sourceValue))
    (history : RetainedCodeEntryTransports activeEntryRuntime
      (current.setGlobal declaration sourceValue) activeEntryStore
      (writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
        (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1))
      activeEntryWitness witness) :
    ConcreteStructuredResourceScope callerContext sourceModule callerFunction externals
      callerEntryRuntime callerEntryStore callerEntryWitness callerFacts remainingBytes
      (current.setGlobal declaration sourceValue) callerEnv
      (writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
        (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1)) callerLocals witness := by
  let nextStore := writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
    (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1)
  have callerState := currentScope.transports.savedStateRelated
    callerScope.stateRelated currentScope.stateRelated
  have nextState : StateRelated callerFunction
      (current.setGlobal declaration sourceValue) callerEnv nextStore callerLocals witness := by
    refine ⟨?_, ?_, callerState.2.2⟩
    · simpa [nextStore, writeWasmGlobal, replaceRuntime, clearFailure] using runtimeRelated
    · simp [nextStore, writeWasmGlobal, replaceRuntime, clearFailure]
  have nextReuse := callerScope.1.1.1.1.1.1.transport nextState
    history.witness history.capacity
  have nextOrdinary := history.retained callerScope.1.1.stateRelated.2
    (WitnessTransport.refl activeEntryWitness) callerScope.1.1.1.1.1.2.1
  have nextAligned : ConcreteLocalFrameAligned callerFunction
      (current.setGlobal declaration sourceValue) callerEnv nextStore callerLocals witness := by
    simpa [ConcreteLocalFrameAligned] using callerScope.frameAligned
  have nextBudget : nextStore.host.runtime.heap.AddressSpaceBudget remainingBytes :=
    cachePublication_preserves_addressSpaceBudget operation rfl
      currentScope.1.1.1.1.1.2.2.2
  have nextInteger : nextStore.host.externals.IntegerResultRefines externals := by
    rw [history.externals]
    exact callerScope.1.1.1.1.2.1
  have nextNatural : ConcreteExternalImpl.NaturalResultRefines
      nextStore.host.externals externals := by
    rw [history.externals]
    exact callerScope.1.1.1.1.2.2.1
  have nextScalar : ConcreteExternalImpl.ScalarResultRefines
      nextStore.host.externals externals := by
    rw [history.externals]
    exact callerScope.1.1.1.1.2.2.2
  have nextDescriptors : nextStore.host.closureDescriptors = witness.closureDescriptors := by
    simpa [nextStore, writeWasmGlobal, replaceRuntime, clearFailure] using currentScope.1.1.1.2
  have nextCache : LazyCacheGlobalsRel witness sourceModule
      (current.setGlobal declaration sourceValue) nextStore :=
    (currentScope.1.1.2.1.afterCacheSet operation).publish
      initializerFound signature rfl valueRelated rfl
  have nextTables : ClosureTablesAgree nextStore witness := by
    exact ⟨currentScope.1.1.2.2.dispatch, currentScope.1.1.2.2.descriptors⟩
  refine ⟨⟨⟨⟨⟨⟨nextReuse, nextOrdinary, nextAligned, nextBudget⟩,
    nextInteger, nextNatural, nextScalar⟩, nextDescriptors⟩, nextCache, nextTables⟩,
    callerScope.transports.trans history⟩, ?_⟩
  rw [← programEq]
  exact currentScope.2

/-- Fresh graph construction discharges the publication transport needed by
caller restoration. Cache layout, external contracts, resource headroom and
closure ABI are recovered from the existing scopes rather than new premises. -/
theorem ConcreteStructuredResourceScope.publishFreshCache
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {callerEntryRuntime activeEntryRuntime current : RuntimeState}
    {callerEntryStore activeEntryStore store : Wasm.Store Host}
    {callerEntryWitness activeEntryWitness witness : RefinementWitness}
    {callerFacts calleeFacts : ReuseCapacityFacts} {callerBytes remainingBytes : Nat}
    {callerEnv calleeEnv : Env} {callerLocals calleeLocals : Wasm.Locals}
    {declaration : Name} {kind : AbiKind} {physical : Wasm.Value}
    {root : Location} {cacheIndex : Nat}
    (callerScope : ConcreteStructuredResourceScope callerContext sourceModule
      callerFunction externals callerEntryRuntime callerEntryStore callerEntryWitness
      callerFacts callerBytes activeEntryRuntime callerEnv activeEntryStore callerLocals
      activeEntryWitness)
    (currentScope : ConcreteStructuredResourceScope calleeContext sourceModule
      calleeFunction externals activeEntryRuntime activeEntryStore activeEntryWitness
      calleeFacts remainingBytes current calleeEnv store calleeLocals witness)
    (programEq : calleeContext.program = callerContext.program)
    (initializerFound : sourceModule.initializers[cacheIndex]? = some declaration)
    (signature : (sourceModule.callSignature? (.declaration declaration)).bind
      (·.results[0]?) = some kind)
    (valueRelated : PhysicalValueRel witness kind physical (.object (.heap root)))
    (closed : HeapRegionClosed activeEntryRuntime.nextLocation current.heap)
    (rootBound : activeEntryRuntime.nextLocation ≤ root) :
    ∃ runtimeAfter,
      cacheSetStep declaration kind store [physical] =
        .Return [physical] (replaceRuntime store runtimeAfter) ∧
      ConcreteStructuredResourceScope callerContext sourceModule callerFunction externals
        callerEntryRuntime callerEntryStore callerEntryWitness callerFacts remainingBytes
        (current.setGlobal declaration (.object (.heap root))) callerEnv
        (writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
          (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1)) callerLocals witness := by
  obtain ⟨slot, found, kindEq⟩ := currentScope.1.1.2.1.hostSlot initializerFound signature
  obtain ⟨runtimeAfter, operation, related, history⟩ :=
    currentScope.transports.publishFreshCache callerScope.stateRelated.1.heap
      currentScope.stateRelated.1 valueRelated found kindEq currentScope.1.1.1.2
      closed rootBound cacheIndex
  exact ⟨runtimeAfter, operation,
    callerScope.afterCachePublication currentScope programEq initializerFound signature
      valueRelated operation related history⟩

end FirTalos.Concrete
