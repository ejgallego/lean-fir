import FirTalos.ConcreteRetainedTransports
import FirTalos.ConcreteRegionTransport

/-! Publication at the original initializer entry, rather than at the current
witness that already represents the result. Region closure is a construction
fact to be derived by producers, not a new public compiler-client invariant.
The executable cache operation and physical transports come from the existing
concrete refinement. No target instruction path is assumed or proved here. -/

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Publishing a graph constructed above the entry frontier preserves every
represented historical caller. Unlike call composition, this does not reindex
the saved facts to the current witness, which may already include the result. -/
theorem RetainedCallerTransport.setGlobal_of_freshRegion
    {heap : MemoryState} {witness : RefinementWitness}
    {entry current : RuntimeState} {root : Location}
    (related : LiveHeapRel heap witness entry)
    (history : RetainedCallerTransport witness entry current)
    (closed : HeapRegionClosed entry.nextLocation current.heap)
    (rootBound : entry.nextLocation ≤ root) (name : Name) :
    RetainedCallerTransport witness entry
      (current.setGlobal name (.object (.heap root))) := by
  intro facts bindings env locals savedHeap savedWitness saved transported
  exact ReuseTokenOrdinaryTransport.freshRegion_setGlobal_of_witness
    saved transported related (history saved transported) closed rootBound name

/-- The actual concrete cache host call and its two generated global writes
preserve the cumulative entry transport for a freshly constructed heap result.
Publication/disjointness and physical capacity transports are derived, not
supplied. This leaves cache-slot/layout facts and producer graph closure explicit.
It is independent of the current non-heap-only lazy-miss admission policy. -/
theorem RetainedCodeEntryTransports.publishFreshCache
    {entry current : RuntimeState} {entryStore store : Wasm.Store Host}
    {entryWitness witness : RefinementWitness} {root : Location}
    {declaration : Name} {kind : AbiKind} {physical : Wasm.Value}
    {slot : ConcreteGlobalSlot}
    (history : RetainedCodeEntryTransports entry current entryStore store entryWitness witness)
    (entryRelated : LiveHeapRel entryStore.host.runtime.heap entryWitness entry)
    (currentRelated : ConcreteRuntimeRel store.host.runtime witness current)
    (valueRelated : PhysicalValueRel witness kind physical (.object (.heap root)))
    (found : store.host.runtime.globals.find? declaration = some slot)
    (kindEq : slot.kind = kind)
    (descriptorsEq : store.host.closureDescriptors = witness.closureDescriptors)
    (closed : HeapRegionClosed entry.nextLocation current.heap)
    (rootBound : entry.nextLocation ≤ root) (cacheIndex : Nat) :
    ∃ runtimeAfter,
      cacheSetStep declaration kind store [physical] =
        .Return [physical] (replaceRuntime store runtimeAfter) ∧
      let nextStore := writeWasmGlobal
        (writeWasmGlobal (replaceRuntime store runtimeAfter)
          (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1)
      ConcreteRuntimeRel nextStore.host.runtime witness
        (current.setGlobal declaration (.object (.heap root))) ∧
      RetainedCodeEntryTransports entry
        (current.setGlobal declaration (.object (.heap root)))
        entryStore nextStore entryWitness witness ∧
      HeapRegionClosed entry.nextLocation
        (current.setGlobal declaration (.object (.heap root))).heap := by
  obtain ⟨runtimeAfter, operation, runtimeRelated, _, capacity⟩ :=
    cacheSetStep_of_refines currentRelated valueRelated found kindEq descriptorsEq
  refine ⟨runtimeAfter, operation, ?_, ?_, closed.setGlobal declaration _⟩
  · simpa [writeWasmGlobal] using runtimeRelated
  · refine {
      witness := history.witness
      closureAllocationsPersistent := history.closureAllocationsPersistent
      capacity := history.capacity.transAcross history.witness capacity
      retained := RetainedCallerTransport.setGlobal_of_freshRegion entryRelated
        history.retained closed rootBound declaration
      externals := by
        simpa [writeWasmGlobal, replaceRuntime, clearFailure] using history.externals
      hostDispatchPreserved := by
        simpa [writeWasmGlobal, replaceRuntime, clearFailure] using history.hostDispatchPreserved
      witnessDispatchPreserved := history.witnessDispatchPreserved
      hostDescriptorsPreserved := by
        simpa [writeWasmGlobal, replaceRuntime, clearFailure] using history.hostDescriptorsPreserved
      witnessDescriptorsPreserved := history.witnessDescriptorsPreserved }

end FirTalos.Concrete
