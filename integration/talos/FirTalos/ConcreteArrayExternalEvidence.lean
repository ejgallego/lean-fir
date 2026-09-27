import FirTalos.ConcreteArrayExternal
import FirTalos.ConcreteStructuredSimulation

/-! Empty-Array allocation at the existing external-call evidence boundary.
The installed handler equation remains explicit: these are concrete host
refinement results, not execution theorems for the emitted resident helper. -/

namespace FirTalos.Concrete

open Lean Fir.LeanIR.Impure Fir.Wasm Fir.Wasm.Concrete

/-- The exact address-space budget both bounds the capacity field and makes
empty Array allocation constructive. No successful-allocation premise remains. -/
theorem emptyArrayAllocation_of_budget
    {state : MemoryState} (valid : state.FrontierInvariant)
    (capacity remainingBytes : Nat)
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : residentArrayAllocationBytes capacity ≤ remainingBytes) :
    capacity < UInt32.size ∧ ∃ result address,
      allocateResidentArray state #[] capacity = .ok (result, address) ∧
      result.AddressSpaceBudget
        (remainingBytes - residentArrayAllocationBytes capacity) := by
  have allocationFits :
      align8 (headerBytes + target.semanticSlotBytes * capacity) ≤ remainingBytes := fits
  have capacityFits : capacity < UInt32.size := by
    have endWithin := (budget.allocationCapacity (by
      simpa only [align8_align8] using allocationFits)).endWithinAddressSpace
    have extent := align8_ge (headerBytes + target.semanticSlotBytes * capacity)
    have positive := budget.cursorPositive
    simp [target, wordModulus] at endWithin extent
    change capacity < 4294967296
    omega
  obtain ⟨result, address, allocated⟩ :=
    state.allocateObject_eq_ok_of_capacity .opaque
      (target.semanticSlotBytes * capacity) false residentArrayMarker 0
      (UInt32.ofNat capacity) 0 valid.cursorAligned
      (budget.allocationCapacity (by
        simpa only [align8_align8] using allocationFits))
  refine ⟨capacityFits, result, address, ?_,
    budget.allocateObject valid.cursorAligned allocationFits allocated⟩
  simp [allocateResidentArray, uint32Field, capacityFits, allocated,
    liftMemory, writeObjectFields, Bind.bind, Except.bind, Pure.pure, Except.pure]

def concreteEmptyArrayResponse (before : ConcreteRuntimeState)
    (result : MemoryState) (address : Word32) : ConcreteExternalResponse :=
  { value := .word32 address, heap := result, world := before.world }

def semanticEmptyArrayResponse (before : RuntimeState)
    (capacity : Nat) : ExternalResponse :=
  arrayExternalResponse (semanticArrayResult before #[] capacity)
    (.object (.heap before.nextLocation))

/-- Empty allocation supplies the response relation, including fresh witness
extension and all pre-existing live objects. World and trace updates are left
to the common external invocation theorem. -/
theorem ConcreteRuntimeRel.emptyArrayExternalResponse
    {before : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState}
    (related : ConcreteRuntimeRel before witness runtime)
    (request : ExternalRequest) (result : MemoryState) (address : Word32)
    (capacity : Nat) (capacityFits : capacity < UInt32.size)
    (allocated : allocateResidentArray before.heap #[] capacity = .ok (result, address)) :
    ConcreteExternalResponseRel witness
        (witness.bindArray runtime.nextLocation address capacity)
        request runtime .object
        (concreteEmptyArrayResponse before result address)
        (semanticEmptyArrayResponse runtime capacity) ∧
      ClosureAllocationsPersistent witness
        (witness.bindArray runtime.nextLocation address capacity) := by
  obtain ⟨extension, persistent, heap, value, _⟩ :=
    allocateResidentArray_liveHeapRel before.heap result witness runtime #[] #[]
      capacity address related.heap rfl (by simp) (by decide) capacityFits
      (by simp) allocated
  refine ⟨⟨extension, ?_, value, related.world⟩, persistent⟩
  apply heap.auxiliary <;>
    simp [semanticEmptyArrayResponse, arrayExternalResponse,
      semanticExternalRuntimeAfter]

/-- The deployment law for this one request. It fixes the handler's actual
computation, not merely its return representation. Request decoding and source
call semantics are independent premises at the generic external boundary. -/
def EmptyArrayHandlerAt (implementation : ConcreteExternalImpl)
    (request : ConcreteExternalRequest) (before : ConcreteRuntimeState)
    (capacity : Nat) : Prop :=
  implementation.call request before = do
    let (result, address) ← allocateResidentArray before.heap #[] capacity
    return concreteEmptyArrayResponse before result address

/-- Construct the existing external-call evidence from allocation headroom and
the installed handler equation. In particular, clients supply no successful
allocation, post-heap relation, post-witness, or target path. The interpreter and
host append the same single event, preserving the world exactly. -/
theorem emptyArrayExternalCallEvidence_of_budget
    (operation : ExternalOperation) (initial : Wasm.Store Host)
    (physicalArgs : List Wasm.Value) (concreteArgs : List LaneValue)
    (semanticArgs : Array Value) (witness : RefinementWitness)
    (runtime : RuntimeState) (externals : ExternalImpl)
    (capacity remainingBytes : Nat)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (related : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (requestRelated : ConcreteExternalRequestRel witness
      (concreteExternalRequest operation .object concreteArgs.toArray)
      (operation.request semanticArgs))
    (handler : EmptyArrayHandlerAt initial.host.externals
      (concreteExternalRequest operation .object concreteArgs.toArray)
      initial.host.runtime capacity)
    (semanticCalled : externals.call (operation.request semanticArgs) runtime =
      .ok (semanticEmptyArrayResponse runtime capacity))
    (budget : initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits : residentArrayAllocationBytes capacity ≤ remainingBytes) :
    ∃ nextStore nextWitness physicalResult,
      ConcreteExternalCallEvidence operation .object initial physicalArgs
        runtime (semanticExternalRuntimeAfter (operation.request semanticArgs)
          runtime (semanticEmptyArrayResponse runtime capacity))
        (.object (.heap runtime.nextLocation)) witness
        nextStore nextWitness physicalResult ∧
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - residentArrayAllocationBytes capacity) := by
  obtain ⟨capacityFits, result, address, allocated, residualBudget⟩ :=
    emptyArrayAllocation_of_budget related.heap.frontier capacity remainingBytes budget fits
  have called : initial.host.externals.call
      (concreteExternalRequest operation .object concreteArgs.toArray)
      initial.host.runtime =
        .ok (concreteEmptyArrayResponse initial.host.runtime result address) := by
    rw [handler]
    simp [allocated, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨responseRelated, persistent⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.emptyArrayExternalResponse related
      (operation.request semanticArgs)
      result address capacity capacityFits allocated
  obtain ⟨operationStep, _, runtimeRelated, valueRelated⟩ :=
    externalStep_of_refines operation .object initial physicalArgs concreteArgs
      semanticArgs witness runtime externals
      (witness.bindArray runtime.nextLocation address capacity)
      (concreteEmptyArrayResponse initial.host.runtime result address)
      (semanticEmptyArrayResponse runtime capacity)
      decoded related requestRelated called semanticCalled responseRelated
  let nextStore := replaceRuntime initial
    (initial.host.runtime.applyExternalResponse
      (concreteExternalRequest operation .object concreteArgs.toArray)
      (concreteEmptyArrayResponse initial.host.runtime result address))
  have extension := responseRelated.witnessExtension
  refine ⟨nextStore, witness.bindArray runtime.nextLocation address capacity,
    physicalOfLane (.word32 address), ?_, residualBudget⟩
  refine {
    operationStep
    witnessExtension := extension
    runtimeRelated
    failureClear := by simp [nextStore, replaceRuntime, clearFailure]
    valueRelated
    externalsPreserved := by simp [nextStore, replaceRuntime, clearFailure]
    closureTables := {
      hostDispatchPreserved := by simp [nextStore, replaceRuntime, clearFailure]
      witnessDispatchPreserved := extension.closureDispatch
      hostDescriptorsPreserved := by simp [nextStore, replaceRuntime, clearFailure]
      witnessDescriptorsPreserved := extension.closureDescriptors }
    witnessTransport := WitnessTransport.ofExtension extension
    closureAllocationsPersistent := persistent
    capacityTransport := ?_
    ordinaryTransport := ?_
    runtimeGlobals := rfl
    storeGlobals := rfl
    hostStaticLayout := rfl }
  · exact HeaderCapacityTransport.ofPrefixExtension witness
      (allocateResidentArray_prefixExtension _ _ #[] capacity address
        related.heap.frontier (by simp) (by decide) capacityFits allocated)
  · exact (alloc_ordinaryPersistenceTransport
      (alloc_array_eq runtime #[] capacity)).congrAfter rfl

/-- Specialization to the existing source primitive contract. Both sides
return a fresh empty Array with the requested capacity; the only new trace
entry is the actual `Array.mkEmpty` call. Capacity is arbitrary, not the
constant appearing in the retained initializer. -/
theorem mkEmptyExternalCallEvidence_of_budget
    (operation : ExternalOperation) (named : operation.name = `Array.mkEmpty)
    (initial : Wasm.Store Host) (physicalArgs : List Wasm.Value)
    (concreteArgs : List LaneValue) (witness : RefinementWitness)
    (runtime : RuntimeState) (externals : ExternalImpl)
    (contract : FreshArrayExternalContract externals)
    (capacity : UInt64) (remainingBytes : Nat)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (related : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (requestRelated : ConcreteExternalRequestRel witness
      (concreteExternalRequest operation .object concreteArgs.toArray)
      (operation.request #[.erased, .object (.tagged capacity)]))
    (handler : EmptyArrayHandlerAt initial.host.externals
      (concreteExternalRequest operation .object concreteArgs.toArray)
      initial.host.runtime capacity.toNat)
    (budget : initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits : residentArrayAllocationBytes capacity.toNat ≤ remainingBytes) :
    ∃ nextStore nextWitness physicalResult,
      ConcreteExternalCallEvidence operation .object initial physicalArgs runtime
        (semanticArrayResult { runtime with trace := runtime.trace.push {
          name := `Array.mkEmpty, args := #[.erased, .object (.tagged capacity)],
          result := .object (.heap runtime.nextLocation) } } #[] capacity.toNat)
        (.object (.heap runtime.nextLocation)) witness
        nextStore nextWitness physicalResult ∧
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - residentArrayAllocationBytes capacity.toNat) := by
  have semanticCalled : externals.call
      (operation.request #[.erased, .object (.tagged capacity)]) runtime =
      .ok (semanticEmptyArrayResponse runtime capacity.toNat) := by
    simpa [ExternalOperation.request, named, semanticEmptyArrayResponse] using
      contract.mkEmpty runtime operation.paramTypes operation.resultType capacity
  simpa [semanticExternalRuntimeAfter, semanticEmptyArrayResponse,
    arrayExternalResponse, semanticArrayResult, semanticExternalEvent,
    ExternalOperation.request, named] using
    emptyArrayExternalCallEvidence_of_budget operation initial physicalArgs concreteArgs
      #[.erased, .object (.tagged capacity)] witness runtime externals
      capacity.toNat remainingBytes decoded related requestRelated handler
      semanticCalled budget fits

end FirTalos.Concrete
