import FirTalos.ConcreteArrayExternalEvidence

/-! Fresh, non-full tagged Array push at the common external-call boundary.
No copy/grow branch or emitted resident-helper execution is claimed. -/

namespace FirTalos.Concrete

open Lean Fir.LeanIR.Impure Fir.Wasm Fir.Wasm.Concrete

/-- Source Array shape and the live-heap relation determine the descriptor;
clients need not separately certify it for an already represented Array. -/
theorem arrayDescriptor_of_mapped
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {elements : Array Value} {capacity : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (shape : cell.object = .array elements capacity) :
    witness.descriptors.lookup? address = some (.array capacity) := by
  obtain ⟨actual, actualFound, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at actualFound
  cases Option.some.inj actualFound
  cases cellRelated.live_of_eq_true live with
  | array descriptor objectEq =>
      rw [shape] at objectEq
      rw [(HeapObject.array.inj objectEq).2]
      exact descriptor
  | closure closureRelated =>
      obtain ⟨_, _, _, objectEq⟩ := closureRelated.objectEq
      rw [shape] at objectEq
      contradiction
  | constructor _ objectEq | boxed _ objectEq | natural _ objectEq
  | integer _ objectEq | string _ objectEq =>
      rw [shape] at objectEq
      contradiction

def concreteArrayPushResponse (before : ConcreteRuntimeState)
    (result : MemoryState) (address : Word32) : ConcreteExternalResponse :=
  { value := .word32 address, heap := result, world := before.world }

/-- Deployment equation for the selected unique/non-full branch. It specifies
actual handler computation, not a caller-provided response refinement. -/
def ArrayPushInPlaceHandlerAt (implementation : ConcreteExternalImpl)
    (request : ConcreteExternalRequest) (before : ConcreteRuntimeState)
    (address word : Word32) : Prop :=
  implementation.call request before = do
    let result ← pushResidentArrayElementInPlaceRaw before.heap address word
    return concreteArrayPushResponse before result address

/-- A fresh empty Array with spare capacity accepts an already represented tagged value
in place. The witness and allocation budget are unchanged, the exact source
event is appended, and all common external-call frame obligations are derived.
The source primitive contract and installed handler equation remain explicit. -/
theorem pushFreshTaggedExternalCallEvidence
    (operation : ExternalOperation) (named : operation.name = `Array.push)
    (initial : Wasm.Store Host) (physicalArgs : List Wasm.Value)
    (concreteArgs : List LaneValue) (witness : RefinementWitness)
    (entry : RuntimeState) (externals : ExternalImpl)
    (contract : FreshArrayExternalContract externals)
    (capacity : Nat) (spare : 0 < capacity)
    (payload : UInt64) (word : Word32)
    (tagged : ValueRel witness .tobject (.word32 word) (.object (.tagged payload)))
    (address : Word32) (remainingBytes : Nat)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (related : ConcreteRuntimeRel initial.host.runtime witness
      (semanticArrayResult entry #[] capacity))
    (mapped : witness.locations.lookup? entry.nextLocation = some address)
    (requestRelated : ConcreteExternalRequestRel witness
      (concreteExternalRequest operation .object concreteArgs.toArray)
      (operation.request #[.erased, .object (.heap entry.nextLocation),
        .object (.tagged payload)]))
    (handler : ArrayPushInPlaceHandlerAt initial.host.externals
      (concreteExternalRequest operation .object concreteArgs.toArray)
      initial.host.runtime address word)
    (budget : initial.host.runtime.heap.AddressSpaceBudget remainingBytes) :
    ∃ nextStore physicalResult,
      ConcreteExternalCallEvidence operation .object initial physicalArgs
        (semanticArrayResult entry #[] capacity)
        (semanticArrayResult { entry with trace := entry.trace.push {
          name := `Array.push,
          args := #[.erased, .object (.heap entry.nextLocation), .object (.tagged payload)],
          result := .object (.heap entry.nextLocation) } }
          #[.object (.tagged payload)] capacity)
        (.object (.heap entry.nextLocation)) witness nextStore witness physicalResult ∧
      nextStore.host.runtime.heap.heapCursor = initial.host.runtime.heap.heapCursor ∧
      nextStore.host.runtime.heap.AddressSpaceBudget remainingBytes := by
  have found : findCell? (semanticArrayResult entry #[] capacity).heap
      entry.nextLocation = some (semanticArrayCell #[] capacity) := by
    simp [semanticArrayResult, findCell?]
  have descriptor := arrayDescriptor_of_mapped related.heap mapped found rfl rfl
  obtain ⟨result, after, pushed, mutation, heapRelated, capacityFrame, cursor⟩ :=
    related.heap.pushResidentArrayElementInPlaceRaw_refines mapped found rfl rfl
      descriptor (.object (.tagged payload)) word spare tagged
  have afterEq : after = semanticArrayResult entry #[.object (.tagged payload)] capacity := by
    simpa [Fir.LeanIR.Impure.setCell, semanticArrayResult, semanticArrayCell,
      replaceCell] using mutation.symm
  subst after
  let semanticArgs : Array Value :=
    #[.erased, .object (.heap entry.nextLocation), .object (.tagged payload)]
  let response := arrayExternalResponse
    (semanticArrayResult entry #[.object (.tagged payload)] capacity)
    (.object (.heap entry.nextLocation))
  have semanticCalled : externals.call (operation.request semanticArgs)
      (semanticArrayResult entry #[] capacity) = .ok response := by
    simpa [ExternalOperation.request, named, semanticArgs, response] using
      contract.pushFreshTagged entry operation.paramTypes operation.resultType
        capacity payload spare
  have called : initial.host.externals.call
      (concreteExternalRequest operation .object concreteArgs.toArray)
      initial.host.runtime = .ok (concreteArrayPushResponse initial.host.runtime result address) := by
    rw [handler]
    simp [pushed, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have responseRelated : ConcreteExternalResponseRel witness witness
      (operation.request semanticArgs) (semanticArrayResult entry #[] capacity) .object
      (concreteArrayPushResponse initial.host.runtime result address) response := by
    refine ⟨.refl witness, ?_, .object (.mapped mapped), related.world⟩
    apply heapRelated.auxiliary <;>
      simp [response, arrayExternalResponse, semanticExternalRuntimeAfter, semanticArrayResult]
  obtain ⟨operationStep, _, runtimeRelated, valueRelated⟩ :=
    externalStep_of_refines operation .object initial physicalArgs concreteArgs
      semanticArgs witness (semanticArrayResult entry #[] capacity) externals witness
      (concreteArrayPushResponse initial.host.runtime result address) response
      decoded related requestRelated called semanticCalled responseRelated
  let nextStore := replaceRuntime initial
    (initial.host.runtime.applyExternalResponse
      (concreteExternalRequest operation .object concreteArgs.toArray)
      (concreteArrayPushResponse initial.host.runtime result address))
  have nextRuntimeEq : semanticExternalRuntimeAfter (operation.request semanticArgs)
      (semanticArrayResult entry #[] capacity) response =
      semanticArrayResult { entry with trace := entry.trace.push {
        name := `Array.push, args := semanticArgs,
        result := .object (.heap entry.nextLocation) } }
        #[.object (.tagged payload)] capacity := by
    simp [semanticExternalRuntimeAfter, response, arrayExternalResponse,
      semanticArrayResult, semanticExternalEvent, ExternalOperation.request, named]
  refine ⟨nextStore, physicalOfLane (.word32 address), ?_, cursor, ?_⟩
  · refine {
      operationStep
      witnessExtension := .refl witness
      runtimeRelated := by
        simpa only [nextRuntimeEq, semanticArgs, nextStore, replaceRuntime, clearFailure]
          using runtimeRelated
      failureClear := by simp [nextStore, replaceRuntime, clearFailure]
      valueRelated
      externalsPreserved := by simp [nextStore, replaceRuntime, clearFailure]
      closureTables := ⟨rfl, rfl, rfl, rfl⟩
      witnessTransport := WitnessTransport.refl witness
      closureAllocationsPersistent := ClosureAllocationsPersistent.refl witness
      capacityTransport := capacityFrame
      ordinaryTransport := (setCell_ordinaryPersistenceTransport
        (replacement := semanticArrayCell #[.object (.tagged payload)] capacity)
        found rfl mutation).congrAfter rfl
      runtimeGlobals := rfl
      storeGlobals := rfl
      hostStaticLayout := rfl }
  · change result.AddressSpaceBudget remainingBytes
    exact {
      cursorPositive := by simpa only [cursor] using budget.cursorPositive
      endWithinAddressSpace := by simpa only [cursor] using budget.endWithinAddressSpace }

end FirTalos.Concrete
