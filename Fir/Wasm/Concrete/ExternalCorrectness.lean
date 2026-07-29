import Fir.Wasm.Concrete.GlobalCorrectness
import Fir.Wasm.Concrete.IntegerAllocationCorrectness
import Fir.LeanIR.Interpreter

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- The physical request presented to a generated external import. Source
types are retained exactly, while ABI kinds describe the concrete lanes. -/
structure ConcreteExternalRequest where
  name : Lean.Name
  paramTypes : Array Lean.Expr
  resultType : Lean.Expr
  paramKinds : Array AbiKind
  resultKind : AbiKind
  args : Array LaneValue

def ConcreteExternalRequest.event (request : ConcreteExternalRequest)
    (result : LaneValue) : ConcreteExternalEvent := {
  name := request.name
  paramKinds := request.paramKinds
  args := request.args
  resultKind := request.resultKind
  result }

def semanticExternalEvent (request : ExternalRequest)
    (result : Value) : ExternalEvent := {
  name := request.name
  args := request.args
  result }

/-- The concrete request has exactly the source declaration metadata and a
typed physical lane for every semantic argument. -/
structure ConcreteExternalRequestRel (witness : RefinementWitness)
    (concrete : ConcreteExternalRequest) (semantic : ExternalRequest) : Prop where
  name : concrete.name = semantic.name
  paramTypes : concrete.paramTypes = semantic.paramTypes
  resultType : concrete.resultType = semantic.resultType
  paramTypesSize : concrete.paramTypes.size = concrete.paramKinds.size
  paramKindsSize : concrete.paramKinds.size = semantic.args.size
  argsSize : concrete.args.size = semantic.args.size
  arguments : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue) (value : Value),
    concrete.paramKinds[index]? = some kind →
    concrete.args[index]? = some lane →
    semantic.args[index]? = some value →
    ValueRel witness kind lane value

theorem ConcreteExternalRequestRel.witnessExtension
    {before after : RefinementWitness}
    {concrete : ConcreteExternalRequest} {semantic : ExternalRequest}
    (extension : before.Extends after)
    (related : ConcreteExternalRequestRel before concrete semantic) :
    ConcreteExternalRequestRel after concrete semantic := {
  name := related.name
  paramTypes := related.paramTypes
  resultType := related.resultType
  paramTypesSize := related.paramTypesSize
  paramKindsSize := related.paramKindsSize
  argsSize := related.argsSize
  arguments := by
    intro index kind lane value kindFound laneFound valueFound
    exact (related.arguments index kind lane value kindFound laneFound valueFound).witnessExtension
      extension }

theorem ConcreteExternalRequestRel.event
    {before after : RefinementWitness}
    {concrete : ConcreteExternalRequest} {semantic : ExternalRequest}
    {concreteResult : LaneValue} {semanticResult : Value}
    (extension : before.Extends after)
    (requestRelated : ConcreteExternalRequestRel before concrete semantic)
    (resultRelated : ValueRel after concrete.resultKind concreteResult semanticResult) :
    ConcreteExternalEventRel after (concrete.event concreteResult)
      (semanticExternalEvent semantic semanticResult) := {
  name := requestRelated.name
  paramKindsSize := requestRelated.paramKindsSize
  argsSize := requestRelated.argsSize
  arguments := by
    intro index kind lane value kindFound laneFound valueFound
    exact (requestRelated.arguments index kind lane value
      kindFound laneFound valueFound).witnessExtension extension
  result := resultRelated }

/-- Successful physical response from a concrete external implementation.
The updated memory is returned explicitly because foreign primitives may
allocate, mutate, or release FIR objects. -/
structure ConcreteExternalResponse where
  value : LaneValue
  heap : MemoryState
  world : Nat

structure ConcreteExternalImpl where
  call : ConcreteExternalRequest → ConcreteRuntimeState →
    Except ConcreteError ConcreteExternalResponse

/-- Source runtime after a successful response, stated independently of the
interpreter control stack. This is definitionally the runtime component of
`resumeExternal`. -/
def semanticExternalRuntimeAfter (request : ExternalRequest)
    (before : RuntimeState) (response : ExternalResponse) : RuntimeState := {
  before with
  heap := response.heap
  nextLocation := response.nextLocation
  world := response.world
  trace := before.trace.push (semanticExternalEvent request response.value) }

theorem semanticExternalRuntimeAfter_eq_resumeExternal
    (request : ExternalRequest) (waiting : MachineState)
    (response : ExternalResponse) :
    (resumeExternal request waiting response).runtime =
      semanticExternalRuntimeAfter request waiting.runtime response := rfl

def ConcreteRuntimeState.applyExternalResponse
    (request : ConcreteExternalRequest) (before : ConcreteRuntimeState)
    (response : ConcreteExternalResponse) : ConcreteRuntimeState := {
  before with
  heap := response.heap
  world := response.world
  trace := before.trace.push (request.event response.value) }

def ConcreteExternalImpl.invoke (implementation : ConcreteExternalImpl)
    (request : ConcreteExternalRequest) (before : ConcreteRuntimeState) :
    Except ConcreteError (ConcreteRuntimeState × LaneValue) := do
  let response ← implementation.call request before
  return (before.applyExternalResponse request response, response.value)

/-- Contract required of one successful concrete foreign response. External
code may change the heap and extend its witness, but it must establish the
complete post-heap relation and return a lane related at the declared ABI. -/
structure ConcreteExternalResponseRel
    (beforeWitness afterWitness : RefinementWitness)
    (request : ExternalRequest) (before : RuntimeState)
    (resultKind : AbiKind)
    (concrete : ConcreteExternalResponse) (semantic : ExternalResponse) : Prop where
  witnessExtension : beforeWitness.Extends afterWitness
  heap : LiveHeapRel concrete.heap afterWitness
    (semanticExternalRuntimeAfter request before semantic)
  value : ValueRel afterWitness resultKind concrete.value semantic.value
  world : concrete.world = semantic.world

/-- Applying related successful responses preserves heap, generated globals,
world, trace, and the returned value simultaneously. -/
theorem ConcreteRuntimeRel.applyExternalResponse
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness afterWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {concreteResponse : ConcreteExternalResponse}
    {semanticResponse : ExternalResponse}
    (runtimeRelated : ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (requestRelated : ConcreteExternalRequestRel beforeWitness
      concreteRequest semanticRequest)
    (responseRelated : ConcreteExternalResponseRel beforeWitness afterWitness
      semanticRequest semanticBefore concreteRequest.resultKind
      concreteResponse semanticResponse) :
    ConcreteRuntimeRel
      (concreteBefore.applyExternalResponse concreteRequest concreteResponse)
      afterWitness
      (semanticExternalRuntimeAfter semanticRequest semanticBefore semanticResponse) ∧
    ValueRel afterWitness concreteRequest.resultKind concreteResponse.value
      semanticResponse.value := by
  constructor
  · exact {
      heap := responseRelated.heap
      globals := by
        simpa [ConcreteRuntimeState.applyExternalResponse,
          semanticExternalRuntimeAfter] using
          runtimeRelated.globals.witnessExtension responseRelated.witnessExtension
      world := by
        simpa [ConcreteRuntimeState.applyExternalResponse,
          semanticExternalRuntimeAfter] using responseRelated.world
      trace := by
        have traceRelated := runtimeRelated.trace.witnessExtension
          responseRelated.witnessExtension
        have eventRelated := requestRelated.event
          responseRelated.witnessExtension responseRelated.value
        simpa [ConcreteRuntimeState.applyExternalResponse,
          semanticExternalRuntimeAfter] using traceRelated.push eventRelated }
  · exact responseRelated.value

/-- One successful concrete/source call pair refines end to end. The theorem
keeps both call equations visible so later generated-host composition cannot
replace the foreign implementation with an unconstrained response. -/
theorem ConcreteExternalImpl.invoke_refines
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness afterWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {concreteResponse : ConcreteExternalResponse}
    {semanticResponse : ExternalResponse}
    (runtimeRelated : ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (requestRelated : ConcreteExternalRequestRel beforeWitness
      concreteRequest semanticRequest)
    (concreteCalled : concreteImplementation.call concreteRequest concreteBefore =
      .ok concreteResponse)
    (semanticCalled : semanticImplementation.call semanticRequest semanticBefore =
      .ok semanticResponse)
    (responseRelated : ConcreteExternalResponseRel beforeWitness afterWitness
      semanticRequest semanticBefore concreteRequest.resultKind
      concreteResponse semanticResponse) :
    concreteImplementation.invoke concreteRequest concreteBefore =
        .ok (concreteBefore.applyExternalResponse concreteRequest concreteResponse,
          concreteResponse.value) ∧
      semanticImplementation.call semanticRequest semanticBefore =
        .ok semanticResponse ∧
      ConcreteRuntimeRel
        (concreteBefore.applyExternalResponse concreteRequest concreteResponse)
        afterWitness
        (semanticExternalRuntimeAfter semanticRequest semanticBefore semanticResponse) ∧
      ValueRel afterWitness concreteRequest.resultKind concreteResponse.value
        semanticResponse.value := by
  refine ⟨?_, semanticCalled, ?_⟩
  · unfold ConcreteExternalImpl.invoke
    rw [concreteCalled]
    rfl
  · exact runtimeRelated.applyExternalResponse requestRelated responseRelated

/-- Postcondition for a pure external result whose representation may allocate.
The heap and witness may grow (as they do for heap-backed `Nat`, `Int`, and
`String` values), while the world is unchanged and each side records exactly
its own request/result event. The runtime relation additionally proves that
those two exact events are related under the extended witness.

This boundary is deliberately result-polymorphic: adding or changing a heap
layout only affects the proof of `ConcreteExternalResponseRel`, not external
call composition. -/
structure ConcretePureExternalPost
    (concreteBefore : ConcreteRuntimeState)
    (beforeWitness afterWitness : RefinementWitness)
    (semanticBefore : RuntimeState)
    (concreteRequest : ConcreteExternalRequest)
    (semanticRequest : ExternalRequest)
    (concreteResponse : ConcreteExternalResponse)
    (semanticResponse : ExternalResponse) : Prop where
  witnessExtension : beforeWitness.Extends afterWitness
  runtime : ConcreteRuntimeRel
    (concreteBefore.applyExternalResponse concreteRequest concreteResponse)
    afterWitness
    (semanticExternalRuntimeAfter semanticRequest semanticBefore semanticResponse)
  value : ValueRel afterWitness concreteRequest.resultKind concreteResponse.value
    semanticResponse.value
  concreteWorld :
    (concreteBefore.applyExternalResponse concreteRequest concreteResponse).world =
      concreteBefore.world
  semanticWorld :
    (semanticExternalRuntimeAfter semanticRequest semanticBefore semanticResponse).world =
      semanticBefore.world
  concreteTrace :
    (concreteBefore.applyExternalResponse concreteRequest concreteResponse).trace =
      concreteBefore.trace.push (concreteRequest.event concreteResponse.value)
  semanticTrace :
    (semanticExternalRuntimeAfter semanticRequest semanticBefore semanticResponse).trace =
      semanticBefore.trace.push
        (semanticExternalEvent semanticRequest semanticResponse.value)

/-- The generic concrete external theorem specialized only by purity of the
source world. In particular, witness-extending `Nat`, `Int`, and `String`
result allocations require no result-specific composition theorem. -/
theorem ConcreteExternalImpl.invoke_pure_result_refines
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness afterWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {concreteResponse : ConcreteExternalResponse}
    {semanticResponse : ExternalResponse}
    (runtimeRelated : ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (requestRelated : ConcreteExternalRequestRel beforeWitness
      concreteRequest semanticRequest)
    (concreteCalled : concreteImplementation.call concreteRequest concreteBefore =
      .ok concreteResponse)
    (semanticCalled : semanticImplementation.call semanticRequest semanticBefore =
      .ok semanticResponse)
    (responseRelated : ConcreteExternalResponseRel beforeWitness afterWitness
      semanticRequest semanticBefore concreteRequest.resultKind
      concreteResponse semanticResponse)
    (worldUnchanged : semanticResponse.world = semanticBefore.world) :
    concreteImplementation.invoke concreteRequest concreteBefore =
        .ok (concreteBefore.applyExternalResponse concreteRequest concreteResponse,
          concreteResponse.value) ∧
      semanticImplementation.call semanticRequest semanticBefore =
        .ok semanticResponse ∧
      ConcretePureExternalPost concreteBefore beforeWitness afterWitness
        semanticBefore concreteRequest semanticRequest concreteResponse
        semanticResponse := by
  obtain ⟨concreteInvoke, semanticInvoke, runtimeAfter, valueAfter⟩ :=
    concreteImplementation.invoke_refines runtimeRelated requestRelated
      concreteCalled semanticCalled responseRelated
  refine ⟨concreteInvoke, semanticInvoke, {
    witnessExtension := responseRelated.witnessExtension
    runtime := runtimeAfter
    value := valueAfter
    concreteWorld := ?_
    semanticWorld := ?_
    concreteTrace := rfl
    semanticTrace := rfl }⟩
  · simp only [ConcreteRuntimeState.applyExternalResponse]
    calc
      concreteResponse.world = semanticResponse.world := responseRelated.world
      _ = semanticBefore.world := worldUnchanged
      _ = concreteBefore.world := runtimeRelated.world.symm
  · simpa [semanticExternalRuntimeAfter] using worldUnchanged

/-- Canonical concrete response for a pure external that materializes one
heap-backed arbitrary-precision integer. -/
def concreteIntegerExternalResponse
    (before : ConcreteRuntimeState) (result : MemoryState) (address : Word32) :
    ConcreteExternalResponse := {
  value := .word32 address
  heap := result
  world := before.world }

/-- Matching semantic response. Heap allocation advances the source location
cursor, while the world remains unchanged; event insertion is performed by
`semanticExternalRuntimeAfter`. -/
def semanticIntegerExternalResponse
    (before : RuntimeState) (value : Int) : ExternalResponse := {
  value := .object (.heap before.nextLocation)
  heap := (semanticIntegerResult before value).heap
  nextLocation := (semanticIntegerResult before value).nextLocation
  world := before.world }

/-- Integer allocation establishes the complete response contract expected by
the result-polymorphic external-call theorem: the witness grows, the heap and
result lane refine, and the pure world token is unchanged. -/
theorem ConcreteRuntimeRel.integerExternalResponse
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (semanticRequest : ExternalRequest)
    (result : MemoryState) (address : Word32) (value : Int)
    (allocated :
      allocateInteger concreteBefore.heap value = .ok (result, address)) :
    ConcreteExternalResponseRel beforeWitness
      (beforeWitness.bindInteger semanticBefore.nextLocation address value)
      semanticRequest semanticBefore .tobject
      (concreteIntegerExternalResponse concreteBefore result address)
      (semanticIntegerExternalResponse semanticBefore value) := by
  obtain ⟨extension, heapRelated, valueRelated⟩ :=
    allocateInteger_liveHeapRel concreteBefore.heap result beforeWitness
      semanticBefore value address runtimeRelated.heap allocated
  exact {
    witnessExtension := extension
    heap := heapRelated.auxiliary (by rfl) (by rfl)
    value := valueRelated
    world := runtimeRelated.world }

/-- End-to-end specialization of `invoke_pure_result_refines` for an
arbitrary-precision `Int` returned by a pure external. This is the executable
proof boundary used by generated handlers: they need only expose their call
equation and the successful `allocateInteger` equation. -/
theorem ConcreteExternalImpl.invoke_pure_integer_result_refines
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {result : MemoryState} {address : Word32} {value : Int}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (requestRelated : ConcreteExternalRequestRel beforeWitness
      concreteRequest semanticRequest)
    (resultKind : concreteRequest.resultKind = .tobject)
    (allocated :
      allocateInteger concreteBefore.heap value = .ok (result, address))
    (concreteCalled :
      concreteImplementation.call concreteRequest concreteBefore =
        .ok (concreteIntegerExternalResponse concreteBefore result address))
    (semanticCalled :
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticIntegerExternalResponse semanticBefore value)) :
    concreteImplementation.invoke concreteRequest concreteBefore =
        .ok (concreteBefore.applyExternalResponse concreteRequest
            (concreteIntegerExternalResponse concreteBefore result address),
          (concreteIntegerExternalResponse concreteBefore result address).value) ∧
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticIntegerExternalResponse semanticBefore value) ∧
      ConcretePureExternalPost concreteBefore beforeWitness
        (beforeWitness.bindInteger semanticBefore.nextLocation address value)
        semanticBefore concreteRequest semanticRequest
        (concreteIntegerExternalResponse concreteBefore result address)
        (semanticIntegerExternalResponse semanticBefore value) := by
  have responseRelated : ConcreteExternalResponseRel beforeWitness
      (beforeWitness.bindInteger semanticBefore.nextLocation address value)
      semanticRequest semanticBefore concreteRequest.resultKind
      (concreteIntegerExternalResponse concreteBefore result address)
      (semanticIntegerExternalResponse semanticBefore value) := by
    rw [resultKind]
    exact runtimeRelated.integerExternalResponse semanticRequest result address
      value allocated
  exact concreteImplementation.invoke_pure_result_refines runtimeRelated
    requestRelated concreteCalled semanticCalled
    responseRelated
    (by rfl)

/--
Operation-family correctness law for pure concrete handlers that materialize
an arbitrary-precision integer result.

This is a property of the two external implementations, not an execution
certificate for one compiled program. For every pair of related requests and
every successful source integer response, any successful invocation of the
canonical concrete allocator determines the handler's exact response.
-/
def ConcreteExternalImpl.IntegerResultRefines
    (concreteImplementation : ConcreteExternalImpl)
    (semanticImplementation : ExternalImpl) : Prop :=
  ∀ {concreteBefore : ConcreteRuntimeState}
      {beforeWitness : RefinementWitness}
      {semanticBefore : RuntimeState}
      {concreteRequest : ConcreteExternalRequest}
      {semanticRequest : ExternalRequest}
      {value : Int} {result : MemoryState} {address : Word32},
    ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore →
      ConcreteExternalRequestRel beforeWitness concreteRequest semanticRequest →
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticIntegerExternalResponse semanticBefore value) →
      allocateInteger concreteBefore.heap value = .ok (result, address) →
      concreteImplementation.call concreteRequest concreteBefore =
        .ok (concreteIntegerExternalResponse concreteBefore result address)

/--
One exact source-facing budget turns an integer-result implementation law into
the complete pure-external refinement postcondition.

Allocation success, the physical address, and the extended witness are all
constructed internally. The result includes the exact residual budget so a
structural compiler proof can continue with the remaining source path.
-/
theorem ConcreteRuntimeRel.invoke_pure_integer_result_refines_of_budget
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {value : Int} {remainingBytes : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (implementationRelated :
      concreteImplementation.IntegerResultRefines semanticImplementation)
    (requestRelated :
      ConcreteExternalRequestRel beforeWitness concreteRequest semanticRequest)
    (resultKind : concreteRequest.resultKind = .tobject)
    (semanticCalled :
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticIntegerExternalResponse semanticBefore value))
    (budget :
      concreteBefore.heap.AddressSpaceBudget remainingBytes)
    (fits : integerAllocationBytes value ≤ remainingBytes) :
    ∃ result address,
      allocateInteger concreteBefore.heap value = .ok (result, address) ∧
        concreteImplementation.invoke concreteRequest concreteBefore =
          .ok (concreteBefore.applyExternalResponse concreteRequest
              (concreteIntegerExternalResponse concreteBefore result address),
            (concreteIntegerExternalResponse concreteBefore result address).value) ∧
        semanticImplementation.call semanticRequest semanticBefore =
          .ok (semanticIntegerExternalResponse semanticBefore value) ∧
        ConcretePureExternalPost concreteBefore beforeWitness
          (beforeWitness.bindInteger semanticBefore.nextLocation address value)
          semanticBefore concreteRequest semanticRequest
          (concreteIntegerExternalResponse concreteBefore result address)
          (semanticIntegerExternalResponse semanticBefore value) ∧
        result.AddressSpaceBudget
          (remainingBytes - integerAllocationBytes value) := by
  obtain ⟨result, address, allocated, remainingBudget⟩ :=
    runtimeRelated.heap.frontier.allocateInteger_eq_ok_of_budget value budget fits
  have concreteCalled :=
    implementationRelated runtimeRelated requestRelated semanticCalled allocated
  obtain ⟨concreteInvoke, semanticInvoke, post⟩ :=
    concreteImplementation.invoke_pure_integer_result_refines runtimeRelated
      requestRelated resultKind allocated concreteCalled semanticCalled
  exact ⟨result, address, allocated, concreteInvoke, semanticInvoke, post,
    remainingBudget⟩

end Fir.Wasm.Concrete
