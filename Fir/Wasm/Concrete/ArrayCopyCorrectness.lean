import Fir.Wasm.Concrete.ArrayHeapCorrectness
import Fir.Wasm.Concrete.ArrayMutationCorrectness
import Fir.Wasm.Concrete.OwnershipFrameCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Retain every word in an Array's copied live prefix. This is the concrete
ownership step emitted before a non-exclusive copy publishes its fresh Array.
It intentionally reuses the closure-capture retain primitive because that
primitive is exactly the erased-or-object `tobject` retain boundary needed by
generic container elements. -/
def retainResidentArrayElements (state : MemoryState) (source : Word32)
    (header : Header) :
    Except ConcreteError MemoryState :=
  readOwnedReferences state source header >>= fun words =>
    words.foldlM (init := state) retainClosureCapture

/-- The proof-side shape of W7's shared `Array.push` slow path. The copied
prefix is retained before publication, the fresh Array is extended by the
transferred argument, and only then is one ownership reference to the old
shared Array consumed. -/
def pushResidentArrayElementCopied (state : MemoryState) (source : Word32)
    (sourceHeader : Header) (words : Array Word32) (newCapacity : Nat)
    (value : Word32) (descriptors : ClosureDescriptorTable) :
    Except ConcreteError (MemoryState × Word32) := do
  let retained ← retainResidentArrayElements state source sourceHeader
  let (allocated, fresh) ← allocateResidentArray retained words newCapacity
  let pushed ← pushResidentArrayElementInPlaceRaw allocated fresh value
  let final ← decrementReferenceOnce pushed source true descriptors
  return (final, fresh)

/-- A capacity frame proved for an extended allocation witness also frames
the allocations named by its prefix witness. -/
theorem MappedHeaderCapacityTransport.witnessRestriction
    {before after : MemoryState} {first second : RefinementWitness}
    (extension : first.Extends second)
    (transport : MappedHeaderCapacityTransport before after second) :
    MappedHeaderCapacityTransport before after first := by
  intro address location header mapped headerRead owned
  exact transport address location header
    (extension.locations location address mapped) headerRead owned

/-- Allocate a fresh resident Array from words read out of an existing Array's
live prefix. The premise deliberately identifies every copied word with its
source-memory read: spare capacity is neither read nor copied.

This is the allocation-and-copy frame shared by the non-exclusive push and
pop paths. Ownership retains and consumption of the source reference are
separate ordered steps; this theorem establishes that fresh allocation alone
extends the witness and heap relation, preserves the complete source Array,
and leaves every previously mapped allocation at the same physical extent. -/
theorem LiveHeapRel.allocateResidentArray_copyFrame
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (sourceAddress : Word32)
    (elements : Array Value) (sourceCapacity : Nat) (sourceHeader : Header)
    (words : Array Word32) (newCapacity : Nat) (address : Word32)
    (related : LiveHeapRel state witness runtime)
    (sourceRelated : ResidentArrayObjectRel state witness sourceAddress
      elements sourceCapacity sourceHeader)
    (count : words.size = elements.size)
    (sizeCapacity : elements.size ≤ newCapacity)
    (sizeFits : elements.size < UInt32.size)
    (capacityFits : newCapacity < UInt32.size)
    (copied : ∀ (index : Nat) (value : Value),
      elements[index]? = some value →
      ∃ word,
        words[index]? = some word ∧
        state.memory.readWord32
            (sourceAddress.value + headerBytes +
              target.semanticSlotBytes * index) = .ok word)
    (allocated :
      allocateResidentArray state words newCapacity = .ok (result, address)) :
    let nextWitness :=
      witness.bindArray runtime.nextLocation address newCapacity
    witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel result nextWitness
        (semanticArrayResult runtime elements newCapacity) ∧
      state.PrefixExtension result ∧
      MappedHeaderCapacityTransport state result witness ∧
      ResidentArrayObjectRel result nextWitness sourceAddress elements
        sourceCapacity sourceHeader ∧
      sourceAddress ≠ address ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      alloc runtime (.array elements newCapacity) =
        (semanticArrayResult runtime elements newCapacity,
          .heap runtime.nextLocation) := by
  dsimp only
  have each : ∀ (index : Nat) (value : Value),
      elements[index]? = some value →
      ∃ word, words[index]? = some word ∧
        ValueRel witness .tobject (.word32 word) value := by
    intro index value valueAt
    obtain ⟨word, wordAt, copiedRead⟩ := copied index value valueAt
    obtain ⟨sourceWord, sourceRead, valueRelated⟩ :=
      sourceRelated.liveElements index value valueAt
    rw [copiedRead] at sourceRead
    have sourceWordEq : sourceWord = word := (Except.ok.inj sourceRead).symm
    subst sourceWord
    exact ⟨word, wordAt, valueRelated⟩
  obtain ⟨witnessExtension, closurePersistent, heapRelated, valueRelated,
      semanticAllocation⟩ :=
    allocateResidentArray_liveHeapRel state result witness runtime words elements
      newCapacity address related count sizeCapacity sizeFits capacityFits each
        allocated
  have wordsCapacity : words.size ≤ newCapacity := by omega
  have wordsFits : words.size < UInt32.size := by omega
  have memoryExtension : state.PrefixExtension result :=
    allocateResidentArray_prefixExtension state result words newCapacity address
      related.frontier wordsCapacity wordsFits capacityFits allocated
  have sourceAfter : ResidentArrayObjectRel result
      (witness.bindArray runtime.nextLocation address newCapacity) sourceAddress
      elements sourceCapacity sourceHeader :=
    (sourceRelated.prefixExtension memoryExtension).witnessExtension
      witnessExtension
  have capacityTransport :
      MappedHeaderCapacityTransport state result witness :=
    MappedHeaderCapacityTransport.ofPrefixExtension witness memoryExtension
  obtain ⟨middle, objectAllocation, _, _⟩ :=
    allocateResidentArray_decompose state result words newCapacity address
      wordsCapacity wordsFits capacityFits allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have sourceFresh : sourceAddress ≠ address := by
    intro equal
    subst address
    have owned := sourceRelated.headerOwned
    rw [freshAddress] at owned
    simp [headerBytes] at owned
    omega
  exact ⟨witnessExtension, closurePersistent, heapRelated, memoryExtension,
    capacityTransport, sourceAfter, sourceFresh, valueRelated,
    semanticAllocation⟩

/-- The complete shared-copy prefix: read-related source words are retained in
order, and the resulting concrete/semantic heaps remain related. The exact
fresh allocation is deliberately the next theorem boundary so W7's emitted
order—retain, store, then consume the source reference—can be composed without
smuggling allocation effects into the retain fold. -/
theorem LiveHeapRel.retainResidentArrayElements_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime finalRuntime : RuntimeState}
    {sourceAddress : Word32} {elements : Array Value}
    {sourceCapacity : Nat} {sourceHeader : Header}
    (related : LiveHeapRel state witness runtime)
    (sourceRelated : ResidentArrayObjectRel state witness sourceAddress
      elements sourceCapacity sourceHeader)
    (capacity : ClosureRetainCapacity runtime elements.toList)
    (semanticOperation :
      elements.toList.foldlM (init := runtime) retainOwnedValue =
        .ok finalRuntime) :
    ∃ finalState,
      retainResidentArrayElements state sourceAddress sourceHeader =
        .ok finalState ∧
      LiveHeapRel finalState witness finalRuntime ∧
      MappedHeaderCapacityTransport state finalState witness ∧
      finalState.heapCursor = state.heapCursor := by
  obtain ⟨words, wordsRead, wordsRelated⟩ := sourceRelated.readOwnedReferences
  obtain ⟨finalState, concreteOperation, finalRelated, capacityTransport,
      cursor⟩ :=
    wordsRelated.foldlM_retainClosureCaptures_refines related capacity
      semanticOperation
  refine ⟨finalState, ?_, finalRelated, capacityTransport, cursor⟩
  unfold retainResidentArrayElements
  rw [wordsRead]
  exact concreteOperation

private theorem setCell_semanticArrayResult_fresh_push
    (runtime : RuntimeState) (elements : Array Value) (capacity : Nat)
    (value : Value) :
    setCell (semanticArrayResult runtime elements capacity)
        runtime.nextLocation
        { semanticArrayCell elements capacity with
          object := .array (elements.push value) capacity } =
      .ok (semanticArrayResult runtime (elements.push value) capacity) := by
  simp [setCell, semanticArrayResult, semanticArrayCell, replaceCell]

/-- End-to-end refinement of the non-exclusive resident `Array.push` copy
path. The theorem makes the ownership protocol explicit:

1. retain the old live prefix in semantic and concrete order;
2. allocate the copied prefix at fresh locations;
3. transfer the pushed argument into the fresh Array without retaining it;
4. consume one reference to the old shared Array.

The result relates the complete final heaps, exposes the exact fresh semantic
reference, and transports every pre-existing allocation extent across all
four steps. It therefore supplies the reusable proof contract for W7's
shared push lowering rather than merely validating its individual helpers. -/
theorem LiveHeapRel.pushResidentArrayElementCopied_refines
    {state retainedState allocatedState : MemoryState}
    {witness : RefinementWitness}
    {runtime retainedRuntime finalRuntime : RuntimeState}
    {sourceLocation : Location} {sourceAddress : Word32}
    {elements : Array Value} {sourceCapacity : Nat} {sourceHeader : Header}
    {words : Array Word32} {newCapacity : Nat} {address : Word32}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? sourceLocation = some sourceAddress)
    (sourceRelated : ResidentArrayObjectRel state witness sourceAddress
      elements sourceCapacity sourceHeader)
    (count : words.size = elements.size)
    (sizeCapacity : elements.size ≤ newCapacity)
    (spare : elements.size < newCapacity)
    (sizeFits : elements.size < UInt32.size)
    (capacityFits : newCapacity < UInt32.size)
    (copied : ∀ (index : Nat) (element : Value),
      elements[index]? = some element →
      ∃ word,
        words[index]? = some word ∧
        state.memory.readWord32
            (sourceAddress.value + headerBytes +
              target.semanticSlotBytes * index) = .ok word)
    (value : Value) (word : Word32)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (retainCapacity : ClosureRetainCapacity runtime elements.toList)
    (semanticRetain :
      elements.toList.foldlM (init := runtime) retainOwnedValue =
        .ok retainedRuntime)
    (concreteRetain :
      retainResidentArrayElements state sourceAddress sourceHeader =
        .ok retainedState)
    (allocated :
      allocateResidentArray retainedState words newCapacity =
        .ok (allocatedState, address))
    (semanticConsume :
      decValueOnce
          (semanticArrayResult retainedRuntime (elements.push value) newCapacity)
          (.object (.heap sourceLocation)) true = .ok finalRuntime) :
    let nextWitness :=
      witness.bindArray retainedRuntime.nextLocation address newCapacity
    ∃ finalState,
      pushResidentArrayElementCopied state sourceAddress sourceHeader words
        newCapacity word witness.closureDescriptors = .ok (finalState, address) ∧
      witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel finalState nextWitness finalRuntime ∧
      MappedHeaderCapacityTransport state finalState witness ∧
      sourceAddress ≠ address ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap retainedRuntime.nextLocation)) ∧
      finalState.heapCursor = allocatedState.heapCursor := by
  dsimp only
  have each : ∀ (index : Nat) (element : Value),
      elements[index]? = some element →
      ∃ copiedWord, words[index]? = some copiedWord ∧
        ValueRel witness .tobject (.word32 copiedWord) element := by
    intro index element elementAt
    obtain ⟨copiedWord, copiedAt, copiedRead⟩ := copied index element elementAt
    obtain ⟨sourceWord, sourceRead, elementRelated⟩ :=
      sourceRelated.liveElements index element elementAt
    rw [copiedRead] at sourceRead
    have sourceWordEq : sourceWord = copiedWord :=
      (Except.ok.inj sourceRead).symm
    subst sourceWord
    exact ⟨copiedWord, copiedAt, elementRelated⟩
  obtain ⟨actualRetainedState, actualConcreteRetain, retainedRelated,
      retainTransport, retainedCursor⟩ :=
    related.retainResidentArrayElements_refines sourceRelated retainCapacity
      semanticRetain
  rw [concreteRetain] at actualConcreteRetain
  have actualRetainedEq : actualRetainedState = retainedState :=
    (Except.ok.inj actualConcreteRetain).symm
  subst actualRetainedState
  obtain ⟨witnessExtension, closurePersistent, allocatedRelated, freshRelated,
      _⟩ :=
    allocateResidentArray_liveHeapRel retainedState allocatedState witness
      retainedRuntime words elements newCapacity address retainedRelated count
        sizeCapacity sizeFits capacityFits each allocated
  let nextWitness :=
    witness.bindArray retainedRuntime.nextLocation address newCapacity
  have wordsCapacity : words.size ≤ newCapacity := by omega
  have wordsFits : words.size < UInt32.size := by omega
  have allocationExtension : retainedState.PrefixExtension allocatedState :=
    allocateResidentArray_prefixExtension retainedState allocatedState words
      newCapacity address retainedRelated.frontier wordsCapacity wordsFits
        capacityFits allocated
  have allocationTransport :
      MappedHeaderCapacityTransport retainedState allocatedState witness :=
    MappedHeaderCapacityTransport.ofPrefixExtension witness allocationExtension
  obtain ⟨middle, objectAllocation, _, _⟩ :=
    allocateResidentArray_decompose retainedState allocatedState words
      newCapacity address wordsCapacity wordsFits capacityFits allocated
  have freshAddress :=
    retainedRelated.frontier.allocateObject_address objectAllocation
  have sourceFresh : sourceAddress ≠ address := by
    intro equal
    subst address
    have owned := sourceRelated.headerOwned
    rw [freshAddress, retainedCursor] at owned
    simp [headerBytes] at owned
    omega
  have freshFound :
      findCell?
          (semanticArrayResult retainedRuntime elements newCapacity).heap
          retainedRuntime.nextLocation =
        some (semanticArrayCell elements newCapacity) := by
    simp [semanticArrayResult, findCell?]
  have nextValueRelated :
      ValueRel nextWitness .tobject (.word32 word) value :=
    valueRelated.witnessExtension witnessExtension
  obtain ⟨pushedState, pushedRuntime, concretePush, semanticPush,
      pushedRelated, pushTransport, pushedCursor⟩ :=
    allocatedRelated.pushResidentArrayElementInPlaceRaw_refines
      (RefinementWitness.lookup_bindArray_location witness
        retainedRuntime.nextLocation address newCapacity)
      freshFound (by rfl) (by rfl)
      (RefinementWitness.lookup_bindArray_descriptor witness
        retainedRuntime.nextLocation address newCapacity)
      value word spare nextValueRelated
  have canonicalPush :=
    setCell_semanticArrayResult_fresh_push retainedRuntime elements newCapacity
      value
  rw [canonicalPush] at semanticPush
  have pushedRuntimeEq : pushedRuntime =
      semanticArrayResult retainedRuntime (elements.push value) newCapacity :=
    (Except.ok.inj semanticPush).symm
  subst pushedRuntime
  have sourceMapped :
      nextWitness.locations.lookup? sourceLocation = some sourceAddress :=
    witnessExtension.locations sourceLocation sourceAddress mapped
  have semanticDecrement :
      decLocation
          (semanticArrayResult retainedRuntime (elements.push value) newCapacity)
          sourceLocation = .ok finalRuntime := by
    simpa [decValueOnce] using semanticConsume
  obtain ⟨actualFinalState, concreteConsume, finalRelated,
      consumeTransport⟩ :=
    pushedRelated.decrementReferenceOnce_refines_with_capacity sourceMapped true
      semanticDecrement
  have concreteConsumeOldDescriptors :
      decrementReferenceOnce pushedState sourceAddress true
          witness.closureDescriptors = .ok actualFinalState := by
    simpa [witnessExtension.closureDescriptors] using concreteConsume
  have oldPushTransport :
      MappedHeaderCapacityTransport allocatedState pushedState witness :=
    pushTransport.witnessRestriction witnessExtension
  have oldConsumeTransport :
      MappedHeaderCapacityTransport pushedState actualFinalState witness :=
    consumeTransport.witnessRestriction witnessExtension
  have finalTransport :=
    retainTransport.trans <|
      allocationTransport.trans <|
        oldPushTransport.trans oldConsumeTransport
  have finalCursor : actualFinalState.heapCursor = allocatedState.heapCursor := by
    rw [decrementReferenceOnce_preserves_heapCursor concreteConsumeOldDescriptors]
    exact pushedCursor
  refine ⟨actualFinalState, ?_, witnessExtension, closurePersistent, finalRelated,
    finalTransport, sourceFresh, freshRelated, finalCursor⟩
  unfold pushResidentArrayElementCopied
  rw [concreteRetain]
  simp only [Bind.bind, Except.bind]
  rw [allocated]
  simp only [Bind.bind, Except.bind]
  rw [concretePush]
  simp only [Bind.bind, Except.bind]
  rw [concreteConsumeOldDescriptors]
  rfl

end Fir.Wasm.Concrete
