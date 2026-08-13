import Fir.Wasm.Concrete.ArrayHeapCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

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

end Fir.Wasm.Concrete
