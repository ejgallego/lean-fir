import Fir.Wasm.Concrete.OwnershipFrameCorrectness
import Fir.Wasm.Concrete.ConstructorHeapCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Explicit transition relation for the unique reset-to-reuse protocol.
`LiveHeapRel` is required only before reset; the exact concrete and semantic
reset equations name the temporary states without claiming that cleared
heap-only slots satisfy the normal ABI-indexed value relation. A later reuse
must consume both states together and re-establish `LiveHeapRel`. -/
structure ResetReuseProtocolRel
    (before after : MemoryState) (witness : RefinementWitness)
    (runtime nextRuntime : RuntimeState) (location : Location)
    (address : Word32) (cell : HeapCell) (object : ConstructorObject)
    (count : Nat) : Prop where
  relatedBefore : LiveHeapRel before witness runtime
  mapped : witness.locations.lookup? location = some address
  found : findCell? runtime.heap location = some cell
  live : cell.live = true
  ordinary : cell.persistent = false
  unique : cell.rc = 1
  constructor : cell.object = .ctor object
  countFits : count ≤ object.objectFields.size
  concreteReset : resetObject before count address = .ok (after, address)
  semanticReset :
    Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
      .ok (nextRuntime, .reuseToken (some location))

/-- The protocol transition returns the same already-mapped location/address
pair in both reuse-token representations. -/
theorem ResetReuseProtocolRel.tokenRelated
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {object : ConstructorObject}
    {count : Nat}
    (protocol : ResetReuseProtocolRel before after witness runtime nextRuntime
      location address cell object count) :
    ValueRel witness .reuseToken (.word32 address)
      (.reuseToken (some location)) :=
  .reuseSome (.mapped protocol.mapped)

/-- Rebinding the active constructor descriptor after reuse does not change
the protocol token's semantic location identity. -/
theorem ResetReuseProtocolRel.tokenRelated_rebindConstructor
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {object : ConstructorObject}
    {count : Nat}
    (protocol : ResetReuseProtocolRel before after witness runtime nextRuntime
      location address cell object count)
    (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    ValueRel (witness.rebindConstructor address info fieldKinds) .reuseToken
      (.word32 address) (.reuseToken (some location)) :=
  protocol.tokenRelated.rebindConstructor address info fieldKinds

theorem ResetReuseProtocolRel.reboundWitnessWellFormed
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {object : ConstructorObject}
    {count : Nat}
    (protocol : ResetReuseProtocolRel before after witness runtime nextRuntime
      location address cell object count)
    (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    (witness.rebindConstructor address info fieldKinds).WellFormed :=
  protocol.relatedBefore.witnessWellFormed.rebindConstructor address info fieldKinds

/-- Both physical tagged encodings take reset's empty-token path without
changing concrete memory. -/
theorem LiveHeapRel.resetObject_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload) (count : Nat) :
    resetObject state count word = .ok (state, Word32.zero) := by
  cases tagged with
  | immediate actualPayload fits =>
      unfold resetObject
      rw [Word32.classify_encodeImmediate]
      rfl
  | promoted found =>
      have promoted := related.promoted payload word found
      obtain ⟨header, headerRead, headerKind, persistent, _, marker, _, _⟩ :=
        promoted.header
      have addressHeap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state word header
          headerRead).1
      have isPromoted : header.isPromotedTag = true := by
        unfold Header.isPromotedTag
        rw [headerKind, persistent, marker]
        decide
      have releaseNoop : decrementReferenceOnce state word true = .ok state := by
        simpa using related.decrementReferenceOnce_tagged
          (TaggedReferenceRel.promoted found) true
      unfold resetObject
      rw [addressHeap, headerRead]
      simp only [Bind.bind, Except.bind, liftMemory]
      rw [if_pos (by simp [isPromoted])]
      rw [releaseNoop]
      rfl

/-- The tagged reset equation agrees with FIR and returns the related empty
reuse token. -/
theorem LiveHeapRel.resetObject_refines_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload) (count : Nat) :
    resetObject state count word = .ok (state, Word32.zero) ∧
      Fir.LeanIR.Impure.reset runtime count (.object (.tagged payload)) =
        .ok (runtime, .reuseToken none) ∧
      ValueRel witness .reuseToken (.word32 Word32.zero) (.reuseToken none) := by
  exact ⟨related.resetObject_tagged tagged count, rfl, .reuseNone⟩

/-- A non-unique ordinary heap cell follows reset's fallback path: one public
decrement is performed and the empty reuse token is returned. -/
theorem LiveHeapRel.resetObject_refines_nonunique
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {count : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (notUnique : cell.rc ≠ 1)
    (semanticOperation :
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .ok (nextRuntime, .reuseToken none)) :
    ∃ result,
      resetObject state count address = .ok (result, Word32.zero) ∧
      LiveHeapRel result witness nextRuntime ∧
      ValueRel witness .reuseToken (.word32 Word32.zero) (.reuseToken none) := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, ordinary, refCount⟩ :=
    targetRelated.ordinaryHeader
  have headerCountNe : header.refCount ≠ 1 := by
    intro one
    rw [one] at refCount
    simp at refCount
    exact notUnique refCount.symm
  have fallback :
      (header.isPromotedTag || header.persistent || header.refCount != 1) = true := by
    simp [notPromoted, ordinary, headerCountNe]
  have semanticDec :
      Fir.LeanIR.Impure.decLocation runtime location = .ok nextRuntime := by
    unfold Fir.LeanIR.Impure.reset at semanticOperation
    simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
      at semanticOperation
    rw [if_pos (by simp [targetRelated.persistent_eq_false, notUnique])]
      at semanticOperation
    cases decEq : Fir.LeanIR.Impure.decLocation runtime location with
    | error fault =>
        rw [decEq] at semanticOperation
        contradiction
    | ok middleRuntime =>
        rw [decEq] at semanticOperation
        have pairEq := Except.ok.inj semanticOperation
        have runtimeEq : middleRuntime = nextRuntime :=
          congrArg Prod.fst pairEq
        subst middleRuntime
        rfl
  obtain ⟨result, concreteDec, finalRelated⟩ :=
    related.decrementReferenceOnce_refines mapped semanticDec
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  have concreteReset :
      resetObject state count address = .ok (result, Word32.zero) := by
    unfold resetObject
    rw [addressHeap, headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_pos fallback, concreteDec]
    rfl
  exact ⟨result, concreteReset, finalRelated, .reuseNone⟩

/-- Consuming an empty reuse token is exactly fresh constructor allocation.
For a nonempty layout, the existing allocation theorem supplies the extended
witness, complete heap relation, and returned heap reference. -/
theorem LiveHeapRel.reuseObject_none_refines_nonempty
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (fields : Array Word32)
    (semanticFields : Array Value) (address : Word32) (updateHeader : Bool)
    (related : LiveHeapRel state witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (reused : reuseObject state Word32.zero info updateHeader fields =
      .ok (result, address)) :
    let nextWitness :=
      witness.bindConstructor runtime.nextLocation address info fieldKinds
    LiveHeapRel result nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      Fir.LeanIR.Impure.reuse runtime (.reuseToken none) info updateHeader
        semanticFields =
          .ok (semanticConstructorResult runtime info semanticFields,
            .object (.heap runtime.nextLocation)) := by
  have allocated : allocateConstructor state info fields = .ok (result, address) := by
    unfold reuseObject at reused
    rw [if_pos (by decide)] at reused
    exact reused
  obtain ⟨heapRelated, valueRelated⟩ :=
    allocateConstructor_nonempty_liveHeapRel state result witness runtime info
      fieldKinds fields semanticFields address related arity semanticArity
      fieldKindsSize fieldKindsValid fieldRelated nonempty tagFits objectFieldsFit
      usizeFieldsFit scalarBytesFit allocated
  exact ⟨heapRelated, valueRelated, by
    simpa [Fir.LeanIR.Impure.reuse] using
      allocCtor_nonempty_eq runtime info semanticFields semanticArity nonempty⟩

end Fir.Wasm.Concrete
