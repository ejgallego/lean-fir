import Fir.Wasm.Concrete.BoxingCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Every implemented live-cell case exposes the header facts used by
`isShared`, independently of the object's payload layout. -/
theorem LiveCellRel.sharingHeader
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) :
    ∃ header,
      state.readLiveHeader address = .ok header ∧
      header.refCount.toNat = cell.rc ∧
      header.persistent = cell.persistent := by
  cases related with
  | constructor _ _ _ headerRead _ refCount persistent _ =>
      exact ⟨_, headerRead, refCount, persistent⟩
  | boxed _ _ objectRelated refCount persistent _ =>
      exact ⟨_, objectRelated.headerRead, refCount, persistent⟩
  | natural _ _ headerRead _ _ _ _ _ refCount persistent _ =>
      exact ⟨_, headerRead, refCount, persistent⟩
  | string _ _ objectRelated refCount persistent _ =>
      exact ⟨_, objectRelated.headerRead, refCount, persistent⟩
  | closure closureRelated =>
      cases closureRelated with
      | closure _ _ headerRead _ _ _ _ refCount persistent _ =>
          exact ⟨_, headerRead, refCount, persistent⟩

/-- Concrete header sharing agrees exactly with the semantic cell's
persistent/refcount predicate. -/
theorem LiveCellRel.readIsShared_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) :
    readIsShared state address =
      .ok (if cell.persistent || cell.rc != 1 then 1 else 0) := by
  obtain ⟨header, headerRead, refCount, persistent⟩ := related.sharingHeader
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  unfold readIsShared
  rw [addressHeap]
  simp only
  rw [headerRead]
  simp only [Bind.bind, Except.bind, liftMemory]
  rw [persistent]
  by_cases rcOne : cell.rc = 1
  · have headerOne : header.refCount = 1 := by
      apply UInt32.toNat.inj
      simpa [rcOne] using refCount
    cases cell.persistent <;> simp [headerOne, rcOne] <;> rfl
  · have headerNotOne : header.refCount ≠ 1 := by
      intro headerOne
      apply rcOne
      have oneEq : (1 : Nat) = cell.rc := by
        simpa [headerOne] using refCount
      exact oneEq.symm
    cases cell.persistent <;> simp [headerNotOne, rcOne] <;> rfl

/-- A canonical released cell fails sharing observation through the exact
address-indexed source channel.  This is the concrete half of the stale
reference boundary: the retained freed header is still readable, but it is
never reinterpreted as a live object's sharing metadata. -/
theorem DeadCellRel.readIsShared_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) :
    readIsShared state address =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨header, headerRead, addressHeap, _, _, dead, _, _, _, _, _, _, _, _⟩ :=
    related.header
  have deadRead : state.readLiveHeader address = .error (.deadObject address) := by
    unfold MemoryState.readLiveHeader
    rw [addressHeap]
    simp only [headerRead, Bind.bind, Except.bind]
    rw [dead]
    rfl
  unfold readIsShared
  rw [addressHeap]
  simp only
  rw [deadRead]
  rfl

/-- Both direct immediates and persistent promoted representations are shared
without consulting semantic heap state. -/
theorem LiveHeapRel.readIsShared_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload) :
    readIsShared state word = .ok 1 := by
  cases tagged with
  | immediate actualPayload fits =>
      unfold readIsShared
      simp [Word32.classify_encodeImmediate]
      rfl
  | promoted found =>
      have promoted := related.promoted payload word found
      obtain ⟨header, headerRead, _, persistent, _, _, _, _⟩ := promoted.header
      have addressHeap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state word header
          headerRead).1
      unfold readIsShared
      rw [addressHeap]
      simp only
      rw [headerRead]
      simp only [Bind.bind, Except.bind, liftMemory]
      rw [persistent]
      rfl

/-- Complete `tobject -> UInt8` sharing refinement for a semantically valid
object. The success premise is essential because witness mappings persist for
released cells, whose stale references must report `deadObject`. The result is
a direct scalar lane, matching Lean 4.32's final impure ABI. -/
theorem LiveHeapRel.readIsShared_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {word : Word32} {value : Value}
    (related : LiveHeapRel state witness runtime)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (semanticSuccess : ∃ result,
      Fir.LeanIR.Impure.isShared runtime value = .ok result) :
    ∃ shared : UInt8,
      readIsShared state word = .ok shared ∧
      Fir.LeanIR.Impure.isShared runtime value = .ok (.scalar (.uint8 shared)) ∧
      ValueRel witness .uint8 (.word32 (Word32.ofUInt8 shared))
        (.scalar (.uint8 shared)) := by
  cases valueRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | tagged taggedRelated =>
          exact ⟨1, related.readIsShared_tagged taggedRelated, rfl, .uint8 rfl⟩
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              rename_i location
              obtain ⟨cell, found, cellRelation⟩ :=
                related.concreteToSemantic _ word mapped
              have live : cell.live = true := by
                obtain ⟨_, succeeded⟩ := semanticSuccess
                cases liveEq : cell.live with
                | false =>
                    simp [Fir.LeanIR.Impure.isShared, getLiveCell, found, liveEq,
                      Bind.bind, Except.bind] at succeeded
                | true => rfl
              have cellRelated := cellRelation.live_of_eq_true live
              let shared : UInt8 :=
                if cell.persistent || cell.rc != 1 then 1 else 0
              have concrete : readIsShared state word = .ok shared := by
                simpa [shared] using cellRelated.readIsShared_eq
              have semantic : Fir.LeanIR.Impure.isShared runtime
                  (.object (.heap location)) = .ok (.scalar (.uint8 shared)) := by
                unfold Fir.LeanIR.Impure.isShared
                simp [getLiveCell, found, live, shared]
                rfl
              exact ⟨shared, concrete, semantic, .uint8 rfl⟩

/-- A mapped stale heap word and its dead semantic location report the same
`deadObject` failure.  The concrete error retains the physical address; the
semantic error retains the represented location.  The witness mapping lets
the later fault layer relate those indices without weakening either side. -/
theorem LiveHeapRel.readIsShared_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    readIsShared state address =
        .error (.sourceAddress (.deadObject address)) ∧
      Fir.LeanIR.Impure.isShared runtime (.object (.heap location)) =
        .error (.deadObject location) := by
  cases mapped with
  | mapped mappedFound =>
      obtain ⟨mappedCell, semanticFound, cellRelation⟩ :=
        related.concreteToSemantic location address mappedFound
      rw [found] at semanticFound
      have cellEq := Option.some.inj semanticFound
      subst mappedCell
      constructor
      · cases cellRelation with
        | live liveRelated =>
            cases liveRelated with
            | constructor _ _ _ _ _ _ _ live => simp_all
            | boxed _ _ _ _ _ live => simp_all
            | natural _ _ _ _ _ _ _ _ _ _ live => simp_all
            | string _ _ _ _ _ live => simp_all
            | closure closureRelated =>
                cases closureRelated with
                | closure _ _ _ _ _ _ _ _ _ live => simp_all
        | dead _ _ _ deadRelated => exact deadRelated.readIsShared_eq
      · simp [Fir.LeanIR.Impure.isShared, getLiveCell, found, dead,
          Except.map]
        rfl

end Fir.Wasm.Concrete
