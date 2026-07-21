import Fir.Wasm.Concrete.GlobalCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- A live header already carrying the persistent bit is an exact no-op for
every concrete persistence fuel budget. -/
theorem markPersistentFuel_eq_of_persistent
    {state : MemoryState} {object : Word32} {header : Header}
    (headerRead : state.readLiveHeader object = .ok header)
    (persistent : header.persistent = true) (fuel : Nat)
    (descriptors : ClosureDescriptorTable := #[]) :
    markPersistentFuel fuel state object descriptors = .ok state := by
  obtain ⟨heap, _, _, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state object header headerRead
  cases fuel with
  | zero =>
      simp only [markPersistentFuel]
      rw [heap]
      simp only [headerRead, liftMemory, Bind.bind, Except.bind]
      rw [if_pos persistent]
      rfl
  | succ fuel =>
      simp only [markPersistentFuel]
      rw [heap]
      simp only [headerRead, liftMemory, Bind.bind, Except.bind]
      rw [if_pos persistent]
      rfl

/-- The public cursor-bounded persistence operation likewise leaves an
already-persistent allocation unchanged. -/
theorem markPersistent_eq_of_persistent
    {state : MemoryState} {object : Word32} {header : Header}
    (headerRead : state.readLiveHeader object = .ok header)
    (persistent : header.persistent = true)
    (descriptors : ClosureDescriptorTable := #[]) :
    markPersistent state object descriptors = .ok state := by
  exact markPersistentFuel_eq_of_persistent headerRead persistent _ descriptors

/-- Syntactic classification used by cache composition: only a semantic heap
reference requires the recursive persistence simulation. -/
def IsNonHeapReference : Value → Prop
  | .object (.heap _) => False
  | _ => True

/-- Every cache lane that does not denote a semantic heap location discharges
the persistence boundary constructively. Scalar and sentinel lanes bypass the
concrete operation; direct tags are immediate no-ops; promoted tags are
already persistent by their representation invariant. -/
theorem CachePersistenceRefines.of_nonHeapReference
    {concrete : MemoryState} {witness : RefinementWitness}
    {semantic : RuntimeState} {kind : AbiKind} {lane : LaneValue}
    {value : Value} {descriptors : ClosureDescriptorTable}
    (heapRelated : LiveHeapRel concrete witness semantic)
    (valueRelated : ValueRel witness kind lane value)
    (nonHeap : IsNonHeapReference value) :
    CachePersistenceRefines concrete witness semantic kind lane value descriptors := by
  cases valueRelated with
  | object related => contradiction
  | tagged related =>
      cases related with
      | immediate payload fits =>
          refine ⟨concrete, ?_, ?_⟩
          · simp [persistGlobalValue, markPersistent, markPersistentFuel,
              Word32.classify_encodeImmediate]
            rfl
          · simpa [RuntimeState.markPersistent] using heapRelated
      | promoted found =>
          obtain ⟨header, headerRead, _, persistent, _, _, _, _⟩ :=
            (heapRelated.promoted _ _ found).header
          refine ⟨concrete, ?_, ?_⟩
          · simp only [persistGlobalValue]
            exact markPersistent_eq_of_persistent headerRead persistent descriptors
          · simpa [RuntimeState.markPersistent] using heapRelated
  | tobject related =>
      cases related with
      | heap related => contradiction
      | tagged related =>
          cases related with
          | immediate payload fits =>
              refine ⟨concrete, ?_, ?_⟩
              · simp [persistGlobalValue, markPersistent, markPersistentFuel,
                  Word32.classify_encodeImmediate]
                rfl
              · simpa [RuntimeState.markPersistent] using heapRelated
          | promoted found =>
              obtain ⟨header, headerRead, _, persistent, _, _, _, _⟩ :=
                (heapRelated.promoted _ _ found).header
              refine ⟨concrete, ?_, ?_⟩
              · simp only [persistGlobalValue]
                exact markPersistent_eq_of_persistent headerRead persistent descriptors
              · simpa [RuntimeState.markPersistent] using heapRelated
  | erased =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | reuseNone =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | reuseSome related =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | uint8 encoded =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | uint16 encoded =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | uint32 encoded =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | uint64 =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | usize =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩

/-- Cache writes of non-heap values no longer require callers to manufacture
an explicit persistence witness. -/
theorem ConcreteRuntimeRel.writeGlobal_nonHeapReference
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {semantic : RuntimeState} {name : Lean.Name} {slot : ConcreteGlobalSlot}
    {kind : AbiKind} {lane : LaneValue} {value : Value}
    {descriptors : ClosureDescriptorTable}
    (related : ConcreteRuntimeRel concrete witness semantic)
    (found : concrete.globals.find? name = some slot)
    (kindEq : slot.kind = kind)
    (valueRelated : ValueRel witness kind lane value)
    (nonHeap : IsNonHeapReference value) :
    ∃ after,
      concrete.writeGlobal name kind lane descriptors = .ok after ∧
        ConcreteRuntimeRel after witness (semantic.setGlobal name value) := by
  exact related.writeGlobal found kindEq valueRelated
    (.of_nonHeapReference related.heap valueRelated nonHeap)

end Fir.Wasm.Concrete
