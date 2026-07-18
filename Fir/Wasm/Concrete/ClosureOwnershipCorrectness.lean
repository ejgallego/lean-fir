import Fir.Wasm.Concrete.ClosureHeapCorrectness
import Fir.Wasm.Concrete.ReferenceCountCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Semantic closure captures visited by concrete ownership. Scalar captures
remain in `HeapObject.ownedValues`, but FIR's release fold treats them as
no-ops; this filter keeps precisely the representations for which the
concrete runtime reads an object word. -/
def closureOwnedValues : List AbiKind → List Value → List Value
  | kind :: kinds, value :: values =>
      if kind.isObjectField then
        value :: closureOwnedValues kinds values
      else
        closureOwnedValues kinds values
  | _, _ => []

/-- Every ABI relation accepted by the ownership filter has an `i32` word
and therefore induces the type-erased relation used by recursive release. -/
theorem ValueRel.ownershipOfObjectField
    {witness : RefinementWitness} {kind : AbiKind} {lane : LaneValue}
    {value : Value} (related : ValueRel witness kind lane value)
    (admissible : kind.isObjectField = true) :
    ∃ word, lane = .word32 word ∧ OwnershipValueRel witness word value := by
  cases related with
  | object reference =>
      exact ⟨_, rfl, .intro .object admissible (.object reference)⟩
  | tagged reference =>
      exact ⟨_, rfl, .intro .tagged admissible (.tagged reference)⟩
  | tobject reference =>
      exact ⟨_, rfl, .intro .tobject admissible (.tobject reference)⟩
  | erased =>
      exact ⟨_, rfl, .intro .erased admissible .erased⟩
  | reuseNone | reuseSome | uint8 | uint16 | uint32 | uint64 | usize =>
      simp [AbiKind.isObjectField] at admissible

/-- Pointwise typed capture reads determine the exact filtered word list
returned by the executable closure ownership decoder. -/
private theorem readClosureOwnedReferences_of_each
    (state : MemoryState) (witness : RefinementWitness) (address : Word32)
    (index : Nat) (kinds : List AbiKind) (values : List Value)
    (sizeEq : kinds.length = values.length)
    (each : ∀ offset kind value,
      kinds[offset]? = some kind →
      values[offset]? = some value →
      ∃ lane,
        state.memory.readClosureCapture
            (closureCaptureAddress address.value (index + offset)) kind = .ok lane ∧
          ValueRel witness kind lane value) :
    ∃ words,
      readClosureOwnedReferences state address index kinds = .ok words ∧
        OwnershipValuesRel witness words (closureOwnedValues kinds values) := by
  induction kinds generalizing index values with
  | nil =>
      cases values with
      | nil => exact ⟨[], rfl, .nil⟩
      | cons value values => simp at sizeEq
  | cons kind kinds ih =>
      cases values with
      | nil => simp at sizeEq
      | cons value values =>
          have tailSize : kinds.length = values.length := by
            simpa using sizeEq
          obtain ⟨lane, headRead, headRelated⟩ :=
            each 0 kind value (by simp) (by simp)
          have tailEach : ∀ offset tailKind tailValue,
              kinds[offset]? = some tailKind →
              values[offset]? = some tailValue →
              ∃ lane,
                state.memory.readClosureCapture
                    (closureCaptureAddress address.value (index + 1 + offset))
                      tailKind = .ok lane ∧
                  ValueRel witness tailKind lane tailValue := by
            intro offset tailKind tailValue kindAt valueAt
            obtain ⟨tailLane, tailRead, tailRelated⟩ :=
              each (offset + 1) tailKind tailValue (by simpa using kindAt)
                (by simpa using valueAt)
            exact ⟨tailLane, by simpa [Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using tailRead, tailRelated⟩
          obtain ⟨words, wordsRead, wordsRelated⟩ :=
            ih (index + 1) values tailSize tailEach
          by_cases admissible : kind.isObjectField = true
          · obtain ⟨word, laneEq, wordRelated⟩ :=
              headRelated.ownershipOfObjectField admissible
            subst lane
            have normalizedRead :
                state.memory.readClosureCapture
                    (closureCaptureAddress address.value index) kind =
                  .ok (.word32 word) := by
              simpa using headRead
            refine ⟨word :: words, ?_, ?_⟩
            · simp only [readClosureOwnedReferences, admissible, if_true]
              rw [normalizedRead]
              simp only [liftMemory, Bind.bind, Except.bind]
              rw [wordsRead]
              rfl
            · simpa [closureOwnedValues, admissible] using
                (OwnershipValuesRel.cons wordRelated wordsRelated)
          · have rejected : kind.isObjectField = false :=
              by cases found : kind.isObjectField <;> simp_all
            refine ⟨words, ?_, ?_⟩
            · simp [readClosureOwnedReferences, rejected, wordsRead]
            · simpa [closureOwnedValues, rejected] using wordsRelated

/-- The local closure decoder supplies exactly the pointwise hypotheses of
the executable ownership-list theorem. -/
theorem ClosureObjectRel.readClosureOwnedReferences
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32} {function : Lean.Name} {arity : Nat}
    {captureKinds : Array AbiKind} {captures : Array Value}
    (related : ClosureObjectRel state witness dispatch descriptors address
      function arity captureKinds captures) :
    ∃ words,
      Fir.Wasm.Concrete.readClosureOwnedReferences state address 0
          captureKinds.toList = .ok words ∧
        OwnershipValuesRel witness words
          (closureOwnedValues captureKinds.toList captures.toList) := by
  apply readClosureOwnedReferences_of_each state witness address 0
      captureKinds.toList captures.toList
  · simpa using related.captureKindsSize
  · intro offset kind value kindAt valueAt
    obtain ⟨lane, read, laneRelated⟩ := related.captures offset kind value
      (by simpa using kindAt) (by simpa using valueAt)
    exact ⟨lane, by simpa using read, laneRelated⟩

/-- A packaged live closure cell makes the public ownership decoder return
the filtered semantic captures under the module's one immutable descriptor
table. -/
theorem ClosureCellRel.readOwnedReferences
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : ClosureCellRel state witness address cell) :
    ∃ (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
        (captures : Array Value) (header : Header) (words : List Word32),
      cell.object = .closure function arity captures ∧
      state.readLiveHeader address = .ok header ∧
      Fir.Wasm.Concrete.readOwnedReferences state address header
          witness.closureDescriptors = .ok words ∧
      OwnershipValuesRel witness words
        (closureOwnedValues captureKinds.toList captures.toList) := by
  cases related with
  | @closure function arity captureKinds captures header _ objectEq objectRelated
      headerRead headerKind descriptorLookup ordinary fixedCount extent refCount
      persistent live =>
      obtain ⟨words, wordsRead, wordsRelated⟩ :=
        objectRelated.readClosureOwnedReferences
      refine ⟨function, arity, captureKinds, captures, header, words, objectEq,
        headerRead, ?_, wordsRelated⟩
      simpa [Fir.Wasm.Concrete.readOwnedReferences, headerKind,
        descriptorLookup, objectRelated.captureKindsSize, fixedCount] using wordsRead

end Fir.Wasm.Concrete
