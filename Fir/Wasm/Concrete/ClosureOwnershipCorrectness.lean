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

/-- A capture rejected by the concrete ownership filter cannot be a semantic
heap reference, so FIR's recursive-release step is the identity on it. -/
private theorem ValueRel.releaseNoOp_of_notObjectField
    {witness : RefinementWitness} {kind : AbiKind} {lane : LaneValue}
    {value : Value} (related : ValueRel witness kind lane value)
    (rejected : kind.isObjectField = false) (fuel : Nat)
    (runtime : RuntimeState) :
    (match value with
    | .object (.heap child) =>
        Fir.LeanIR.Impure.decLocationFuel fuel runtime child
    | _ => .ok runtime) = .ok runtime := by
  cases related with
  | object | tagged | tobject | erased =>
      simp [AbiKind.isObjectField] at rejected
  | reuseNone | reuseSome | uint8 | uint16 | uint32 | uint64 | usize => rfl

/-- Filtering statically non-owning closure captures preserves FIR's release
fold because every omitted typed value takes the semantic no-op branch. -/
private theorem closureOwnedValues_foldlM_eq_of_each
    (witness : RefinementWitness) (kinds : List AbiKind) (values : List Value)
    (sizeEq : kinds.length = values.length)
    (each : ∀ (offset : Nat) (kind : AbiKind) (value : Value),
      kinds[offset]? = some kind →
      values[offset]? = some value →
      ∃ lane, ValueRel witness kind lane value)
    (fuel : Nat) (runtime : RuntimeState) :
    values.foldlM (init := runtime) (fun next value =>
      match value with
      | .object (.heap child) =>
          Fir.LeanIR.Impure.decLocationFuel fuel next child
      | _ => .ok next) =
    (closureOwnedValues kinds values).foldlM (init := runtime) (fun next value =>
      match value with
      | .object (.heap child) =>
          Fir.LeanIR.Impure.decLocationFuel fuel next child
      | _ => .ok next) := by
  induction kinds generalizing values runtime with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at sizeEq
  | cons kind kinds ih =>
      cases values with
      | nil => simp at sizeEq
      | cons value values =>
          have tailSize : kinds.length = values.length := by
            simpa using sizeEq
          obtain ⟨lane, headRelated⟩ := each 0 kind value (by simp) (by simp)
          have tailEach : ∀ (offset : Nat) (tailKind : AbiKind) (tailValue : Value),
              kinds[offset]? = some tailKind →
              values[offset]? = some tailValue →
              ∃ lane, ValueRel witness tailKind lane tailValue := by
            intro offset tailKind tailValue kindAt valueAt
            exact each (offset + 1) tailKind tailValue (by simpa using kindAt)
              (by simpa using valueAt)
          by_cases admissible : kind.isObjectField = true
          · simp only [closureOwnedValues, admissible, if_true, List.foldlM_cons]
            cases headOperation :
                (match value with
                | .object (.heap child) =>
                    Fir.LeanIR.Impure.decLocationFuel fuel runtime child
                | _ => .ok runtime) with
            | error fault => rfl
            | ok next => exact ih values tailSize tailEach next
          · have rejected : kind.isObjectField = false := by
              cases found : kind.isObjectField <;> simp_all
            have headNoOp :=
              headRelated.releaseNoOp_of_notObjectField rejected fuel runtime
            simp only [closureOwnedValues, rejected, List.foldlM_cons]
            rw [headNoOp]
            exact ih values tailSize tailEach runtime

/-- The semantic release fold over every closure capture agrees with the
concrete ownership decoder's filtered capture order. -/
theorem ClosureObjectRel.foldlM_closureOwnedValues
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32} {function : Lean.Name} {arity : Nat}
    {captureKinds : Array AbiKind} {captures : Array Value}
    (related : ClosureObjectRel state witness dispatch descriptors address
      function arity captureKinds captures)
    (fuel : Nat) (runtime : RuntimeState) :
    captures.toList.foldlM (init := runtime) (fun next value =>
      match value with
      | .object (.heap child) =>
          Fir.LeanIR.Impure.decLocationFuel fuel next child
      | _ => .ok next) =
    (closureOwnedValues captureKinds.toList captures.toList).foldlM
      (init := runtime) (fun next value =>
        match value with
        | .object (.heap child) =>
            Fir.LeanIR.Impure.decLocationFuel fuel next child
        | _ => .ok next) := by
  apply closureOwnedValues_foldlM_eq_of_each witness captureKinds.toList
    captures.toList
  · simpa using related.captureKindsSize
  · intro offset kind value kindAt valueAt
    obtain ⟨lane, _, laneRelated⟩ := related.captures offset kind value
      (by simpa using kindAt) (by simpa using valueAt)
    exact ⟨lane, laneRelated⟩

/-- A capture omitted by the concrete ownership filter is also a no-op for
the closure-application retain fold. -/
theorem ValueRel.retainNoOp_of_notObjectField
    {witness : RefinementWitness} {kind : AbiKind} {lane : LaneValue}
    {value : Value} (related : ValueRel witness kind lane value)
    (rejected : kind.isObjectField = false) (runtime : RuntimeState) :
    retainOwnedValue runtime value = .ok runtime := by
  cases related with
  | object | tagged | tobject | erased =>
      simp [AbiKind.isObjectField] at rejected
  | reuseNone | reuseSome | uint8 | uint16 | uint32 | uint64 | usize => rfl

/-- Filtering statically non-owning closure captures preserves the semantic
application-retain fold because every omitted value is a typed no-op. -/
private theorem closureOwnedValues_retain_foldlM_eq_of_each
    (witness : RefinementWitness) (kinds : List AbiKind) (values : List Value)
    (sizeEq : kinds.length = values.length)
    (each : ∀ (offset : Nat) (kind : AbiKind) (value : Value),
      kinds[offset]? = some kind →
      values[offset]? = some value →
      ∃ lane, ValueRel witness kind lane value)
    (runtime : RuntimeState) :
    values.foldlM (init := runtime) retainOwnedValue =
      (closureOwnedValues kinds values).foldlM
        (init := runtime) retainOwnedValue := by
  induction kinds generalizing values runtime with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at sizeEq
  | cons kind kinds ih =>
      cases values with
      | nil => simp at sizeEq
      | cons value values =>
          have tailSize : kinds.length = values.length := by
            simpa using sizeEq
          obtain ⟨lane, headRelated⟩ := each 0 kind value (by simp) (by simp)
          have tailEach : ∀ (offset : Nat) (tailKind : AbiKind)
              (tailValue : Value),
              kinds[offset]? = some tailKind →
              values[offset]? = some tailValue →
              ∃ lane, ValueRel witness tailKind lane tailValue := by
            intro offset tailKind tailValue kindAt valueAt
            exact each (offset + 1) tailKind tailValue (by simpa using kindAt)
              (by simpa using valueAt)
          by_cases admissible : kind.isObjectField = true
          · simp only [closureOwnedValues, admissible, if_true,
              List.foldlM_cons, Bind.bind, Except.bind]
            cases headOperation : retainOwnedValue runtime value with
            | error fault => rfl
            | ok next => exact ih values tailSize tailEach next
          · have rejected : kind.isObjectField = false := by
              cases found : kind.isObjectField <;> simp_all
            have headNoOp :=
              headRelated.retainNoOp_of_notObjectField rejected runtime
            simp only [closureOwnedValues, rejected, if_false,
              List.foldlM_cons, Bind.bind, Except.bind]
            rw [headNoOp]
            exact ih values tailSize tailEach runtime

/-- The semantic application-retain fold over all fixed arguments agrees with
the exact filtered value order returned by the concrete ownership decoder. -/
theorem ClosureObjectRel.foldlM_retainOwnedValue
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32} {function : Lean.Name} {arity : Nat}
    {captureKinds : Array AbiKind} {captures : Array Value}
    (related : ClosureObjectRel state witness dispatch descriptors address
      function arity captureKinds captures)
    (runtime : RuntimeState) :
    captures.toList.foldlM (init := runtime) retainOwnedValue =
      (closureOwnedValues captureKinds.toList captures.toList).foldlM
        (init := runtime) retainOwnedValue := by
  apply closureOwnedValues_retain_foldlM_eq_of_each witness captureKinds.toList
    captures.toList
  · simpa using related.captureKindsSize
  · intro offset kind value kindAt valueAt
    obtain ⟨lane, _, laneRelated⟩ := related.captures offset kind value
      (by simpa using kindAt) (by simpa using valueAt)
    exact ⟨lane, laneRelated⟩

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
      headerRead headerKind descriptorLookup fixedCount extent refCount
      persistent live =>
      obtain ⟨words, wordsRead, wordsRelated⟩ :=
        objectRelated.readClosureOwnedReferences
      refine ⟨function, arity, captureKinds, captures, header, words, objectEq,
        headerRead, ?_, wordsRelated⟩
      simpa [Fir.Wasm.Concrete.readOwnedReferences, headerKind,
        descriptorLookup, objectRelated.captureKindsSize, fixedCount] using wordsRead

end Fir.Wasm.Concrete
