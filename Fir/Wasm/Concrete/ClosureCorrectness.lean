import Fir.Wasm.Concrete.ClosureRuntime
import Fir.Wasm.Concrete.FreshAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Local decoder relation for one concrete closure. The generated trampoline
supplies the static capture kinds; the header recovers target/arity/fixed
metadata, and every occupied slot decodes to the corresponding semantic
capture under the allocation witness. -/
structure ClosureObjectRel (state : MemoryState) (witness : RefinementWitness)
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (address : Word32)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (semantic : Array Value) : Prop where
  descriptor : witness.descriptors.lookup? address =
    some (.closure function arity captureKinds)
  metadata : ∃ metadata,
    readClosureMetadata state dispatch descriptors address = .ok metadata ∧
      metadata.function = function ∧ metadata.arity = arity ∧
      metadata.fixed = semantic.size ∧ metadata.captureKinds = captureKinds
  captureKindsSize : captureKinds.size = semantic.size
  captures : ∀ (index : Nat) (kind : AbiKind) (value : Value),
    captureKinds[index]? = some kind →
    semantic[index]? = some value →
    ∃ lane,
      state.memory.readClosureCapture
          (closureCaptureAddress address.value index) kind = .ok lane ∧
        ValueRel witness kind lane value

/-- A locally related closure satisfies the exact successful metadata test
used by the generated Wasm-level trampoline. -/
theorem ClosureObjectRel.matches
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {semantic : Array Value}
    (related : ClosureObjectRel state witness dispatch descriptors address
      function arity captureKinds semantic) :
    closureMatches state dispatch descriptors address function arity semantic.size =
      .ok 1 := by
  obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
      metadataFixed, metadataKinds⟩ := related.metadata
  unfold closureMatches
  rw [metadataRead]
  simp only [Bind.bind, Except.bind]
  simp [metadataFunction, metadataArity, metadataFixed]
  rfl

/-- Successful closure metadata decoding returns the exact live header read
at the same address. This lets ownership proofs reuse the packaged refcount
and persistence equations without reopening descriptor lookup details. -/
theorem readClosureMetadata_header_eq
    {state : MemoryState} {dispatch : ClosureDispatchTable}
    {descriptors : ClosureDescriptorTable} {address : Word32}
    {metadata : ClosureMetadata} {header : Header}
    (metadataRead :
      readClosureMetadata state dispatch descriptors address = .ok metadata)
    (headerRead : state.readLiveHeader address = .ok header) :
    metadata.header = header := by
  have closureHeaderRead : readClosureHeader state address = .ok metadata.header := by
    unfold readClosureMetadata at metadataRead
    cases operation : readClosureHeader state address with
    | error failure =>
        rw [operation] at metadataRead
        contradiction
    | ok decodedHeader =>
        rw [operation] at metadataRead
        simp only [Bind.bind, Except.bind] at metadataRead
        split at metadataRead <;> try contradiction
        split at metadataRead <;> try contradiction
        split at metadataRead <;> try contradiction
        have metadataEq := Except.ok.inj metadataRead
        subst metadata
        rfl
  unfold readClosureHeader at closureHeaderRead
  split at closureHeaderRead <;> try contradiction
  rw [headerRead] at closureHeaderRead
  simp only [liftMemory, Bind.bind, Except.bind] at closureHeaderRead
  split at closureHeaderRead <;> try contradiction
  split at closureHeaderRead <;> try contradiction
  exact (Except.ok.inj closureHeaderRead).symm

/-- The checked concrete match operation agrees exactly with the semantic
function/arity/fixed-count predicate, including the nonmatching result. -/
theorem ClosureObjectRel.matches_eq
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {semantic : Array Value}
    (related : ClosureObjectRel state witness dispatch descriptors address
      function arity captureKinds semantic)
    (expectedFunction : Lean.Name) (expectedArity expectedFixed : Nat) :
    closureMatches state dispatch descriptors address expectedFunction expectedArity
        expectedFixed =
      .ok (if function == expectedFunction && arity == expectedArity &&
          semantic.size == expectedFixed then 1 else 0) := by
  obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
      metadataFixed, metadataKinds⟩ := related.metadata
  unfold closureMatches
  rw [metadataRead]
  simp only [Bind.bind, Except.bind]
  simp [metadataFunction, metadataArity, metadataFixed]
  rfl

/-- Typed projection from a locally related closure returns the concrete lane
related to the matching semantic capture. -/
theorem ClosureObjectRel.project
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {semantic : Array Value}
    (related : ClosureObjectRel state witness dispatch descriptors address
      function arity captureKinds semantic)
    (index : Nat) (kind : AbiKind) (value : Value)
    (kindAt : captureKinds[index]? = some kind)
    (valueAt : semantic[index]? = some value) :
    ∃ lane,
      projectClosureCapture state dispatch descriptors address function arity
          semantic.size index kind = .ok lane ∧
        ValueRel witness kind lane value := by
  obtain ⟨lane, read, laneRelated⟩ :=
    related.captures index kind value kindAt valueAt
  obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
      metadataFixed, metadataKinds⟩ := related.metadata
  obtain ⟨indexLt, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
  have metadataCheck :
      (metadata.function == function && metadata.arity == arity &&
        metadata.fixed == semantic.size) = true := by
    simp [metadataFunction, metadataArity, metadataFixed]
  have indexCheck : index < semantic.size := indexLt
  have kindCheck : metadata.captureKinds[index]? = some kind := by
    rw [metadataKinds]
    exact kindAt
  refine ⟨lane, ?_, laneRelated⟩
  unfold projectClosureCapture
  rw [metadataRead]
  simp only [Bind.bind, Except.bind]
  rw [if_pos metadataCheck]
  rw [if_pos indexCheck]
  rw [kindCheck]
  simp only [show kind.refines kind = true by cases kind <;> decide,
    ↓reduceIte]
  exact congrArg liftMemory read

/-- A concrete application snapshot carries every fixed argument in its
original typed lane. This relation deliberately does not require the source
closure cell to remain live: exclusive application releases that cell before
the generated projection prefix runs. -/
structure ClosureApplicationRel (witness : RefinementWitness)
    (application : ClosureApplication) (address : Word32)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (semantic : Array Value) : Prop where
  /-- The snapshot retains the allocation-time ABI descriptor even when
  exclusive ownership consumption has made the source closure cell dead. -/
  descriptor : witness.descriptors.lookup? address =
    some (.closure function arity captureKinds)
  objectEq : application.object = address
  functionEq : application.function = function
  arityEq : application.arity = arity
  captureKindsEq : application.captureKinds = captureKinds
  captureKindsSize : captureKinds.size = semantic.size
  capturesSize : application.captures.size = semantic.size
  captures : ∀ (index : Nat) (kind : AbiKind) (value : Value),
    captureKinds[index]? = some kind →
    semantic[index]? = some value →
    ∃ lane : LaneValue,
      application.captures[index]? = some lane ∧
        ValueRel witness kind lane value

/-- Projection from an application snapshot may widen the captured lane along
the compiler's ABI refinement order. The physical bits are unchanged; only a
precise `object` or `tagged` capture may widen to `tobject`. -/
theorem ClosureApplicationRel.project_of_refines
    {witness : RefinementWitness} {application : ClosureApplication}
    {address : Word32} {function : Lean.Name} {arity : Nat}
    {captureKinds : Array AbiKind} {semantic : Array Value}
    (related : ClosureApplicationRel witness application address function arity
      captureKinds semantic)
    (index : Nat) (actualKind expectedKind : AbiKind) (value : Value)
    (kindAt : captureKinds[index]? = some actualKind)
    (kindRefines : actualKind.refines expectedKind = true)
    (valueAt : semantic[index]? = some value) :
    ∃ lane,
      application.project address function arity semantic.size index expectedKind =
        .ok lane ∧
      ValueRel witness actualKind lane value := by
  obtain ⟨lane, laneAt, laneRelated⟩ :=
    related.captures index actualKind value kindAt valueAt
  obtain ⟨indexLt, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
  have applicationKindAt :
      application.captureKinds[index]? = some actualKind := by
    rw [related.captureKindsEq]
    exact kindAt
  refine ⟨lane, ?_, laneRelated⟩
  unfold ClosureApplication.project
  simp only [related.objectEq, related.functionEq, related.arityEq,
    related.capturesSize, beq_self_eq_true, Bind.bind, Except.bind]
  rw [if_pos (by
    change ((address.value == address.value) && true && true && true) = true
    simp)]
  rw [if_pos indexLt]
  rw [applicationKindAt]
  simp only [kindRefines, ↓reduceIte]
  rw [laneAt]
  rfl

/-- Exact-kind projection is the reflexive specialization of ABI-refining
application projection. -/
theorem ClosureApplicationRel.project
    {witness : RefinementWitness} {application : ClosureApplication}
    {address : Word32} {function : Lean.Name} {arity : Nat}
    {captureKinds : Array AbiKind} {semantic : Array Value}
    (related : ClosureApplicationRel witness application address function arity
      captureKinds semantic)
    (index : Nat) (kind : AbiKind) (value : Value)
    (kindAt : captureKinds[index]? = some kind)
    (valueAt : semantic[index]? = some value) :
    ∃ lane,
      application.project address function arity semantic.size index kind =
        .ok lane ∧
      ValueRel witness kind lane value := by
  exact related.project_of_refines index kind kind value kindAt
    (by cases kind <;> decide) valueAt

/-- Pointwise related closure slots can be read into one exact ordered
snapshot. The explicit list theorem is the induction boundary used by
`takeClosureApplication`; clients consume the array-shaped relation below. -/
private theorem readClosureCaptures_of_each
    (state : MemoryState) (witness : RefinementWitness) (address : Word32)
    (index : Nat) (kinds : List AbiKind) (values : List Value)
    (sizeEq : kinds.length = values.length)
    (each : ∀ (offset : Nat) (kind : AbiKind) (value : Value),
      kinds[offset]? = some kind →
      values[offset]? = some value →
      ∃ lane : LaneValue,
        state.memory.readClosureCapture
            (closureCaptureAddress address.value (index + offset)) kind =
              .ok lane ∧
          ValueRel witness kind lane value) :
    ∃ lanes : List LaneValue,
      readClosureCaptures state address index kinds = .ok lanes ∧
      lanes.length = values.length ∧
      ∀ (offset : Nat) (kind : AbiKind) (value : Value),
        kinds[offset]? = some kind →
        values[offset]? = some value →
        ∃ lane : LaneValue, lanes[offset]? = some lane ∧
          ValueRel witness kind lane value := by
  induction kinds generalizing index values with
  | nil =>
      cases values with
      | nil => exact ⟨[], rfl, rfl, by simp⟩
      | cons value values => simp at sizeEq
  | cons kind kinds ih =>
      cases values with
      | nil => simp at sizeEq
      | cons value values =>
          have tailSize : kinds.length = values.length := by
            simpa using sizeEq
          obtain ⟨lane, laneRead, laneRelated⟩ :=
            each 0 kind value (by simp) (by simp)
          have tailEach : ∀ (offset : Nat) (tailKind : AbiKind)
              (tailValue : Value),
              kinds[offset]? = some tailKind →
              values[offset]? = some tailValue →
              ∃ tailLane : LaneValue,
                state.memory.readClosureCapture
                    (closureCaptureAddress address.value
                      (index + 1 + offset)) tailKind = .ok tailLane ∧
                  ValueRel witness tailKind tailLane tailValue := by
            intro offset tailKind tailValue kindAt valueAt
            obtain ⟨tailLane, tailRead, tailRelated⟩ :=
              each (offset + 1) tailKind tailValue (by simpa using kindAt)
                (by simpa using valueAt)
            exact ⟨tailLane, by simpa [Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using tailRead, tailRelated⟩
          obtain ⟨lanes, lanesRead, lanesSize, lanesRelated⟩ :=
            ih (index + 1) values tailSize tailEach
          refine ⟨lane :: lanes, ?_, by simp [lanesSize], ?_⟩
          · unfold readClosureCaptures
            have laneRead' :
                state.memory.readClosureCapture
                    (closureCaptureAddress address.value index) kind =
                  .ok lane := by
              simpa using laneRead
            rw [congrArg liftMemory laneRead']
            simp only [Bind.bind, Except.bind]
            rw [lanesRead]
            rfl
          · intro offset actualKind actualValue kindAt valueAt
            cases offset with
            | zero =>
                simp at kindAt valueAt
                subst actualKind
                subst actualValue
                exact ⟨lane, by simp, laneRelated⟩
            | succ offset =>
                obtain ⟨tailLane, tailLaneAt, tailRelated⟩ :=
                  lanesRelated offset actualKind actualValue
                    (by simpa using kindAt) (by simpa using valueAt)
                exact ⟨tailLane, by simpa using tailLaneAt, tailRelated⟩

/-- Reading every capture of a locally related closure produces the
array-shaped transfer relation used after ownership has been taken. -/
theorem ClosureObjectRel.readCaptures
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32} {function : Lean.Name} {arity : Nat}
    {captureKinds : Array AbiKind} {semantic : Array Value}
    (related : ClosureObjectRel state witness dispatch descriptors address
      function arity captureKinds semantic) :
    ∃ lanes,
      readClosureCaptures state address 0 captureKinds.toList = .ok lanes ∧
      ClosureApplicationRel witness {
        object := address
        function
        arity
        captureKinds
        captures := lanes.toArray }
        address function arity captureKinds semantic := by
  obtain ⟨lanes, lanesRead, lanesSize, lanesRelated⟩ :=
    readClosureCaptures_of_each state witness address 0 captureKinds.toList
      semantic.toList (by simpa using related.captureKindsSize) (by
        intro offset kind value kindAt valueAt
        obtain ⟨lane, laneRead, laneRelated⟩ :=
          related.captures offset kind value (by simpa using kindAt)
            (by simpa using valueAt)
        exact ⟨lane, by simpa using laneRead, laneRelated⟩)
  refine ⟨lanes, lanesRead, {
    descriptor := related.descriptor
    objectEq := rfl
    functionEq := rfl
    arityEq := rfl
    captureKindsEq := rfl
    captureKindsSize := related.captureKindsSize
    capturesSize := by simpa using lanesSize
    captures := ?_ }⟩
  intro index kind value kindAt valueAt
  obtain ⟨lane, laneAt, laneRelated⟩ := lanesRelated index kind value
    (by simpa using kindAt) (by simpa using valueAt)
  exact ⟨lane, by simpa using laneAt, laneRelated⟩

/-- An eight-byte capture decoder depends only on the bytes in its slot. -/
theorem LinearMemory.readClosureCapture_of_byteFrame
    (before after : LinearMemory) (address : Nat) (kind : AbiKind)
    (frame : ∀ offset, offset < 8 →
      after.readByte (address + offset) = before.readByte (address + offset)) :
    after.readClosureCapture address kind = before.readClosureCapture address kind := by
  have readUInt32 (start : Nat) (offset : Nat)
      (startEq : start = address + offset) (within : offset + 3 < 8) :
      after.readUInt32 start = before.readUInt32 start := by
    subst start
    unfold LinearMemory.readUInt32
    rw [frame offset (by omega)]
    rw [show after.readByte (address + offset + 1) =
        before.readByte (address + offset + 1) by
      simpa only [Nat.add_assoc] using frame (offset + 1) (by omega)]
    rw [show after.readByte (address + offset + 2) =
        before.readByte (address + offset + 2) by
      simpa only [Nat.add_assoc] using frame (offset + 2) (by omega)]
    rw [show after.readByte (address + offset + 3) =
        before.readByte (address + offset + 3) by
      simpa only [Nat.add_assoc] using frame (offset + 3) (by omega)]
  have low : after.readUInt32 address = before.readUInt32 address :=
    readUInt32 address 0 (by omega) (by omega)
  have high : after.readUInt32 (address + 4) = before.readUInt32 (address + 4) :=
    readUInt32 (address + 4) 4 rfl (by omega)
  have word : after.readWord32 address = before.readWord32 address := by
    unfold LinearMemory.readWord32
    rw [low]
  have wide : after.readUInt64 address = before.readUInt64 address := by
    unfold LinearMemory.readUInt64
    rw [low, high]
  unfold LinearMemory.readClosureCapture
  cases kind.valueType <;> simp only [Bind.bind, Except.bind]
  · rw [word, high]
  · rw [wide]
  · rw [low, high]
  · rw [wide]

/-- A typed closure slot wholly below the old frontier reads identically
through a fresh prefix extension. -/
theorem MemoryState.PrefixExtension.readClosureCapture
    {before after : MemoryState} (extension : before.PrefixExtension after)
    (address : Nat) (kind : AbiKind)
    (owned : address + 8 ≤ before.heapCursor) :
    after.memory.readClosureCapture address kind =
      before.memory.readClosureCapture address kind := by
  apply LinearMemory.readClosureCapture_of_byteFrame
  intro offset offsetLt
  exact extension.readByte (address + offset) (by omega)

/-- Checked closure metadata is stable when its common header lies in the
preserved prefix. -/
theorem MemoryState.PrefixExtension.readClosureMetadata
    {before after : MemoryState} (extension : before.PrefixExtension after)
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (address : Word32)
    (headerOwned : address.value + headerBytes ≤ before.heapCursor)
    (metadata : ClosureMetadata)
    (read : Fir.Wasm.Concrete.readClosureMetadata before dispatch descriptors
      address = .ok metadata) :
    Fir.Wasm.Concrete.readClosureMetadata after dispatch descriptors address =
      .ok metadata := by
  by_cases heap : address.classify = .heap
  · cases headerResult : before.readLiveHeader address with
    | error failure =>
        unfold Fir.Wasm.Concrete.readClosureMetadata readClosureHeader at read
        simp only [heap, if_true] at read
        rw [headerResult] at read
        change Except.error (ConcreteError.ofMemory failure) = .ok metadata at read
        contradiction
    | ok header =>
        have headerAfter := extension.readLiveHeader_eq_ok address header
          headerOwned headerResult
        unfold Fir.Wasm.Concrete.readClosureMetadata readClosureHeader at read ⊢
        simpa [heap, headerResult, headerAfter, liftMemory] using read
  · unfold Fir.Wasm.Concrete.readClosureMetadata readClosureHeader at read
    simp only [heap, if_false] at read
    change Except.error (ConcreteError.source RuntimeFault.expectedClosure) =
      .ok metadata at read
    contradiction

/-- Local closure decoding is stable through fresh allocation once the
header and complete capture extent are owned by the old state. -/
theorem ClosureObjectRel.prefixExtension
    {before after : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {semantic : Array Value}
    (related : ClosureObjectRel before witness dispatch descriptors address
      function arity captureKinds semantic)
    (extension : before.PrefixExtension after)
    (headerOwned : address.value + headerBytes ≤ before.heapCursor)
    (capturesOwned : closureCaptureAddress address.value semantic.size ≤
      before.heapCursor) :
    ClosureObjectRel after witness dispatch descriptors address function arity
      captureKinds semantic := by
  refine {
    descriptor := related.descriptor
    metadata := ?_
    captureKindsSize := related.captureKindsSize
    captures := ?_ }
  · obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
        metadataFixed⟩ := related.metadata
    refine ⟨metadata, ?_, metadataFunction, metadataArity, metadataFixed⟩
    exact extension.readClosureMetadata dispatch descriptors address headerOwned
      metadata metadataRead
  · intro index kind value kindAt valueAt
    obtain ⟨lane, readBefore, laneRelated⟩ :=
      related.captures index kind value kindAt valueAt
    obtain ⟨indexLt, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
    have slotOwned : closureCaptureAddress address.value index + 8 ≤
        before.heapCursor := by
      simp [closureCaptureAddress, target] at capturesOwned ⊢
      omega
    refine ⟨lane, ?_, laneRelated⟩
    rw [extension.readClosureCapture _ kind slotOwned]
    exact readBefore

/-- Local closure decoding is monotone in proof-only witness metadata. -/
theorem ClosureObjectRel.witnessExtension
    {state : MemoryState} {before after : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {semantic : Array Value}
    (related : ClosureObjectRel state before dispatch descriptors address
      function arity captureKinds semantic)
    (extension : before.Extends after) :
    ClosureObjectRel state after dispatch descriptors address function arity
      captureKinds semantic := by
  refine {
    descriptor := extension.descriptors _ _ related.descriptor
    metadata := related.metadata
    captureKindsSize := related.captureKindsSize
    captures := ?_ }
  intro index kind value kindAt valueAt
  obtain ⟨lane, read, laneRelated⟩ :=
    related.captures index kind value kindAt valueAt
  exact ⟨lane, read, laneRelated.witnessExtension extension⟩

end Fir.Wasm.Concrete
