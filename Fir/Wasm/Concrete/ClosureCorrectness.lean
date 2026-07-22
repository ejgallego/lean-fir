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
  captures : ∀ index kind value,
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
  rw [show (metadata.captureKinds[index]? == some kind) = true by
    rw [kindCheck]
    cases kind <;> decide]
  simp only [if_true]
  exact congrArg liftMemory read

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
