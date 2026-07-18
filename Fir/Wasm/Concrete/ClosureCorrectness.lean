import Fir.Wasm.Concrete.ClosureRuntime

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Local decoder relation for one concrete closure. The generated trampoline
supplies the static capture kinds; the header recovers target/arity/fixed
metadata, and every occupied slot decodes to the corresponding semantic
capture under the allocation witness. -/
structure ClosureObjectRel (state : MemoryState) (witness : RefinementWitness)
    (dispatch : ClosureDispatchTable) (address : Word32)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (semantic : Array Value) : Prop where
  descriptor : witness.descriptors.lookup? address =
    some (.closure function arity captureKinds)
  metadata : ∃ metadata,
    readClosureMetadata state dispatch address = .ok metadata ∧
      metadata.function = function ∧ metadata.arity = arity ∧
      metadata.fixed = semantic.size
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
    {dispatch : ClosureDispatchTable} {address : Word32}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {semantic : Array Value}
    (related : ClosureObjectRel state witness dispatch address function arity
      captureKinds semantic) :
    closureMatches state dispatch address function arity semantic.size = .ok 1 := by
  obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
      metadataFixed⟩ := related.metadata
  unfold closureMatches
  rw [metadataRead]
  simp only [Bind.bind, Except.bind]
  simp [metadataFunction, metadataArity, metadataFixed]
  rfl

/-- Typed projection from a locally related closure returns the concrete lane
related to the matching semantic capture. -/
theorem ClosureObjectRel.project
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {address : Word32}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {semantic : Array Value}
    (related : ClosureObjectRel state witness dispatch address function arity
      captureKinds semantic)
    (index : Nat) (kind : AbiKind) (value : Value)
    (kindAt : captureKinds[index]? = some kind)
    (valueAt : semantic[index]? = some value) :
    ∃ lane,
      projectClosureCapture state dispatch address function arity semantic.size
          index kind = .ok lane ∧
        ValueRel witness kind lane value := by
  obtain ⟨lane, read, laneRelated⟩ :=
    related.captures index kind value kindAt valueAt
  obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
      metadataFixed⟩ := related.metadata
  obtain ⟨indexLt, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
  have metadataCheck :
      (metadata.function == function && metadata.arity == arity &&
        metadata.fixed == semantic.size) = true := by
    simp [metadataFunction, metadataArity, metadataFixed]
  have indexCheck : index < semantic.size := indexLt
  refine ⟨lane, ?_, laneRelated⟩
  unfold projectClosureCapture
  rw [metadataRead]
  simp only [Bind.bind, Except.bind]
  rw [if_pos metadataCheck]
  rw [if_pos indexCheck]
  exact congrArg liftMemory read

end Fir.Wasm.Concrete
