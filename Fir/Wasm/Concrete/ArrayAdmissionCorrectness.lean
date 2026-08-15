import Fir.Wasm.Concrete.HeapRefinement
import Fir.Wasm.Concrete.NaturalDispatchCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-!
# Proof-indexed resident Array admission

The unchecked typed Array helpers are sound only after source/compiler
admission retains the erased semantic bound and the physical index shape.
This file states that smallest boundary independently of any one generated
helper.  The ordinary checked lower-level Array operations remain unchanged.
-/

/-- Every live resident Array has a logical size small enough for the
canonical immediate-Nat index representation.  This follows from the
wasm32-sized allocation header and eight-byte retained slots, not from a
whole-execution address-space assumption. -/
theorem ResidentArrayObjectRel.logicalSize_le_maxImmediatePayload
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header}
    (related :
      ResidentArrayObjectRel state witness address elements capacity header) :
    elements.size ≤ maxImmediatePayload := by
  have allocationLt : header.allocationBytes.toNat < UInt32.size :=
    header.allocationBytes.toNat_lt_size
  have retainedMinimum :
      headerBytes + target.semanticSlotBytes * capacity ≤
        residentArrayAllocationBytes capacity :=
    align8_ge _
  rw [related.allocationBytes] at allocationLt
  have sizeCapacity := related.sizeCapacity
  simp [residentArrayAllocationBytes, headerBytes, target, UInt32.size,
    maxImmediatePayload] at allocationLt retainedMinimum ⊢
  omega

/-- Missing source/compiler fact for a proof-indexed Nat Array operand.
`bound` is the erased proof; `canonical` excludes the promoted representation
that the general tagged relation intentionally permits. -/
structure ProofIndexedResidentArrayNatAdmission
    (word : Word32) (payload : UInt64) (logicalSize : Nat) : Prop where
  bound : payload.toNat < logicalSize
  fits : payload.toNat ≤ maxImmediatePayload
  canonical : word = Word32.encodeImmediate payload.toNat fits

namespace ProofIndexedResidentArrayNatAdmission

/-- A related resident Array plus the erased bound reduces admission to the
single compiler guarantee that this typed Nat operand is canonical. -/
theorem ofArray
    {state : MemoryState} {witness : RefinementWitness}
    {address indexWord : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header} {payload : UInt64}
    (array :
      ResidentArrayObjectRel state witness address elements capacity header)
    (bound : payload.toNat < elements.size)
    (canonical : indexWord = Word32.encodeImmediate payload.toNat
      (Nat.le_trans (Nat.le_of_lt bound)
        array.logicalSize_le_maxImmediatePayload)) :
    ProofIndexedResidentArrayNatAdmission indexWord payload elements.size := {
  bound
  fits := Nat.le_trans (Nat.le_of_lt bound)
    array.logicalSize_le_maxImmediatePayload
  canonical := canonical }

/-- The generated low-bit test accepts a proof-indexed Nat operand. -/
theorem lowBit
    {word : Word32} {payload : UInt64} {logicalSize : Nat}
    (evidence :
      ProofIndexedResidentArrayNatAdmission word payload logicalSize) :
    UInt32.ofNat word.value &&& 1 = 1 := by
  rw [evidence.canonical]
  exact Word32.encodeImmediate_and_one payload.toNat evidence.fits

/-- Shift-right-one recovers the exact semantic Nat index. -/
theorem decode
    {word : Word32} {payload : UInt64} {logicalSize : Nat}
    (evidence :
      ProofIndexedResidentArrayNatAdmission word payload logicalSize) :
    UInt32.ofNat word.value >>> 1 = UInt32.ofNat payload.toNat := by
  rw [evidence.canonical]
  exact Word32.encodeImmediate_shr_one payload.toNat evidence.fits

/-- The erased proof retained by admission reconstructs the exact semantic
element selected by the unchecked typed helper. -/
theorem valueAt
    {word : Word32} {payload : UInt64} {elements : Array Value}
    (evidence :
      ProofIndexedResidentArrayNatAdmission word payload elements.size) :
    ∃ value, elements[payload.toNat]? = some value := by
  exact ⟨elements[payload.toNat]'evidence.bound,
    Array.getElem?_eq_getElem evidence.bound⟩

end ProofIndexedResidentArrayNatAdmission

/-- USize indices already have an exact 64-bit lane; proof-indexed admission
retains only the erased semantic bound. -/
structure ProofIndexedResidentArrayUSizeAdmission
    (index : UInt64) (logicalSize : Nat) : Prop where
  bound : index.toNat < logicalSize
  logicalSizeFits : logicalSize ≤ maxImmediatePayload

namespace ProofIndexedResidentArrayUSizeAdmission

/-- A related resident Array and the erased source bound construct the exact
USize admission needed by an unchecked typed helper. -/
theorem ofArray
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header} {index : UInt64}
    (array :
      ResidentArrayObjectRel state witness address elements capacity header)
    (bound : index.toNat < elements.size) :
    ProofIndexedResidentArrayUSizeAdmission index elements.size := {
  bound
  logicalSizeFits := array.logicalSize_le_maxImmediatePayload }

/-- A proof-indexed USize index fits wasm32 before W7 narrows it. -/
theorem index_lt_uint32Size
    {index : UInt64} {logicalSize : Nat}
    (evidence : ProofIndexedResidentArrayUSizeAdmission index logicalSize) :
    index.toNat < UInt32.size := by
  have bound := evidence.bound
  have logicalSizeFits := evidence.logicalSizeFits
  unfold maxImmediatePayload at logicalSizeFits
  simp [UInt32.size]
  omega

/-- Wasm32 narrowing preserves the exact semantic USize index. -/
theorem narrowed_toNat
    {index : UInt64} {logicalSize : Nat}
    (evidence : ProofIndexedResidentArrayUSizeAdmission index logicalSize) :
    (UInt32.ofNat index.toNat).toNat = index.toNat := by
  simp [Nat.mod_eq_of_lt (evidence.index_lt_uint32Size)]

/-- Narrowing is performed only for a semantic index selected by the erased
source proof. -/
theorem valueAt
    {index : UInt64} {elements : Array Value}
    (evidence :
      ProofIndexedResidentArrayUSizeAdmission index elements.size) :
    ∃ value, elements[index.toNat]? = some value := by
  exact ⟨elements[index.toNat]'evidence.bound,
    Array.getElem?_eq_getElem evidence.bound⟩

end ProofIndexedResidentArrayUSizeAdmission

end Fir.Wasm.Concrete
