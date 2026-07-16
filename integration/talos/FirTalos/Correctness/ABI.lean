import FirTalos.Codec

namespace FirTalos.Correctness

open Fir.Wasm
open Fir.LeanIR.Impure

/--
The proof invariant needed by the alias-preserving handle codec: a handle found
by semantic value is non-reserved and maps back to that same value.
-/
def Coherent (table : HandleTable) : Prop :=
  ∀ {value : Value} {handle : Handle},
    HandleTable.findHandle? table.entries value = some handle →
      handle ≠ reservedHandle ∧ HandleTable.lookup? table.entries handle = some value

@[simp] theorem coherent_empty : Coherent ({} : HandleTable) := by
  simp [Coherent, HandleTable.findHandle?]

/--
Successful opaque-handle encoding is immediately decodable when the input
table is coherent. The `usesHandle` premise deliberately excludes the erased
sentinel, which has its own fixed physical representation.
-/
theorem decodeAs_of_encode
    {before after : HandleTable} {kind : AbiKind} {value : Value} {handle : Handle}
    (coherent : Coherent before)
    (usesHandle : kind.usesHandle = true)
    (encoded : before.encode kind value = .ok (after, handle)) :
    after.decodeAs kind handle = .ok value := by
  have kindNotErased : (kind == .erased) = false := by
    cases kind <;> simp_all [AbiKind.usesHandle] <;> rfl
  have acceptsValue : kind.acceptsValue value = true := by
    cases accepted : kind.acceptsValue value with
    | false =>
        exfalso
        simp only [HandleTable.encode, kindNotErased, usesHandle, accepted] at encoded
        change Except.error (HandleError.valueKindMismatch kind value) =
          Except.ok (after, handle) at encoded
        contradiction
    | true => rfl
  cases found : HandleTable.findHandle? before.entries value with
  | some oldHandle =>
      simp [HandleTable.encode, kindNotErased, usesHandle, acceptsValue, found] at encoded
      rcases encoded with ⟨rfl, rfl⟩
      rcases coherent found with ⟨notReserved, lookup⟩
      simp [HandleTable.decodeAs, kindNotErased, usesHandle, HandleTable.decode,
        notReserved, lookup]
      change (if kind.acceptsValue value = true then Except.ok value else
        Except.error (HandleError.valueKindMismatch kind value)) = Except.ok value
      simp [acceptsValue]
  | none =>
      by_cases invalidNext : before.next < firstHandle
      · simp [HandleTable.encode, kindNotErased, usesHandle, acceptsValue, found,
          invalidNext] at encoded
      · by_cases exhausted : maxHandle < before.next
        · simp [HandleTable.encode, kindNotErased, usesHandle, acceptsValue, found,
            invalidNext, exhausted] at encoded
        · simp [HandleTable.encode, kindNotErased, usesHandle, acceptsValue, found,
            invalidNext, exhausted] at encoded
          rcases encoded with ⟨rfl, rfl⟩
          have next_lt_size : before.next < UInt32.size := by
            simp [UInt32.size, maxHandle] at *
            omega
          have next_toNat : (UInt32.ofNat before.next).toNat = before.next :=
            UInt32.toNat_ofNat_of_lt' next_lt_size
          have notReserved : UInt32.ofNat before.next ≠ reservedHandle := by
            intro equal
            have : before.next = 0 := by
              rw [← next_toNat, equal]
              rfl
            simp [firstHandle] at invalidNext
            omega
          simp [HandleTable.decodeAs, kindNotErased, usesHandle, HandleTable.decode,
            notReserved, HandleTable.lookup?]
          change (if kind.acceptsValue value = true then Except.ok value else
            Except.error (HandleError.valueKindMismatch kind value)) = Except.ok value
          simp [acceptsValue]

@[simp] theorem decodeValue_uint8 (table : HandleTable) (value : UInt8) :
    decodeValue table .uint8 (.i32 (UInt32.ofNat value.toNat)) =
      .ok (.scalar (.uint8 value)) := by
  simp [decodeValue]
  have := value.toNat_lt
  omega

@[simp] theorem decodeValue_uint16 (table : HandleTable) (value : UInt16) :
    decodeValue table .uint16 (.i32 (UInt32.ofNat value.toNat)) =
      .ok (.scalar (.uint16 value)) := by
  simp [decodeValue]
  have := value.toNat_lt
  omega

@[simp] theorem decodeValue_uint32 (table : HandleTable) (value : UInt32) :
    decodeValue table .uint32 (.i32 value) = .ok (.scalar (.uint32 value)) := rfl

@[simp] theorem decodeValue_uint64 (table : HandleTable) (value : UInt64) :
    decodeValue table .uint64 (.i64 value) = .ok (.scalar (.uint64 value)) := rfl

@[simp] theorem decodeValue_usize (table : HandleTable) (value : UInt64) :
    decodeValue table .usize (.i64 value) = .ok (.usize value) := rfl

end FirTalos.Correctness
