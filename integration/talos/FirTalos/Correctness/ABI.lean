import FirTalos.Codec

namespace FirTalos.Correctness

open Fir.Wasm
open Fir.LeanIR.Impure

deriving instance ReflBEq, LawfulBEq for AbiKind
deriving instance ReflBEq, LawfulBEq for ObjectRef
deriving instance ReflBEq, LawfulBEq for ScalarValue
deriving instance ReflBEq, LawfulBEq for Value

private theorem value_eq_of_beq_true {left right : Value}
    (equal : (left == right) = true) : left = right :=
  LawfulBEq.eq_of_beq equal

/--
The proof invariant needed by the alias-preserving handle codec: a handle found
by semantic value is non-reserved and maps back to that same value.
-/
def Coherent (table : HandleTable) : Prop :=
  ∀ {value : Value} {handle : Handle},
    HandleTable.findHandle? table.entries value = some handle →
      handle ≠ reservedHandle ∧ HandleTable.lookup? table.entries handle = some value

/-- Every allocated handle lies strictly below the table's next fresh handle. -/
def FreshHandles (table : HandleTable) : Prop :=
  ∀ {handle : Handle} {value : Value},
    HandleTable.lookup? table.entries handle = some value → handle.toNat < table.next

/-- Chainable codec invariant used by multi-operation lowering simulations. -/
def HandleTableInvariant (table : HandleTable) : Prop :=
  Coherent table ∧ FreshHandles table

/-- Every handle decoded before an allocation retains its semantic value. -/
def HandleTableExtends (before after : HandleTable) : Prop :=
  ∀ {handle : Handle} {value : Value},
    HandleTable.lookup? before.entries handle = some value →
      HandleTable.lookup? after.entries handle = some value

@[simp] theorem coherent_empty : Coherent ({} : HandleTable) := by
  simp [Coherent, HandleTable.findHandle?]

@[simp] theorem handleTableInvariant_empty : HandleTableInvariant ({} : HandleTable) := by
  simp [HandleTableInvariant, FreshHandles, HandleTable.lookup?]

theorem HandleTableInvariant.coherent {table : HandleTable}
    (invariant : HandleTableInvariant table) : Coherent table :=
  invariant.1

@[refl] theorem HandleTableExtends.refl (table : HandleTable) :
    HandleTableExtends table table := by
  intro handle value lookup
  exact lookup

theorem HandleTableExtends.trans {first second third : HandleTable}
    (firstSecond : HandleTableExtends first second)
    (secondThird : HandleTableExtends second third) :
    HandleTableExtends first third := by
  intro handle value lookup
  exact secondThird (firstSecond lookup)

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

/-- Successful handle allocation preserves coherence and next-handle freshness. -/
theorem handleTableInvariant_of_encode
    {before after : HandleTable} {kind : AbiKind} {value : Value} {handle : Handle}
    (invariant : HandleTableInvariant before)
    (usesHandle : kind.usesHandle = true)
    (encoded : before.encode kind value = .ok (after, handle)) :
    HandleTableInvariant after := by
  rcases invariant with ⟨coherent, fresh⟩
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
      exact ⟨coherent, fresh⟩
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
          let newHandle := UInt32.ofNat before.next
          have next_lt_size : before.next < UInt32.size := by
            simp [UInt32.size, maxHandle] at exhausted ⊢
            omega
          have next_toNat : newHandle.toNat = before.next := by
            exact UInt32.toNat_ofNat_of_lt' next_lt_size
          have new_not_reserved : newHandle ≠ reservedHandle := by
            intro equal
            have : before.next = 0 := by
              rw [← next_toNat, equal]
              rfl
            simp [firstHandle] at invalidNext
            omega
          constructor
          · intro candidate candidateHandle candidateFound
            by_cases sameValue : value == candidate
            · simp [HandleTable.findHandle?, sameValue] at candidateFound
              have equalValue : value = candidate := value_eq_of_beq_true sameValue
              subst candidateHandle
              subst candidate
              exact ⟨new_not_reserved, by simp [HandleTable.lookup?]⟩
            · simp [HandleTable.findHandle?, sameValue] at candidateFound
              rcases coherent candidateFound with ⟨notReserved, lookup⟩
              have old_lt := fresh lookup
              have new_ne_old : newHandle ≠ candidateHandle := by
                intro equal
                have equalNat := congrArg UInt32.toNat equal
                rw [next_toNat] at equalNat
                omega
              exact ⟨notReserved, by
                simp [HandleTable.lookup?, newHandle, new_ne_old, lookup]⟩
          · intro candidateHandle candidate lookup
            by_cases sameHandle : newHandle == candidateHandle
            · have equal : newHandle = candidateHandle := by simpa using sameHandle
              subst candidateHandle
              change newHandle.toNat < before.next + 1
              rw [next_toNat]
              omega
            · simp [HandleTable.lookup?, newHandle, sameHandle] at lookup
              have old_lt := fresh lookup
              change candidateHandle.toNat < before.next + 1
              omega

/-- Successful handle encoding either reuses the table or extends it freshly. -/
theorem handleTableExtends_of_encode
    {before after : HandleTable} {kind : AbiKind} {value : Value} {handle : Handle}
    (invariant : HandleTableInvariant before)
    (usesHandle : kind.usesHandle = true)
    (encoded : before.encode kind value = .ok (after, handle)) :
    HandleTableExtends before after := by
  unfold HandleTableExtends
  rcases invariant with ⟨_, fresh⟩
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
  intro oldHandle oldValue oldLookup
  cases found : HandleTable.findHandle? before.entries value with
  | some oldHandle =>
      simp [HandleTable.encode, kindNotErased, usesHandle, acceptsValue, found] at encoded
      rcases encoded with ⟨rfl, rfl⟩
      exact oldLookup
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
          let newHandle := UInt32.ofNat before.next
          have next_lt_size : before.next < UInt32.size := by
            simp [UInt32.size, maxHandle] at exhausted ⊢
            omega
          have next_toNat : newHandle.toNat = before.next := by
            exact UInt32.toNat_ofNat_of_lt' next_lt_size
          have old_lt := fresh oldLookup
          have new_ne_old : newHandle ≠ oldHandle := by
            intro equal
            have equalNat := congrArg UInt32.toNat equal
            rw [next_toNat] at equalNat
            omega
          simp [HandleTable.lookup?, newHandle, new_ne_old, oldLookup]

/-- Direct handle decoding is stable when successful lookups are preserved. -/
theorem decode_of_handleTableExtends
    {before after : HandleTable} {handle : Handle} {value : Value}
    (extension : HandleTableExtends before after)
    (decoded : before.decode handle = .ok value) :
    after.decode handle = .ok value := by
  by_cases reserved : handle == reservedHandle
  · simp [HandleTable.decode, reserved] at decoded
  · simp only [HandleTable.decode, reserved] at decoded ⊢
    cases beforeLookup : HandleTable.lookup? before.entries handle with
    | none => simp [beforeLookup] at decoded
    | some oldValue =>
        have afterLookup := extension beforeLookup
        rw [afterLookup]
        simpa [beforeLookup] using decoded

/-- Handle-based decoding is stable when the handle table grows. -/
theorem decodeAs_of_handleTableExtends
    {before after : HandleTable} {kind : AbiKind} {handle : Handle} {value : Value}
    (extension : HandleTableExtends before after)
    (decoded : before.decodeAs kind handle = .ok value) :
    after.decodeAs kind handle = .ok value := by
  by_cases erased : (kind == .erased) = true
  · have kindEq : kind = .erased := LawfulBEq.eq_of_beq erased
    subst kind
    by_cases handleReserved : (handle == reservedHandle) = true
    · simp only [HandleTable.decodeAs, beq_self_eq_true, ↓reduceIte,
        handleReserved] at decoded ⊢
      exact decoded
    · simp only [HandleTable.decodeAs, beq_self_eq_true, ↓reduceIte,
        handleReserved] at decoded
      change Except.error (HandleError.invalidSentinel .erased handle) =
        Except.ok value at decoded
      contradiction
  · by_cases usesHandle : kind.usesHandle = true
    · simp only [HandleTable.decodeAs, erased, Bool.false_eq_true, ↓reduceIte,
        usesHandle] at decoded ⊢
      cases beforeDecoded : before.decode handle with
      | error error =>
          rw [beforeDecoded] at decoded
          contradiction
      | ok decodedValue =>
          have afterDecoded :=
            decode_of_handleTableExtends extension beforeDecoded
          rw [afterDecoded]
          rw [beforeDecoded] at decoded
          exact decoded
    · simp only [HandleTable.decodeAs, erased, Bool.false_eq_true, ↓reduceIte,
        usesHandle] at decoded
      contradiction

/-- Physical ABI decoding is stable under an alias-preserving table extension. -/
theorem decodeValue_of_handleTableExtends
    {before after : HandleTable} {kind : AbiKind} {physical : Wasm.Value}
    {value : Value}
    (extension : HandleTableExtends before after)
    (decoded : decodeValue before kind physical = .ok value) :
    decodeValue after kind physical = .ok value := by
  cases kind <;> cases physical <;> simp only [decodeValue] at decoded ⊢ <;>
    try exact decoded
  all_goals
    split at decoded
    · rename_i decodedValue decodedBefore
      have decodedAfter :=
        decodeAs_of_handleTableExtends extension decodedBefore
      rw [decodedAfter]
      simpa using decoded
    · contradiction

theorem decodesValue_of_handleTableExtends
    {before after : HandleTable} {kind : AbiKind} {physical : Wasm.Value}
    {value : Value}
    (extension : HandleTableExtends before after)
    (decoded : DecodesValue before kind physical value) :
    DecodesValue after kind physical value :=
  decodeValue_of_handleTableExtends extension decoded

theorem decodeValue_handle_of_decodeAs
    {table : HandleTable} {kind : AbiKind} {handle : Handle} {value : Value}
    (usesHandle : kind.usesHandle = true)
    (decoded : table.decodeAs kind handle = .ok value) :
    decodeValue table kind (.i32 handle) = .ok value := by
  cases kind <;> simp_all [AbiKind.usesHandle, decodeValue]

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
