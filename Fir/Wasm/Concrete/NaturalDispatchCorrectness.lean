import Fir.Wasm.Concrete.NaturalAllocationCorrectness
import Fir.Wasm.Concrete.PromotedTagCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Exact proof-side model of W7's shared two-word immediate-Nat test. -/
def BothImmediateNaturalWords (left right : Word32) : Prop :=
  left.value % 2 = 1 ∧ right.value % 2 = 1

/-- The information recovered after the shared dispatcher selects its
two-immediate branch. The semantic references must be tagged naturals, and
both physical words are their canonical wasm32 encodings. -/
structure ImmediateNaturalPairRel (leftWord rightWord : Word32)
    (leftReference rightReference : ObjectRef)
    (leftPayload rightPayload : UInt64) : Prop where
  leftReferenceEq : leftReference = .tagged leftPayload
  rightReferenceEq : rightReference = .tagged rightPayload
  leftFits : leftPayload.toNat ≤ maxImmediatePayload
  rightFits : rightPayload.toNat ≤ maxImmediatePayload
  leftWordEq : leftWord = Word32.encodeImmediate leftPayload.toNat leftFits
  rightWordEq : rightWord = Word32.encodeImmediate rightPayload.toNat rightFits

/-- The low-bit operation emitted by resident helpers recognizes every
canonical immediate word. Keeping this UInt32 fact beside the representation
theorem avoids reproving bitvector arithmetic in each generated helper. -/
theorem Word32.encodeImmediate_and_one
    (payload : Nat) (fits : payload ≤ maxImmediatePayload) :
    UInt32.ofNat (Word32.encodeImmediate payload fits).value &&& 1 = 1 := by
  simp [Word32.encodeImmediate]
  bv_decide

/-- Logical shift-right by one is the exact resident decode of a canonical
immediate payload. -/
theorem Word32.encodeImmediate_shr_one
    (payload : Nat) (fits : payload ≤ maxImmediatePayload) :
    UInt32.ofNat (Word32.encodeImmediate payload fits).value >>> 1 =
      UInt32.ofNat payload := by
  simp [Word32.encodeImmediate]
  apply UInt32.toNat_inj.mp
  have payloadLt : payload < 4294967296 := by
    unfold maxImmediatePayload at fits
    omega
  have encodedLt : payload * 2 + 1 < 4294967296 := by
    unfold maxImmediatePayload at fits
    omega
  simp [Nat.mod_eq_of_lt payloadLt, Nat.mod_eq_of_lt encodedLt,
    Nat.shiftRight_eq_div_pow]
  omega

theorem ImmediateNaturalPairRel.wasmPairTest_eq_one
    {leftWord rightWord : Word32} {leftReference rightReference : ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) :
    (UInt32.ofNat leftWord.value &&& 1) &&&
        (UInt32.ofNat rightWord.value &&& 1) = 1 := by
  have leftBit : UInt32.ofNat leftWord.value &&& 1 = 1 := by
    rw [congrArg Word32.value pair.leftWordEq]
    exact Word32.encodeImmediate_and_one leftPayload.toNat pair.leftFits
  have rightBit : UInt32.ofNat rightWord.value &&& 1 = 1 := by
    rw [congrArg Word32.value pair.rightWordEq]
    exact Word32.encodeImmediate_and_one rightPayload.toNat pair.rightFits
  rw [leftBit, rightBit]
  decide

theorem ImmediateNaturalPairRel.wasmLeftPayload
    {leftWord rightWord : Word32} {leftReference rightReference : ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) :
    UInt32.ofNat leftWord.value >>> 1 = UInt32.ofNat leftPayload.toNat := by
  rw [pair.leftWordEq]
  exact Word32.encodeImmediate_shr_one leftPayload.toNat pair.leftFits

theorem ImmediateNaturalPairRel.wasmRightPayload
    {leftWord rightWord : Word32} {leftReference rightReference : ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) :
    UInt32.ofNat rightWord.value >>> 1 = UInt32.ofNat rightPayload.toNat := by
  rw [pair.rightWordEq]
  exact Word32.encodeImmediate_shr_one rightPayload.toNat pair.rightFits

/-- The unsigned Wasm remainder on decoded immediate payloads agrees with the
mathematical Nat remainder used by the concrete runtime contract. -/
theorem ImmediateNaturalPairRel.wasmRemainder
    {leftWord rightWord : Word32} {leftReference rightReference : ObjectRef}
    {leftPayload rightPayload : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload) :
    UInt32.ofNat leftPayload.toNat % UInt32.ofNat rightPayload.toNat =
      UInt32.ofNat (leftPayload.toNat % rightPayload.toNat) := by
  apply UInt32.toNat_inj.mp
  have leftLt : leftPayload.toNat < 4294967296 := by
    have leftFits := pair.leftFits
    unfold maxImmediatePayload at leftFits
    omega
  have rightLt : rightPayload.toNat < 4294967296 := by
    have rightFits := pair.rightFits
    unfold maxImmediatePayload at rightFits
    omega
  have remainderLt : leftPayload.toNat % rightPayload.toNat < 4294967296 := by
    by_cases zero : rightPayload.toNat = 0
    · simp [zero, leftLt]
    · exact Nat.lt_trans
        (Nat.mod_lt leftPayload.toNat (Nat.pos_of_ne_zero zero)) rightLt
  simp
  rw [Nat.mod_eq_of_lt leftLt, Nat.mod_eq_of_lt rightLt,
    Nat.mod_eq_of_lt remainderLt]

/-- A heap-classified word has a zero low bit. -/
theorem Word32.lowBit_zero_of_classify_heap (word : Word32)
    (heap : word.classify = .heap) :
    word.value % 2 = 0 := by
  unfold Word32.classify at heap
  split at heap <;> try contradiction
  split at heap <;> try contradiction
  split at heap <;> try contradiction
  omega

/-- On a well-formed witness, the low-bit test selects exactly the immediate
constructor of the tagged-reference relation. Promoted tagged naturals are
heap-classified and cannot enter the fast branch. -/
theorem TaggedReferenceRel.lowBit_eq_one_iff_immediate
    {witness : RefinementWitness} {word : Word32} {payload : UInt64}
    (valid : witness.WellFormed)
    (related : TaggedReferenceRel witness word payload) :
    word.value % 2 = 1 ↔
      ∃ fits : payload.toNat ≤ maxImmediatePayload,
        word = Word32.encodeImmediate payload.toNat fits := by
  constructor
  · intro odd
    cases related with
    | immediate payload fits => exact ⟨fits, rfl⟩
    | promoted found =>
        have heap := valid.promotedHeap _ _ found
        have nonzero : word.value ≠ 0 := by omega
        have immediate : word.classify = .immediate := by
          simp [Word32.classify, nonzero, odd]
        rw [immediate] at heap
        contradiction
  · rintro ⟨fits, rfl⟩
    simp [Word32.encodeImmediate]

/-- The shift-right-one payload decoder used by W7 is exact after the shared
low-bit dispatcher selects an immediate tagged natural. -/
theorem TaggedReferenceRel.decode_of_lowBit_eq_one
    {witness : RefinementWitness} {word : Word32} {payload : UInt64}
    (valid : witness.WellFormed)
    (related : TaggedReferenceRel witness word payload)
    (odd : word.value % 2 = 1) :
    word.value / 2 = payload.toNat := by
  obtain ⟨fits, rfl⟩ :=
    (related.lowBit_eq_one_iff_immediate valid).mp odd
  simp [Word32.encodeImmediate]
  omega

/-- A representation-polymorphic object word selected by the low-bit test is
necessarily a semantic tagged natural with its canonical immediate word. -/
theorem ObjectReferenceRel.immediate_of_lowBit_eq_one
    {witness : RefinementWitness} {word : Word32} {reference : ObjectRef}
    (valid : witness.WellFormed)
    (related : ObjectReferenceRel witness word reference)
    (odd : word.value % 2 = 1) :
    ∃ payload : UInt64,
      ∃ fits : payload.toNat ≤ maxImmediatePayload,
        reference = .tagged payload ∧
          word = Word32.encodeImmediate payload.toNat fits := by
  cases related with
  | heap heapRelated =>
      have heap := heapRelated.is_heap valid
      have even := word.lowBit_zero_of_classify_heap heap
      omega
  | tagged taggedRelated =>
      obtain ⟨fits, wordEq⟩ :=
        (taggedRelated.lowBit_eq_one_iff_immediate valid).mp odd
      exact ⟨_, fits, rfl, wordEq⟩

/-- The complementary dispatcher branch contains every heap reference and
every promoted tagged natural. This is the exact premise needed to reuse the
pre-existing checked arbitrary-precision fallback unchanged. -/
theorem ObjectReferenceRel.classify_eq_heap_of_lowBit_ne_one
    {witness : RefinementWitness} {word : Word32} {reference : ObjectRef}
    (valid : witness.WellFormed)
    (related : ObjectReferenceRel witness word reference)
    (notOdd : word.value % 2 ≠ 1) :
    word.classify = .heap := by
  cases related with
  | heap heapRelated => exact heapRelated.is_heap valid
  | tagged taggedRelated =>
      cases taggedRelated with
      | immediate payload fits =>
          exfalso
          apply notOdd
          simp [Word32.encodeImmediate]
      | promoted found => exact valid.promotedHeap _ _ found

/-- Two related `tobject` inputs satisfy W7's shared low-bit test exactly
when they form a canonical immediate-natural pair. -/
theorem ValueRel.bothImmediateNaturalWords_iff
    {witness : RefinementWitness} {leftWord rightWord : Word32}
    {leftReference rightReference : ObjectRef}
    (valid : witness.WellFormed)
    (leftRelated : ValueRel witness .tobject (.word32 leftWord)
      (.object leftReference))
    (rightRelated : ValueRel witness .tobject (.word32 rightWord)
      (.object rightReference)) :
    BothImmediateNaturalWords leftWord rightWord ↔
      ∃ leftPayload rightPayload,
        ImmediateNaturalPairRel leftWord rightWord leftReference rightReference
          leftPayload rightPayload := by
  cases leftRelated with
  | tobject leftObjectRelated =>
    cases rightRelated with
    | tobject rightObjectRelated =>
      constructor
      · rintro ⟨leftOdd, rightOdd⟩
        obtain ⟨leftPayload, leftFits, leftReferenceEq, leftWordEq⟩ :=
          leftObjectRelated.immediate_of_lowBit_eq_one valid leftOdd
        obtain ⟨rightPayload, rightFits, rightReferenceEq, rightWordEq⟩ :=
          rightObjectRelated.immediate_of_lowBit_eq_one valid rightOdd
        exact ⟨leftPayload, rightPayload, {
          leftReferenceEq
          rightReferenceEq
          leftFits
          rightFits
          leftWordEq
          rightWordEq }⟩
      · rintro ⟨leftPayload, rightPayload, pair⟩
        constructor
        · rw [pair.leftWordEq]
          simp [Word32.encodeImmediate]
        · rw [pair.rightWordEq]
          simp [Word32.encodeImmediate]

/-- When the shared pair test is false, at least one related object operand is
heap-classified, so the old checked arbitrary-precision path remains the exact
fallback for mixed, promoted, and heap-backed inputs. -/
theorem ValueRel.heapFallback_of_not_bothImmediateNaturalWords
    {witness : RefinementWitness} {leftWord rightWord : Word32}
    {leftReference rightReference : ObjectRef}
    (valid : witness.WellFormed)
    (leftRelated : ValueRel witness .tobject (.word32 leftWord)
      (.object leftReference))
    (rightRelated : ValueRel witness .tobject (.word32 rightWord)
      (.object rightReference))
    (fallback : ¬ BothImmediateNaturalWords leftWord rightWord) :
    leftWord.classify = .heap ∨ rightWord.classify = .heap := by
  cases leftRelated with
  | tobject leftObjectRelated =>
    cases rightRelated with
    | tobject rightObjectRelated =>
      by_cases leftOdd : leftWord.value % 2 = 1
      · have rightNotOdd : rightWord.value % 2 ≠ 1 := by
          intro rightOdd
          exact fallback ⟨leftOdd, rightOdd⟩
        exact .inr
          (rightObjectRelated.classify_eq_heap_of_lowBit_ne_one valid rightNotOdd)
      · exact .inl
          (leftObjectRelated.classify_eq_heap_of_lowBit_ne_one valid leftOdd)

/-- The immediate `Nat.add` branch reuses the existing canonical natural
constructor. Its result remains immediate when the sum fits and becomes the
ordinary promoted persistent natural when it crosses `maxImmediatePayload`;
the semantic heap is unchanged in both cases. -/
theorem LiveHeapRel.immediateNaturalAdd_refines
    {state result : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {leftWord rightWord resultWord : Word32}
    {left right : UInt64}
    (related : LiveHeapRel state witness runtime)
    (leftRelated : ValueRel witness .tobject (.word32 leftWord)
      (.object (.tagged left)))
    (rightRelated : ValueRel witness .tobject (.word32 rightWord)
      (.object (.tagged right)))
    (both : BothImmediateNaturalWords leftWord rightWord)
    (allocated :
      allocateNatural state (left.toNat + right.toNat) = .ok (result, resultWord)) :
    ∃ nextWitness,
      ImmediateNaturalPairRel leftWord rightWord (.tagged left) (.tagged right)
          left right ∧
      witness.Extends nextWitness ∧
      ClosureAllocationsPersistent witness nextWitness ∧
      LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tobject (.word32 resultWord)
        (.object (.tagged (UInt64.ofNat (left.toNat + right.toNat)))) ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨leftPayload, rightPayload, pair⟩ :=
    (ValueRel.bothImmediateNaturalWords_iff related.witnessWellFormed
      leftRelated rightRelated).mp both
  have leftPayloadEq : leftPayload = left := by
    simpa using (ObjectRef.tagged.inj pair.leftReferenceEq).symm
  have rightPayloadEq : rightPayload = right := by
    simpa using (ObjectRef.tagged.inj pair.rightReferenceEq).symm
  subst leftPayload
  subst rightPayload
  have sumTagged : left.toNat + right.toNat ≤ maxTaggedPayload := by
    have leftFits := pair.leftFits
    have rightFits := pair.rightFits
    unfold maxImmediatePayload maxTaggedPayload at *
    omega
  have encoded :
      encodeTagged state (UInt64.ofNat (left.toNat + right.toNat)) =
        .ok (result, resultWord) := by
    unfold allocateNatural at allocated
    rw [if_pos sumTagged] at allocated
    exact allocated
  obtain ⟨nextWitness, extension, closurePersistent, heapRelated,
      valueRelated, capacity⟩ :=
    encodeTagged_liveHeapRel_extends_with_capacity state result witness runtime
      (UInt64.ofNat (left.toNat + right.toNat)) resultWord related encoded
  exact ⟨nextWitness, pair, extension, closurePersistent, heapRelated,
    valueRelated, capacity⟩

/-- The remainder of two immediate natural payloads always fits the wasm32
immediate range. This includes Lean's `n % 0 = n` case. -/
theorem ImmediateNaturalPairRel.mod_fits
    {leftWord rightWord : Word32} {leftReference rightReference : ObjectRef}
    {left right : UInt64}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference left right) :
    left.toNat % right.toNat ≤ maxImmediatePayload := by
  by_cases rightZero : right.toNat = 0
  · simpa [rightZero] using pair.leftFits
  · exact Nat.le_trans
      (Nat.le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero rightZero)))
      pair.rightFits

/-- Exact concrete-runtime model of W7's two-immediate `Nat.mod` branch.
The zero-divisor arm returns the already canonical left word directly. The
nonzero arm calls the existing canonical natural constructor. -/
def immediateNaturalMod (state : MemoryState) (leftWord : Word32)
    (left right : UInt64) : Except ConcreteError (MemoryState × Word32) :=
  if right.toNat = 0 then
    .ok (state, leftWord)
  else
    allocateNatural state (left.toNat % right.toNat)

/-- W7's immediate `Nat.mod` branch implements Lean remainder exactly. Both
the zero-divisor direct return and the nonzero machine-remainder path preserve
the concrete heap and proof witness, return the canonical immediate word, and
have no heap-ownership effects. -/
theorem LiveHeapRel.immediateNaturalMod_refines
    {state result : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {leftWord rightWord resultWord : Word32}
    {left right : UInt64}
    (related : LiveHeapRel state witness runtime)
    (leftRelated : ValueRel witness .tobject (.word32 leftWord)
      (.object (.tagged left)))
    (rightRelated : ValueRel witness .tobject (.word32 rightWord)
      (.object (.tagged right)))
    (both : BothImmediateNaturalWords leftWord rightWord)
    (executed : immediateNaturalMod state leftWord left right =
      .ok (result, resultWord)) :
    ∃ resultFits : left.toNat % right.toNat ≤ maxImmediatePayload,
      ImmediateNaturalPairRel leftWord rightWord (.tagged left) (.tagged right)
          left right ∧
      result = state ∧
      resultWord = Word32.encodeImmediate
        (left.toNat % right.toNat) resultFits ∧
      witness.Extends witness ∧
      ClosureAllocationsPersistent witness witness ∧
      LiveHeapRel result witness runtime ∧
      ValueRel witness .tobject (.word32 resultWord)
        (.object (.tagged (UInt64.ofNat (left.toNat % right.toNat)))) ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨leftPayload, rightPayload, pair⟩ :=
    (ValueRel.bothImmediateNaturalWords_iff related.witnessWellFormed
      leftRelated rightRelated).mp both
  have leftPayloadEq : leftPayload = left := by
    simpa using (ObjectRef.tagged.inj pair.leftReferenceEq).symm
  have rightPayloadEq : rightPayload = right := by
    simpa using (ObjectRef.tagged.inj pair.rightReferenceEq).symm
  subst leftPayload
  subst rightPayload
  have remainderFits := pair.mod_fits
  by_cases rightZero : right.toNat = 0
  · unfold immediateNaturalMod at executed
    rw [if_pos rightZero] at executed
    have pairEq : (state, leftWord) = (result, resultWord) :=
      Except.ok.inj executed
    have stateEq : state = result := congrArg Prod.fst pairEq
    have wordEq : leftWord = resultWord := congrArg Prod.snd pairEq
    subst result
    subst resultWord
    refine ⟨remainderFits, pair, rfl, ?_,
      RefinementWitness.Extends.refl witness,
      ClosureAllocationsPersistent.refl witness, related, ?_,
      MappedHeaderCapacityTransport.refl state witness⟩
    · simpa [rightZero] using pair.leftWordEq
    · simpa [rightZero] using leftRelated
  · have remainderLt : left.toNat % right.toNat < right.toNat :=
      Nat.mod_lt _ (Nat.pos_of_ne_zero rightZero)
    have remainderTagged : left.toNat % right.toNat ≤ maxTaggedPayload := by
      unfold maxImmediatePayload maxTaggedPayload at *
      omega
    have remainderLtUInt64 : left.toNat % right.toNat < UInt64.size := by
      have immediateLtUInt64 : maxImmediatePayload < UInt64.size := by decide
      exact Nat.lt_of_le_of_lt remainderFits immediateLtUInt64
    have remainderToNat :
        (UInt64.ofNat (left.toNat % right.toNat)).toNat =
          left.toNat % right.toNat :=
      UInt64.toNat_ofNat_of_lt' remainderLtUInt64
    have payloadFits :
        (UInt64.ofNat (left.toNat % right.toNat)).toNat ≤
          maxImmediatePayload := by
      simpa [remainderToNat] using remainderFits
    unfold immediateNaturalMod at executed
    rw [if_neg rightZero] at executed
    unfold allocateNatural at executed
    rw [if_pos remainderTagged] at executed
    rw [encodeTagged_immediate state _ payloadFits] at executed
    have pairEq :
        (state, Word32.encodeImmediate
          (UInt64.ofNat (left.toNat % right.toNat)).toNat payloadFits) =
            (result, resultWord) :=
      Except.ok.inj executed
    have stateEq : state = result := congrArg Prod.fst pairEq
    have wordEq : Word32.encodeImmediate
        (UInt64.ofNat (left.toNat % right.toNat)).toNat payloadFits =
          resultWord := congrArg Prod.snd pairEq
    subst result
    subst resultWord
    refine ⟨remainderFits, pair, rfl, ?_,
      RefinementWitness.Extends.refl witness,
      ClosureAllocationsPersistent.refl witness, related,
      encodeTagged_immediate_refines witness
        (UInt64.ofNat (left.toNat % right.toNat)) payloadFits,
      MappedHeaderCapacityTransport.refl state witness⟩
    simp [remainderToNat]

end Fir.Wasm.Concrete
