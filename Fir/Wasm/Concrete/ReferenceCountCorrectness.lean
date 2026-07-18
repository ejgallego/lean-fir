import Fir.Wasm.Concrete.SharingCorrectness
import Fir.Wasm.Concrete.HeaderCorrectness
import Fir.Wasm.Concrete.ConstructorAllocationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Checked recursive ownership treats the zero sentinel as the concrete
representation of a non-owning erased field; unchecked public use still
rejects it as a non-object. -/
theorem decrementReferenceOnceFuel_sentinel
    (fuel : Nat) (state : MemoryState) (object : Word32)
    (sentinel : object.classify = .sentinel) (check : Bool) :
    decrementReferenceOnceFuel fuel state object check =
      if check then .ok state else .error (.source .expectedObject) := by
  cases fuel <;> cases check <;>
    simp [decrementReferenceOnceFuel, sentinel] <;> rfl

/-- Successful concrete recursive release is monotone in fuel: additional
depth never changes the resulting memory state. -/
theorem decrementReferenceOnceFuel_ok_mono
    {fuel more : Nat} {state result : MemoryState} {object : Word32}
    {check : Bool} (fuelLe : fuel ≤ more)
    (operation : decrementReferenceOnceFuel fuel state object check = .ok result) :
    decrementReferenceOnceFuel more state object check = .ok result := by
  induction fuel generalizing more state result object check with
  | zero =>
      cases more with
      | zero => exact operation
      | succ more =>
          cases classEq : object.classify with
          | heap =>
              cases headerEq : state.readLiveHeader object with
              | error failure =>
                  simp [decrementReferenceOnceFuel, classEq, headerEq, liftMemory,
                    Bind.bind, Except.bind] at operation
              | ok header =>
                  by_cases promoted : header.isPromotedTag = true
                  · simpa [decrementReferenceOnceFuel, classEq, headerEq, liftMemory,
                      Bind.bind, Except.bind, promoted] using operation
                  · simp [decrementReferenceOnceFuel, classEq, headerEq, liftMemory,
                      Bind.bind, Except.bind, promoted] at operation
          | sentinel | immediate | invalid =>
              simpa [decrementReferenceOnceFuel, classEq] using operation
  | succ fuel ih =>
      cases more with
      | zero => omega
      | succ more =>
          have smaller : fuel ≤ more := by omega
          cases classEq : object.classify with
          | sentinel | immediate | invalid =>
              simpa [decrementReferenceOnceFuel, classEq] using operation
          | heap =>
              cases headerEq : state.readLiveHeader object with
              | error failure =>
                  simp [decrementReferenceOnceFuel, classEq, headerEq, liftMemory,
                    Bind.bind, Except.bind] at operation
              | ok header =>
                  by_cases promoted : header.isPromotedTag = true
                  · simpa [decrementReferenceOnceFuel, classEq, headerEq, liftMemory,
                      Bind.bind, Except.bind, promoted] using operation
                  · by_cases persistent : header.persistent = true
                    · simpa [decrementReferenceOnceFuel, classEq, headerEq, liftMemory,
                        Bind.bind, Except.bind, promoted, persistent] using operation
                    · by_cases zero : (header.refCount == 0) = true
                      · simp [decrementReferenceOnceFuel, classEq, headerEq, liftMemory,
                          Bind.bind, Except.bind, promoted, persistent, zero] at operation
                      · by_cases above : 1 < header.refCount.toNat
                        · simpa [decrementReferenceOnceFuel, classEq, headerEq, liftMemory,
                            Bind.bind, Except.bind, promoted, persistent, zero, above]
                            using operation
                        · cases ownedEq : readOwnedReferences state object header with
                          | error failure =>
                              simp [decrementReferenceOnceFuel, classEq, headerEq,
                                liftMemory, Bind.bind, Except.bind, promoted, persistent, zero,
                                above, ownedEq] at operation
                          | ok owned =>
                              cases releasedEq : writeLiveHeader state object
                                  header.forRelease with
                              | error failure =>
                                  simp [decrementReferenceOnceFuel, classEq, headerEq,
                                    liftMemory, Bind.bind, Except.bind, promoted, persistent,
                                    zero, above, ownedEq, releasedEq] at operation
                              | ok released =>
                                  have foldMono : ∀ (children : List Word32)
                                      (before after : MemoryState),
                                      children.foldlM (init := before) (fun next child =>
                                        decrementReferenceOnceFuel fuel next child true) =
                                          .ok after →
                                      children.foldlM (init := before) (fun next child =>
                                        decrementReferenceOnceFuel more next child true) =
                                          .ok after := by
                                    intro children
                                    induction children with
                                    | nil =>
                                        intro before after folded
                                        simpa using folded
                                    | cons child children tailIH =>
                                        intro before after folded
                                        simp only [List.foldlM_cons, Bind.bind, Except.bind]
                                          at folded ⊢
                                        cases childEq : decrementReferenceOnceFuel fuel
                                            before child true with
                                        | error failure =>
                                            rw [childEq] at folded
                                            contradiction
                                        | ok middle =>
                                            rw [childEq] at folded
                                            have childMore := ih smaller childEq
                                            rw [childMore]
                                            exact tailIH middle after folded
                                  have folded : owned.foldlM (init := released) (fun next child =>
                                      decrementReferenceOnceFuel fuel next child true) =
                                      .ok result := by
                                    simpa [decrementReferenceOnceFuel, classEq, headerEq,
                                      liftMemory, Bind.bind, Except.bind, promoted, persistent,
                                      zero, above, ownedEq, releasedEq] using operation
                                  have foldedMore := foldMono owned released result folded
                                  simpa [decrementReferenceOnceFuel, classEq, headerEq,
                                    liftMemory, Bind.bind, Except.bind, promoted, persistent,
                                    zero, above, ownedEq, releasedEq] using foldedMore

/-- Type-erased ownership relation for one concrete constructor word. The ABI
kind remains available to rule out scalar representations during recursive
release. -/
inductive OwnershipValueRel (witness : RefinementWitness) (word : Word32)
    (value : Value) : Prop where
  | intro (kind : AbiKind) (admissible : kind.isObjectField = true)
      (related : ValueRel witness kind (.word32 word) value) :
      OwnershipValueRel witness word value

/-- Ordered correspondence between the concrete child words visited by
recursive release and the semantic constructor values visited in the same
left-to-right order. -/
inductive OwnershipValuesRel (witness : RefinementWitness) :
    List Word32 → List Value → Prop where
  | nil : OwnershipValuesRel witness [] []
  | cons (head : OwnershipValueRel witness word value)
      (tail : OwnershipValuesRel witness words values) :
      OwnershipValuesRel witness (word :: words) (value :: values)

private theorem readOwnershipOfFn
    {witness : RefinementWitness} {n : Nat}
    (read : Fin n → Except ConcreteError Word32)
    (semantic : Fin n → Value)
    (each : ∀ index, ∃ word,
      read index = .ok word ∧ OwnershipValueRel witness word (semantic index)) :
    ∃ words,
      List.ofFnM read = .ok words ∧
      OwnershipValuesRel witness words (List.ofFn semantic) := by
  induction n with
  | zero =>
      refine ⟨[], ?_, .nil⟩
      rw [List.ofFnM_zero]
      rfl
  | succ n ih =>
      obtain ⟨word, headRead, headRelated⟩ := each 0
      have tailEach : ∀ index : Fin n, ∃ word,
          read index.succ = .ok word ∧
            OwnershipValueRel witness word (semantic index.succ) := by
        intro index
        exact each index.succ
      obtain ⟨words, tailRead, tailRelated⟩ :=
        ih (fun index => read index.succ) (fun index => semantic index.succ) tailEach
      refine ⟨word :: words, ?_, ?_⟩
      · rw [List.ofFnM_succ, headRead, tailRead]
        rfl
      · rw [List.ofFn_succ]
        exact .cons headRelated tailRelated

/-- A constructor's concrete ownership decoder returns exactly one
ABI-admissible word for each semantic object field, in semantic fold order. -/
theorem ConstructorObjectRel.readOwnedReferences
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject} {header : Header}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (headerRead : state.readLiveHeader address = .ok header) :
    ∃ words,
      Fir.Wasm.Concrete.readOwnedReferences state address header = .ok words ∧
      OwnershipValuesRel witness words semantic.objectFields.toList := by
  obtain ⟨actualHeader, actualRead, headerKind, _, _, _, objectCount, _, _⟩ :=
    related.header
  rw [headerRead] at actualRead
  have headerEq := Except.ok.inj actualRead
  subst actualHeader
  have semanticLt (index : Fin info.size) :
      index.val < semantic.objectFields.size := by
    rw [related.semanticObjectFields]
    exact index.isLt
  let semanticAt : Fin info.size → Value := fun index =>
    semantic.objectFields[index.val]'(semanticLt index)
  have each : ∀ index : Fin info.size, ∃ word,
      readObjectField state address index.val = .ok word ∧
      OwnershipValueRel witness word (semanticAt index) := by
    intro index
    obtain ⟨kind, kindAt, admissible⟩ := related.fieldKind index.isLt
    have valueAt : semantic.objectFields[index.val]? = some (semanticAt index) := by
      unfold semanticAt
      exact Array.getElem?_eq_getElem (semanticLt index)
    obtain ⟨word, wordRead, valueRelated⟩ :=
      related.objectFields index.val kind (semanticAt index) kindAt valueAt
    exact ⟨word, wordRead, .intro kind admissible valueRelated⟩
  obtain ⟨words, wordsRead, wordsRelated⟩ :=
    readOwnershipOfFn (read := fun index : Fin info.size =>
      readObjectField state address index.val) semanticAt each
  have semanticList : List.ofFn semanticAt = semantic.objectFields.toList := by
    apply List.ext_getElem?
    intro index
    simp only [List.getElem?_ofFn, Array.getElem?_toList]
    by_cases indexLt : index < info.size
    · have fieldLt : index < semantic.objectFields.size := by
        rw [related.semanticObjectFields]
        exact indexLt
      simp [indexLt, fieldLt, semanticAt]
    · have fieldNotLt : ¬index < semantic.objectFields.size := by
        rw [related.semanticObjectFields]
        exact indexLt
      simp [indexLt, fieldNotLt]
  unfold Fir.Wasm.Concrete.readOwnedReferences
  rw [headerKind, objectCount]
  rw [semanticList] at wordsRelated
  exact ⟨words, wordsRead, wordsRelated⟩

/-- Exact semantic-heap frame produced by replacing the first cell at one
location. The target lookup changes and every other lookup is preserved. -/
structure HeapReplacePost (before after : Heap) (location : Location)
    (replacement : HeapCell) : Prop where
  replaced : replaceCell before location replacement = some after
  target : findCell? after location = some replacement
  frame : ∀ other, other ≠ location →
    findCell? after other = findCell? before other
  length : after.length = before.length

theorem replaceCell_spec_of_find
    (heap : Heap) (location : Location) (current replacement : HeapCell)
    (found : findCell? heap location = some current) :
    ∃ after, HeapReplacePost heap after location replacement := by
  induction heap with
  | nil => simp [findCell?] at found
  | cons entry rest ih =>
      obtain ⟨candidate, cell⟩ := entry
      by_cases here : candidate = location
      · subst candidate
        refine ⟨(location, replacement) :: rest, ?_, ?_, ?_, rfl⟩
        · simp [replaceCell]
        · simp [findCell?]
        · intro other different
          simp [findCell?, Ne.symm different]
      · have tailFound : findCell? rest location = some current := by
          simpa [findCell?, here] using found
        obtain ⟨after, post⟩ := ih tailFound
        refine ⟨(candidate, cell) :: after, ?_, ?_, ?_, ?_⟩
        · simp [replaceCell, here, post.replaced]
        · simp [findCell?, here, post.target]
        · intro other different
          by_cases atHead : candidate = other
          · subst candidate
            simp [findCell?]
          · simp [findCell?, atHead, post.frame other different]
        · simp [post.length]

/-- `setCell` succeeds whenever its source lookup succeeded and exposes the
same target/other-location frame at the `RuntimeState` boundary. -/
theorem setCell_spec_of_find
    (runtime : RuntimeState) (location : Location) (current replacement : HeapCell)
    (found : findCell? runtime.heap location = some current) :
    ∃ result,
      setCell runtime location replacement = .ok result ∧
      findCell? result.heap location = some replacement ∧
      (∀ other, other ≠ location →
        findCell? result.heap other = findCell? runtime.heap other) ∧
      result.heap.length = runtime.heap.length ∧
      result.nextLocation = runtime.nextLocation := by
  obtain ⟨after, post⟩ := replaceCell_spec_of_find runtime.heap location current
    replacement found
  refine ⟨{ runtime with heap := after }, ?_, post.target, post.frame,
    post.length, rfl⟩
  unfold setCell
  rw [post.replaced]

/-- Assemble a whole-heap postcondition from one semantic `setCell` step, one
new target-cell relation, and concrete frame proofs for every non-target
allocation. This lemma contains no ownership policy; increment, decrement,
and release instantiate the same global bookkeeping boundary. -/
theorem LiveHeapRel.setCell_of_frames
    {state result : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell replacement : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (cursor : result.heapCursor = state.heapCursor)
    (frontier : result.FrontierInvariant)
    (targetRelated : CellRel result witness address replacement)
    (descriptorRegion : ∀ other descriptor,
      witness.descriptors.lookup? other = some descriptor →
      ∃ header,
        Header.read result.memory other = .ok header ∧
        headerBytes ≤ header.allocationBytes.toNat ∧
        header.allocationBytes.toNat % target.heapAlignment = 0 ∧
        other.value + header.allocationBytes.toNat ≤ result.heapCursor)
    (descriptorDisjoint : ∀ left right leftDescriptor rightDescriptor,
      witness.descriptors.lookup? left = some leftDescriptor →
      witness.descriptors.lookup? right = some rightDescriptor →
      left.value ≠ right.value →
      ∀ leftHeader rightHeader,
        Header.read result.memory left = .ok leftHeader →
        Header.read result.memory right = .ok rightHeader →
        left.value + leftHeader.allocationBytes.toNat ≤ right.value ∨
          right.value + rightHeader.allocationBytes.toNat ≤ left.value)
    (cellFrame : ∀ other otherAddress otherCell,
      other ≠ location →
      findCell? runtime.heap other = some otherCell →
      witness.locations.lookup? other = some otherAddress →
      CellRel state witness otherAddress otherCell →
      CellRel result witness otherAddress otherCell)
    (promotedFrame : ∀ payload other,
      witness.promotedTags.Contains payload other →
      PromotedTagRel result witness payload other) :
    ∃ nextRuntime,
      setCell runtime location replacement = .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨nextRuntime, updated, targetFound, otherFound, heapLength, nextLocation⟩ :=
    setCell_spec_of_find runtime location cell replacement found
  refine ⟨nextRuntime, updated, ?_⟩
  refine {
    frontier
    witnessWellFormed := related.witnessWellFormed
    locationsBeforeNext := ?_
    releaseFuelBound := by
      rw [heapLength, cursor]
      exact related.releaseFuelBound
    descriptorsOwned := ?_
    descriptorRegion
    descriptorDisjoint
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := promotedFrame }
  · intro other otherCell foundAfter
    by_cases isTarget : other = location
    · subst other
      rw [targetFound] at foundAfter
      have cellEq := Option.some.inj foundAfter
      subst otherCell
      rw [nextLocation]
      exact related.locationsBeforeNext location cell found
    · have foundBefore : findCell? runtime.heap other = some otherCell := by
        rw [← otherFound other isTarget]
        exact foundAfter
      rw [nextLocation]
      exact related.locationsBeforeNext other otherCell foundBefore
  · intro other descriptor descriptorFound
    obtain ⟨header, _, minimum, _, extent⟩ :=
      descriptorRegion other descriptor descriptorFound
    omega
  · intro other otherCell foundAfter
    by_cases isTarget : other = location
    · subst other
      rw [targetFound] at foundAfter
      have cellEq := Option.some.inj foundAfter
      subst otherCell
      exact ⟨address, mapped, targetRelated⟩
    · have foundBefore : findCell? runtime.heap other = some otherCell := by
        rw [← otherFound other isTarget]
        exact foundAfter
      obtain ⟨otherAddress, otherMapped, otherRelated⟩ :=
        related.semanticToConcrete other otherCell foundBefore
      exact ⟨otherAddress, otherMapped,
        cellFrame other otherAddress otherCell isTarget foundBefore otherMapped
          otherRelated⟩
  · intro other otherAddress otherMapped
    by_cases isTarget : other = location
    · subst other
      have addressEq := Option.some.inj (mapped.symm.trans otherMapped)
      subst otherAddress
      exact ⟨replacement, targetFound, targetRelated⟩
    · obtain ⟨otherCell, foundBefore, otherRelated⟩ :=
        related.concreteToSemantic other otherAddress otherMapped
      exact ⟨otherCell, by
          rw [otherFound other isTarget]
          exact foundBefore,
        cellFrame other otherAddress otherCell isTarget foundBefore otherMapped
          otherRelated⟩

/-- Ownership checks see both physical encodings of a semantic tagged value
as tagged: checked increments are no-ops and unchecked increments fail with
the source `expectedHeapReference` fault. -/
theorem LiveHeapRel.incrementReference_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload)
    (amount : Nat) (check : Bool) :
    incrementReference state word amount check =
      if check then .ok state else .error (.source .expectedHeapReference) := by
  cases tagged with
  | immediate actualPayload fits =>
      unfold incrementReference
      simp [Word32.classify_encodeImmediate]
      cases check <;> rfl
  | promoted found =>
      have promoted := related.promoted payload word found
      obtain ⟨header, headerRead, headerKind, persistent, _, marker, _, _⟩ :=
        promoted.header
      have addressHeap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state word header
          headerRead).1
      have isPromoted : header.isPromotedTag = true := by
        unfold Header.isPromotedTag
        rw [headerKind, persistent, marker]
        decide
      unfold incrementReference
      rw [addressHeap]
      simp only
      rw [headerRead]
      simp only [Bind.bind, Except.bind, liftMemory]
      rw [if_pos isPromoted]
      cases check <;> rfl

/-- Checked tagged decrements are independent of heap-recursion fuel for both
the immediate and promoted physical encodings. -/
theorem LiveHeapRel.decrementReferenceOnceFuel_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload)
    (fuel : Nat) (check : Bool) :
    decrementReferenceOnceFuel fuel state word check =
      if check then .ok state else .error (.source .expectedHeapReference) := by
  cases tagged with
  | immediate actualPayload fits =>
      cases fuel <;>
        simp [decrementReferenceOnceFuel, Word32.classify_encodeImmediate] <;>
        cases check <;> rfl
  | promoted found =>
      have promoted := related.promoted payload word found
      obtain ⟨header, headerRead, headerKind, persistent, _, marker, _, _⟩ :=
        promoted.header
      have addressHeap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state word header
          headerRead).1
      have isPromoted : header.isPromotedTag = true := by
        unfold Header.isPromotedTag
        rw [headerKind, persistent, marker]
        decide
      cases fuel <;>
        simp only [decrementReferenceOnceFuel] <;>
        rw [addressHeap] <;>
        simp only <;>
        rw [headerRead] <;>
        simp only [Bind.bind, Except.bind, liftMemory] <;>
        rw [if_pos isPromoted] <;>
        cases check <;> rfl

/-- Checked decrements retain the same tagged-value split as increments. -/
theorem LiveHeapRel.decrementReferenceOnce_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload)
    (check : Bool) :
    decrementReferenceOnce state word check =
      if check then .ok state else .error (.source .expectedHeapReference) := by
  unfold decrementReferenceOnce
  exact related.decrementReferenceOnceFuel_tagged tagged _ check

/-- One ABI-admissible ownership slot is either the exact concrete address of
a semantic heap child, or a checked concrete no-op matching the semantic
ownership fold's non-heap branch. -/
theorem OwnershipValueRel.releaseStep
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {word : Word32} {value : Value}
    (heap : LiveHeapRel state witness runtime)
    (ownership : OwnershipValueRel witness word value) (fuel : Nat) :
    (∃ location,
      value = .object (.heap location) ∧
      witness.locations.lookup? location = some word) ∨
    ((∀ location, value ≠ .object (.heap location)) ∧
      decrementReferenceOnceFuel fuel state word true = .ok state) := by
  cases ownership with
  | intro kind admissible valueRelated =>
      cases valueRelated with
      | object heapRelated =>
          cases heapRelated with
          | mapped found => exact .inl ⟨_, rfl, found⟩
      | tagged taggedRelated =>
          exact .inr ⟨by intro location; simp,
            by simpa using heap.decrementReferenceOnceFuel_tagged taggedRelated fuel true⟩
      | tobject objectRelated =>
          cases objectRelated with
          | heap heapRelated =>
              cases heapRelated with
              | mapped found => exact .inl ⟨_, rfl, found⟩
          | tagged taggedRelated =>
              exact .inr ⟨by intro location; simp,
                by simpa using
                  heap.decrementReferenceOnceFuel_tagged taggedRelated fuel true⟩
      | erased =>
          exact .inr ⟨by intro location; simp,
            decrementReferenceOnceFuel_sentinel fuel state Word32.zero (by rfl) true⟩
      | reuseNone | reuseSome | uint8 | uint16 | uint32 =>
          simp [AbiKind.isObjectField] at admissible

/-- Ordered ownership-slot correspondence lifts any correct recursive heap
step through the complete concrete/semantic child folds. -/
theorem OwnershipValuesRel.foldlM_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime finalRuntime : RuntimeState}
    {words : List Word32} {values : List Value} {fuel : Nat}
    (related : OwnershipValuesRel witness words values)
    (heap : LiveHeapRel state witness runtime)
    (recurse : ∀ {before : MemoryState} {semantic nextSemantic : RuntimeState}
        {location : Location} {address : Word32},
      LiveHeapRel before witness semantic →
      witness.locations.lookup? location = some address →
      Fir.LeanIR.Impure.decLocationFuel fuel semantic location = .ok nextSemantic →
      ∃ after,
        decrementReferenceOnceFuel fuel before address true = .ok after ∧
        LiveHeapRel after witness nextSemantic)
    (semanticOperation :
      values.foldlM (init := runtime) (fun next value =>
        match value with
        | .object (.heap child) =>
            Fir.LeanIR.Impure.decLocationFuel fuel next child
        | _ => .ok next) = .ok finalRuntime) :
    ∃ finalState,
      words.foldlM (init := state) (fun next child =>
        decrementReferenceOnceFuel fuel next child true) = .ok finalState ∧
      LiveHeapRel finalState witness finalRuntime := by
  induction related generalizing state runtime finalRuntime with
  | nil =>
      simp only [List.foldlM_nil] at semanticOperation ⊢
      have runtimeEq := Except.ok.inj semanticOperation
      subst finalRuntime
      exact ⟨state, rfl, heap⟩
  | @cons word value words values head tail ih =>
      have noOpCase
          (concreteHead : decrementReferenceOnceFuel fuel state word true = .ok state)
          (semanticHead :
            (match value with
            | .object (.heap child) =>
                Fir.LeanIR.Impure.decLocationFuel fuel runtime child
            | _ => .ok runtime) = .ok runtime) :
          ∃ finalState,
            (word :: words).foldlM (init := state) (fun next child =>
              decrementReferenceOnceFuel fuel next child true) = .ok finalState ∧
            LiveHeapRel finalState witness finalRuntime := by
        simp only [List.foldlM_cons, Bind.bind, Except.bind] at semanticOperation
        rw [semanticHead] at semanticOperation
        obtain ⟨finalState, concreteTail, finalHeap⟩ :=
          ih heap semanticOperation
        refine ⟨finalState, ?_, finalHeap⟩
        simp only [List.foldlM_cons, Bind.bind, Except.bind]
        rw [concreteHead]
        exact concreteTail
      rcases head.releaseStep heap fuel with heapStep | noOpStep
      · obtain ⟨location, valueEq, mapped⟩ := heapStep
        subst value
        simp only [List.foldlM_cons, Bind.bind, Except.bind] at semanticOperation
        cases childEq : Fir.LeanIR.Impure.decLocationFuel fuel runtime location with
        | error fault =>
            rw [childEq] at semanticOperation
            contradiction
        | ok nextRuntime =>
            rw [childEq] at semanticOperation
            obtain ⟨nextState, concreteHead, nextHeap⟩ :=
              recurse heap mapped childEq
            obtain ⟨finalState, concreteTail, finalHeap⟩ :=
              ih nextHeap semanticOperation
            refine ⟨finalState, ?_, finalHeap⟩
            simp only [List.foldlM_cons, Bind.bind, Except.bind]
            rw [concreteHead]
            exact concreteTail
      · obtain ⟨notHeap, concreteHead⟩ := noOpStep
        apply noOpCase concreteHead
        cases value with
        | object reference =>
            cases reference with
            | heap location => exact False.elim (notHeap location rfl)
            | tagged payload => rfl
        | usize usize => rfl
        | scalar scalar => rfl
        | erased => rfl
        | reuseToken location => rfl

/-- Shared header-level postcondition for ordinary successful increments. It
separates the common-header write from object-kind-specific payload framing. -/
theorem incrementReference_header
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (notPromoted : header.isPromotedTag = false)
    (ordinary : header.persistent = false)
    (oldCount amount : Nat)
    (refCount : header.refCount.toNat = oldCount)
    (fits : oldCount + amount < UInt32.size)
    (check : Bool) :
    ∃ result updatedHeader memory,
      incrementReference state address amount check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount + amount) } ∧
      result = { state with memory } ∧
      updatedHeader.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  let updatedHeader : Header :=
    { header with refCount := UInt32.ofNat (oldCount + amount) }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : incrementReference state address amount check = .ok result := by
    unfold incrementReference
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [ordinary])]
    rw [refCount]
    rw [uint32Field_eq_ok "reference count" (oldCount + amount) fits]
    unfold writeLiveHeader
    change (do
      let nextMemory ← liftMemory (updatedHeader.write state.memory address)
      return ({ state with memory := nextMemory } : MemoryState)) = .ok result
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have finalValid : result.FrontierInvariant :=
    valid.writeHeader headerOwned headerWrite
  exact ⟨result, updatedHeader, memory, operation, rfl, rfl, headerWrite,
    finalValid, headerReadAfter⟩

/-- Object-independent count replacement at the common-header boundary. It
exposes the exact header write so each payload decoder can prove its own frame
once and share that proof between increment and decrement. -/
theorem writeReferenceCount_header
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (nextCount : UInt32) :
    ∃ result updatedHeader memory,
      writeLiveHeader state address updatedHeader = .ok result ∧
      updatedHeader = { header with refCount := nextCount } ∧
      result = { state with memory } ∧
      updatedHeader.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  let updatedHeader : Header := { header with refCount := nextCount }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : writeLiveHeader state address updatedHeader = .ok result := by
    unfold writeLiveHeader
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have finalValid : result.FrontierInvariant :=
    valid.writeHeader headerOwned headerWrite
  exact ⟨result, updatedHeader, memory, operation, rfl, rfl, headerWrite,
    finalValid, headerReadAfter⟩

/-- Canonicalize one validated live header as a released allocation while
preserving the frontier and the checked allocation extent. -/
theorem releaseHeader
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor) :
    ∃ result memory,
      writeLiveHeader state address header.forRelease = .ok result ∧
      result = { state with memory } ∧
      header.forRelease.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      DeadCellRel result address := by
  obtain ⟨heap, _, _, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address header.forRelease headerInBounds
  let result : MemoryState := { state with memory }
  have operation : writeLiveHeader state address header.forRelease = .ok result := by
    unfold writeLiveHeader
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address header.forRelease
      headerInBounds headerWrite
  have headerReadAfter : Header.read memory address = .ok header.forRelease :=
    Header.read_of_write_eq_ok state.memory memory address header.forRelease
      headerInBounds headerWrite
  have finalValid : result.FrontierInvariant :=
    valid.writeHeader headerOwned headerWrite
  refine ⟨result, memory, operation, rfl, headerWrite, finalValid, ?_⟩
  exact {
    header := ⟨header.forRelease, headerReadAfter, heap,
      by simp [Header.forRelease], by simp [Header.forRelease],
      by simp [Header.forRelease], by simp [Header.forRelease],
      by simp [Header.forRelease], by simp [Header.forRelease],
      by simp [Header.forRelease], by simp [Header.forRelease],
      by simpa [Header.forRelease] using minimum,
      by simpa [Header.forRelease] using aligned,
      by
        change address.value + header.allocationBytes.toNat ≤ memory.size
        rw [memorySize]
        exact extentInMemory⟩
    headerOwned := headerOwned }

/-- The count-one leaf branch is exactly canonical header release: there are
no recursively owned references to visit after the write. -/
theorem decrementReferenceOnce_leaf_one
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (notPromoted : header.isPromotedTag = false)
    (ordinary : header.persistent = false)
    (refCount : header.refCount.toNat = 1)
    (owned : readOwnedReferences state address header = .ok [])
    (check : Bool) :
    ∃ result memory,
      decrementReferenceOnce state address check = .ok result ∧
      result = { state with memory } ∧
      header.forRelease.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      DeadCellRel result address := by
  obtain ⟨result, memory, released, resultEq, headerWrite, finalValid,
      deadRelated⟩ :=
    releaseHeader valid headerRead headerOwned
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead).1
  have refCountNe : header.refCount ≠ 0 := by
    intro zero
    rw [zero] at refCount
    simp at refCount
  have operation : decrementReferenceOnce state address check = .ok result := by
    simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [ordinary])]
    rw [if_neg (by simpa using refCountNe)]
    rw [refCount, if_neg (by omega)]
    rw [owned]
    rw [released]
    rfl
  exact ⟨result, memory, operation, resultEq, headerWrite, finalValid, deadRelated⟩

/-- A common-header rewrite leaves the recursive natural payload decoder
unchanged because every limb starts after the 32-byte header. -/
theorem Header.readNaturalLimbs_of_write_eq_ok
    (before after : LinearMemory) (address : Word32) (updatedHeader : Header)
    (index count : Nat)
    (headerInBounds : address.value + headerBytes ≤ before.size)
    (written : updatedHeader.write before address = .ok after) :
    readNaturalLimbs after address.value index count =
      readNaturalLimbs before address.value index count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      unfold readNaturalLimbs LinearMemory.readUInt64
      rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader
        (address.value + headerBytes + target.semanticSlotBytes * index)
        headerInBounds written (.inr (by omega))]
      rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader
        (address.value + headerBytes + target.semanticSlotBytes * index + 4)
        headerInBounds written (.inr (by omega))]
      rw [ih (index + 1)]

theorem Header.readUInt16_of_write_eq_ok_payload
    (before after : LinearMemory) (address : Word32) (updatedHeader : Header)
    (other : Nat)
    (headerInBounds : address.value + headerBytes ≤ before.size)
    (written : updatedHeader.write before address = .ok after)
    (payload : address.value + headerBytes ≤ other) :
    after.readUInt16 other = before.readUInt16 other := by
  unfold LinearMemory.readUInt16
  rw [Header.readByte_of_write_eq_ok_other before after address updatedHeader other
    headerInBounds written (.inr payload)]
  rw [Header.readByte_of_write_eq_ok_other before after address updatedHeader (other + 1)
    headerInBounds written (.inr (by omega))]

theorem Header.readUInt64_of_write_eq_ok_payload
    (before after : LinearMemory) (address : Word32) (updatedHeader : Header)
    (other : Nat)
    (headerInBounds : address.value + headerBytes ≤ before.size)
    (written : updatedHeader.write before address = .ok after)
    (payload : address.value + headerBytes ≤ other) :
    after.readUInt64 other = before.readUInt64 other := by
  unfold LinearMemory.readUInt64
  rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader other
    headerInBounds written (.inr payload)]
  rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader (other + 4)
    headerInBounds written (.inr (by omega))]

theorem Header.readWord32_of_write_eq_ok_payload
    (before after : LinearMemory) (address : Word32) (updatedHeader : Header)
    (other : Nat)
    (headerInBounds : address.value + headerBytes ≤ before.size)
    (written : updatedHeader.write before address = .ok after)
    (payload : address.value + headerBytes ≤ other) :
    after.readWord32 other = before.readWord32 other := by
  unfold LinearMemory.readWord32
  rw [Header.readUInt32_of_write_eq_ok_other before after address updatedHeader other
    headerInBounds written (.inr payload)]

/-- Rewriting only a constructor's reference count frames every representation
region described by its immutable allocation metadata. -/
theorem ConstructorObjectRel.writeReferenceCount
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject} {header : Header}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (headerRead : state.readLiveHeader address = .ok header)
    (valid : state.FrontierInvariant)
    (nextCount : UInt32) :
    ∃ result updatedHeader,
      writeLiveHeader state address updatedHeader = .ok result ∧
      updatedHeader = { header with refCount := nextCount } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      ConstructorObjectRel result witness address info fieldKinds semantic := by
  obtain ⟨objectHeader, objectHeaderRead, headerKind, allocationBytes, ordinary,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header
  rw [headerRead] at objectHeaderRead
  cases objectHeaderRead
  obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
      headerWrite, finalValid, headerReadAfter⟩ :=
    writeReferenceCount_header valid headerRead related.headerOwned nextCount
  subst updatedHeader
  subst result
  let updatedHeader : Header :=
    { header with refCount := nextCount }
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans related.headerOwned valid.cursorInBounds
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead).1
  have constructorHeaderBefore : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap]
    rw [headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  have constructorHeaderAfter :
      readConstructorHeader ({ state with memory } : MemoryState) address =
        .ok updatedHeader := by
    unfold readConstructorHeader
    simp [heap]
    rw [headerReadAfter]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, updatedHeader, headerKind]
    rfl
  have scalarFieldsAfter : ∀ field, field ∈ semantic.scalarFields →
      match field.value with
      | .uint8 value =>
          field.width = info.size + info.usize ∧
          field.offset + 1 ≤ info.ssize ∧
          readScalarUInt8Field ({ state with memory } : MemoryState) address
            field.width field.offset = .ok value
      | .uint16 value =>
          field.width = info.size + info.usize ∧
          field.offset + 2 ≤ info.ssize ∧
          readScalarUInt16Field ({ state with memory } : MemoryState) address
            field.width field.offset = .ok value
      | .uint32 value =>
          field.width = info.size + info.usize ∧
          field.offset + 4 ≤ info.ssize ∧
          readScalarUInt32Field ({ state with memory } : MemoryState) address
            field.width field.offset = .ok value
      | .uint64 value =>
          field.width = info.size + info.usize ∧
          field.offset + 8 ≤ info.ssize ∧
          readScalarUInt64Field ({ state with memory } : MemoryState) address
            field.width field.offset = .ok value := by
    intro field member
    have beforeField := related.semanticScalarFields field member
    cases valueEq : field.value with
    | uint8 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have operationEq :
            readScalarUInt8Field ({ state with memory } : MemoryState) address
                field.width field.offset =
              readScalarUInt8Field state address field.width field.offset := by
          unfold readScalarUInt8Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddressBefore : scalarFieldAddress address header field.width
              field.offset 1 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          have scalarAddressAfter : scalarFieldAddress address updatedHeader field.width
              field.offset 1 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [updatedHeader, widthEq, objectCount, usizeCount, fieldFits,
              scalarCount]
            rfl
          rw [scalarAddressAfter, scalarAddressBefore]
          change liftMemory (memory.readByte (address.value + headerBytes +
            target.semanticSlotBytes * field.width + field.offset)) =
              liftMemory (state.memory.readByte (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset))
          rw [Header.readByte_of_write_eq_ok_other state.memory memory address
            { header with refCount := nextCount }
            (address.value + headerBytes + target.semanticSlotBytes * field.width +
              field.offset) headerInBounds headerWrite (.inr (by omega))]
        rw [operationEq]
        exact readBefore
    | uint16 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have operationEq :
            readScalarUInt16Field ({ state with memory } : MemoryState) address
                field.width field.offset =
              readScalarUInt16Field state address field.width field.offset := by
          unfold readScalarUInt16Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddressBefore : scalarFieldAddress address header field.width
              field.offset 2 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          have scalarAddressAfter : scalarFieldAddress address updatedHeader field.width
              field.offset 2 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [updatedHeader, widthEq, objectCount, usizeCount, fieldFits,
              scalarCount]
            rfl
          rw [scalarAddressAfter, scalarAddressBefore]
          change liftMemory (memory.readUInt16 (address.value + headerBytes +
            target.semanticSlotBytes * field.width + field.offset)) =
              liftMemory (state.memory.readUInt16 (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset))
          rw [Header.readUInt16_of_write_eq_ok_payload state.memory memory address
            { header with refCount := nextCount }
            (address.value + headerBytes + target.semanticSlotBytes * field.width +
              field.offset) headerInBounds headerWrite (by omega)]
        rw [operationEq]
        exact readBefore
    | uint32 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have operationEq :
            readScalarUInt32Field ({ state with memory } : MemoryState) address
                field.width field.offset =
              readScalarUInt32Field state address field.width field.offset := by
          unfold readScalarUInt32Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddressBefore : scalarFieldAddress address header field.width
              field.offset 4 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          have scalarAddressAfter : scalarFieldAddress address updatedHeader field.width
              field.offset 4 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [updatedHeader, widthEq, objectCount, usizeCount, fieldFits,
              scalarCount]
            rfl
          rw [scalarAddressAfter, scalarAddressBefore]
          change liftMemory (memory.readUInt32 (address.value + headerBytes +
            target.semanticSlotBytes * field.width + field.offset)) =
              liftMemory (state.memory.readUInt32 (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset))
          rw [Header.readUInt32_of_write_eq_ok_other state.memory memory address
            { header with refCount := nextCount }
            (address.value + headerBytes + target.semanticSlotBytes * field.width +
              field.offset) headerInBounds headerWrite (.inr (by omega))]
        rw [operationEq]
        exact readBefore
    | uint64 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have operationEq :
            readScalarUInt64Field ({ state with memory } : MemoryState) address
                field.width field.offset =
              readScalarUInt64Field state address field.width field.offset := by
          unfold readScalarUInt64Field
          rw [constructorHeaderAfter, constructorHeaderBefore]
          simp only [Bind.bind, Except.bind]
          have scalarAddressBefore : scalarFieldAddress address header field.width
              field.offset 8 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [widthEq, objectCount, usizeCount, fieldFits, scalarCount]
            rfl
          have scalarAddressAfter : scalarFieldAddress address updatedHeader field.width
              field.offset 8 = .ok (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset) := by
            unfold scalarFieldAddress
            simp [updatedHeader, widthEq, objectCount, usizeCount, fieldFits,
              scalarCount]
            rfl
          rw [scalarAddressAfter, scalarAddressBefore]
          change liftMemory (memory.readUInt64 (address.value + headerBytes +
            target.semanticSlotBytes * field.width + field.offset)) =
              liftMemory (state.memory.readUInt64 (address.value + headerBytes +
                target.semanticSlotBytes * field.width + field.offset))
          rw [Header.readUInt64_of_write_eq_ok_payload state.memory memory address
            { header with refCount := nextCount }
            (address.value + headerBytes + target.semanticSlotBytes * field.width +
              field.offset) headerInBounds headerWrite (by omega)]
        rw [operationEq]
        exact readBefore
  refine ⟨{ state with memory }, updatedHeader, operation, rfl, finalValid,
    headerReadAfter, ?_⟩
  refine {
    header := ⟨updatedHeader, headerReadAfter,
      by simpa [updatedHeader] using headerKind,
      by simpa [updatedHeader] using allocationBytes,
      by simpa [updatedHeader] using ordinary,
      by simpa [updatedHeader] using tag,
      by simpa [updatedHeader] using objectCount,
      by simpa [updatedHeader] using usizeCount,
      by simpa [updatedHeader] using scalarCount⟩
    headerOwned := related.headerOwned
    extent := by simpa [updatedHeader] using related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := scalarFieldsAfter
    fieldKindsSize := related.fieldKindsSize
    fieldKindsValid := related.fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · intro index kind value kindAt valueAt
    obtain ⟨word, readBefore, valueRelated⟩ :=
      related.objectFields index kind value kindAt valueAt
    have operationEq :
        readObjectField ({ state with memory } : MemoryState) address index =
          readObjectField state address index := by
      unfold readObjectField
      rw [constructorHeaderAfter, constructorHeaderBefore]
      simp only [Bind.bind, Except.bind, updatedHeader]
      rw [Header.readWord32_of_write_eq_ok_payload state.memory memory address
        { header with refCount := nextCount }
        (address.value + headerBytes + target.semanticSlotBytes * index)
        headerInBounds headerWrite (by omega)]
      rw [Header.readUInt32_of_write_eq_ok_other state.memory memory address
        { header with refCount := nextCount }
        (address.value + headerBytes + target.semanticSlotBytes * index + 4)
        headerInBounds headerWrite (.inr (by omega))]
    exact ⟨word, by rw [operationEq]; exact readBefore, valueRelated⟩
  · intro index value valueAt
    have operationEq :
        readUSizeField ({ state with memory } : MemoryState) address index =
          readUSizeField state address index := by
      unfold readUSizeField
      rw [constructorHeaderAfter, constructorHeaderBefore]
      simp only [Bind.bind, Except.bind, updatedHeader]
      rw [Header.readUInt64_of_write_eq_ok_payload state.memory memory address
        { header with refCount := nextCount }
        (address.value + headerBytes + target.semanticSlotBytes *
          (header.aux1.toNat + index)) headerInBounds headerWrite (by omega)]
    rw [operationEq]
    exact related.usizeFields index value valueAt

/-- Constructor increment is the ordinary runtime branch followed by the
shared constructor header-frame theorem. -/
theorem ConstructorObjectRel.incrementReference
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject} {header : Header}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (headerRead : state.readLiveHeader address = .ok header)
    (valid : state.FrontierInvariant)
    (oldCount amount : Nat)
    (refCount : header.refCount.toNat = oldCount)
    (fits : oldCount + amount < UInt32.size)
    (check : Bool) :
    ∃ result updatedHeader,
      Fir.Wasm.Concrete.incrementReference state address amount check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount + amount) } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      ConstructorObjectRel result witness address info fieldKinds semantic := by
  obtain ⟨result, updatedHeader, write, updatedEq, finalValid, headerReadAfter,
      objectAfter⟩ :=
    related.writeReferenceCount headerRead valid
      (UInt32.ofNat (oldCount + amount))
  obtain ⟨objectHeader, objectHeaderRead, headerKind, _, ordinary, _, _, _, _⟩ :=
    related.header
  rw [headerRead] at objectHeaderRead
  cases objectHeaderRead
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead).1
  have notPromoted : header.isPromotedTag = false := by
    have different : (ObjectKind.constructor == ObjectKind.natural) = false := by decide
    simp [Header.isPromotedTag, headerKind, different]
  have operation : Fir.Wasm.Concrete.incrementReference state address amount check =
      .ok result := by
    unfold Fir.Wasm.Concrete.incrementReference
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [ordinary])]
    rw [refCount]
    rw [uint32Field_eq_ok "reference count" (oldCount + amount) fits]
    simpa [updatedEq] using write
  exact ⟨result, updatedHeader, operation, updatedEq, finalValid,
    headerReadAfter, objectAfter⟩

/-- Above one, constructor decrement uses the same payload-frame theorem as
increment while selecting the decrement engine's nonrecursive branch. -/
theorem ConstructorObjectRel.decrementReferenceOnce_above_one
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject} {header : Header}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (headerRead : state.readLiveHeader address = .ok header)
    (valid : state.FrontierInvariant)
    (oldCount : Nat) (refCount : header.refCount.toNat = oldCount)
    (oneLt : 1 < oldCount) (check : Bool) :
    ∃ result updatedHeader,
      decrementReferenceOnce state address check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount - 1) } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      ConstructorObjectRel result witness address info fieldKinds semantic := by
  obtain ⟨result, updatedHeader, write, updatedEq, finalValid, headerReadAfter,
      objectAfter⟩ :=
    related.writeReferenceCount headerRead valid (UInt32.ofNat (oldCount - 1))
  obtain ⟨objectHeader, objectHeaderRead, headerKind, _, ordinary, _, _, _, _⟩ :=
    related.header
  rw [headerRead] at objectHeaderRead
  cases objectHeaderRead
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead).1
  have notPromoted : header.isPromotedTag = false := by
    have different : (ObjectKind.constructor == ObjectKind.natural) = false := by decide
    simp [Header.isPromotedTag, headerKind, different]
  have refCountNe : header.refCount ≠ 0 := by
    intro zero
    rw [zero] at refCount
    simp at refCount
    omega
  have operation : decrementReferenceOnce state address check = .ok result := by
    simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [ordinary])]
    rw [if_neg (by simpa using refCountNe)]
    rw [refCount, if_pos oneLt]
    simpa [updatedEq] using write
  exact ⟨result, updatedHeader, operation, updatedEq, finalValid,
    headerReadAfter, objectAfter⟩

/-- Incrementing one ordinary boxed object's header preserves its canonical
payload decoder while changing exactly the mutable reference count. -/
theorem BoxedObjectRel.incrementReference
    {state : MemoryState} {address : Word32} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {header : Header}
    (related : BoxedObjectRel state address kind scalar header)
    (valid : state.FrontierInvariant)
    (oldCount amount : Nat)
    (refCount : header.refCount.toNat = oldCount)
    (fits : oldCount + amount < UInt32.size)
    (check : Bool) :
    ∃ result updatedHeader,
      Fir.Wasm.Concrete.incrementReference state address amount check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount + amount) } ∧
      result.FrontierInvariant ∧
      BoxedObjectRel result address kind scalar updatedHeader := by
  obtain ⟨heap, decodedBefore, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      related.headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size := by
    omega
  let updatedHeader : Header :=
    { header with refCount := UInt32.ofNat (oldCount + amount) }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have notPromoted : header.isPromotedTag = false := by
    have different : (ObjectKind.boxed == ObjectKind.natural) = false := by decide
    simp [Header.isPromotedTag, related.headerKind, different]
  have operation : Fir.Wasm.Concrete.incrementReference state address amount check =
      .ok result := by
    unfold Fir.Wasm.Concrete.incrementReference
    rw [heap]
    simp only
    rw [related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [related.ordinary])]
    rw [refCount]
    rw [uint32Field_eq_ok "reference count" (oldCount + amount) fits]
    unfold writeLiveHeader
    change (do
      let nextMemory ← liftMemory (updatedHeader.write state.memory address)
      return ({ state with memory := nextMemory } : MemoryState)) = .ok result
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have finalValid : result.FrontierInvariant := by
    exact valid.writeHeader related.headerOwned headerWrite
  have payloadRead : memory.readUInt64 (address.value + headerBytes) =
      state.memory.readUInt64 (address.value + headerBytes) := by
    unfold LinearMemory.readUInt64
    rw [Header.readUInt32_of_write_eq_ok_other state.memory memory address
      updatedHeader (address.value + headerBytes) headerInBounds headerWrite (by omega)]
    rw [Header.readUInt32_of_write_eq_ok_other state.memory memory address
      updatedHeader (address.value + headerBytes + 4) headerInBounds headerWrite
        (by omega)]
  have decoderEq :
      readBoxedScalar result kind address = readBoxedScalar state kind address := by
    unfold readBoxedScalar
    rw [heap]
    simp only
    rw [headerReadAfter, related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    have boxed : (header.kind == ObjectKind.boxed) = true := by
      rw [related.headerKind]
      decide
    have boxedAfter : (updatedHeader.kind == ObjectKind.boxed) = true := by
      simpa [updatedHeader] using boxed
    rw [boxedAfter]
    simp
    unfold readHeapBoxedScalar
    simp only [updatedHeader]
    rw [payloadRead]
  refine ⟨result, updatedHeader, operation, rfl, finalValid, ?_⟩
  exact {
    scalarKind := related.scalarKind
    headerRead := headerReadAfter
    headerKind := by simpa [updatedHeader] using related.headerKind
    ordinary := by simpa [updatedHeader] using related.ordinary
    allocationBytes := by simpa [updatedHeader] using related.allocationBytes
    kindCode := by simpa [updatedHeader] using related.kindCode
    payloadBytes := by simpa [updatedHeader] using related.payloadBytes
    reserved2 := by simpa [updatedHeader] using related.reserved2
    reserved3 := by simpa [updatedHeader] using related.reserved3
    headerOwned := related.headerOwned
    extent := related.extent
    decoded := by rw [decoderEq]; exact related.decoded }

/-- Object-independent common-header count replacement, specialized here to
the canonical boxed payload decoder. -/
theorem BoxedObjectRel.writeReferenceCount
    {state : MemoryState} {address : Word32} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {header : Header}
    (related : BoxedObjectRel state address kind scalar header)
    (valid : state.FrontierInvariant) (nextCount : UInt32) :
    ∃ result updatedHeader,
      writeLiveHeader state address updatedHeader = .ok result ∧
      updatedHeader = { header with refCount := nextCount } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      BoxedObjectRel result address kind scalar updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      related.headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans related.headerOwned valid.cursorInBounds
  let updatedHeader : Header := { header with refCount := nextCount }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : writeLiveHeader state address updatedHeader = .ok result := by
    unfold writeLiveHeader
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decodedHeader : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerReadAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decodedHeader]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  have finalValid : result.FrontierInvariant :=
    valid.writeHeader related.headerOwned headerWrite
  have payloadRead : memory.readUInt64 (address.value + headerBytes) =
      state.memory.readUInt64 (address.value + headerBytes) :=
    Header.readUInt64_of_write_eq_ok_payload state.memory memory address updatedHeader
      (address.value + headerBytes) headerInBounds headerWrite (by omega)
  have decoderEq :
      readBoxedScalar result kind address = readBoxedScalar state kind address := by
    unfold readBoxedScalar
    rw [heap]
    simp only
    rw [headerReadAfter, related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    have boxed : (header.kind == ObjectKind.boxed) = true := by
      rw [related.headerKind]
      decide
    have boxedAfter : (updatedHeader.kind == ObjectKind.boxed) = true := by
      simpa [updatedHeader] using boxed
    rw [boxedAfter]
    simp
    unfold readHeapBoxedScalar
    simp only [updatedHeader]
    rw [payloadRead]
  refine ⟨result, updatedHeader, operation, rfl, finalValid, headerReadAfter, ?_⟩
  exact {
    scalarKind := related.scalarKind
    headerRead := headerReadAfter
    headerKind := by simpa [updatedHeader] using related.headerKind
    ordinary := by simpa [updatedHeader] using related.ordinary
    allocationBytes := by simpa [updatedHeader] using related.allocationBytes
    kindCode := by simpa [updatedHeader] using related.kindCode
    payloadBytes := by simpa [updatedHeader] using related.payloadBytes
    reserved2 := by simpa [updatedHeader] using related.reserved2
    reserved3 := by simpa [updatedHeader] using related.reserved3
    headerOwned := related.headerOwned
    extent := related.extent
    decoded := by rw [decoderEq]; exact related.decoded }

/-- Above one, decrement is precisely a live common-header rewrite. -/
theorem BoxedObjectRel.decrementReferenceOnce_above_one
    {state : MemoryState} {address : Word32} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {header : Header}
    (related : BoxedObjectRel state address kind scalar header)
    (valid : state.FrontierInvariant) (oldCount : Nat)
    (refCount : header.refCount.toNat = oldCount) (oneLt : 1 < oldCount)
    (check : Bool) :
    ∃ result updatedHeader,
      decrementReferenceOnce state address check = .ok result ∧
      updatedHeader = { header with refCount := UInt32.ofNat (oldCount - 1) } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      BoxedObjectRel result address kind scalar updatedHeader := by
  obtain ⟨result, updatedHeader, write, updatedEq, finalValid, headerReadAfter,
      objectAfter⟩ := related.writeReferenceCount valid (UInt32.ofNat (oldCount - 1))
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      related.headerRead).1
  have notPromoted : header.isPromotedTag = false := by
    have different : (ObjectKind.boxed == ObjectKind.natural) = false := by decide
    simp [Header.isPromotedTag, related.headerKind, different]
  have refCountNe : header.refCount ≠ 0 := by
    intro zero
    rw [zero] at refCount
    simp at refCount
    omega
  have operation : decrementReferenceOnce state address check = .ok result := by
    simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
    rw [heap]
    simp only
    rw [related.headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [related.ordinary])]
    rw [if_neg (by simpa using refCountNe)]
    rw [refCount, if_pos oneLt]
    simpa [updatedEq] using write
  exact ⟨result, updatedHeader, operation, updatedEq, finalValid, headerReadAfter,
    objectAfter⟩

/-- First successful decrement refinement: a live box above one remains live,
retains its scalar payload, and lowers the semantic/concrete count together. -/
theorem LiveCellRel.decrementReferenceOnce_boxed_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (boxedCell : ∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
      cell.object = .boxed kind.semanticType scalar.semanticValue)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
      rw [objectEq] at boxedEq
      contradiction
  | @boxed kind scalar header _ descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨result, updatedHeader, operation, updatedEq, finalValid,
          headerReadAfter, objectAfter⟩ :=
        objectRelated.decrementReferenceOnce_above_one valid cell.rc refCount oneLt check
      subst updatedHeader
      have nextFits : cell.rc - 1 < UInt32.size := by
        have oldFits := UInt32.toNat_lt_size header.refCount
        rw [refCount] at oldFits
        omega
      refine ⟨result, operation, finalValid, ?_⟩
      apply LiveCellRel.boxed descriptor (by simpa using objectEq) objectAfter
      · simp only
        exact UInt32.toNat_ofNat_of_lt' nextFits
      · simpa using persistent
      · simpa using live
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
      rw [objectEq] at boxedEq
      contradiction

/-- Local live-cell refinement for the first W6.3 ownership case. -/
theorem LiveCellRel.incrementReference_boxed
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (boxedCell : ∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
      cell.object = .boxed kind.semanticType scalar.semanticValue)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc + amount } := by
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
      rw [objectEq] at boxedEq
      contradiction
  | boxed descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨result, updatedHeader, operation, updatedEq, finalValid,
        objectAfter⟩ := objectRelated.incrementReference valid cell.rc amount
          refCount fits check
      subst updatedHeader
      refine ⟨result, operation, finalValid, ?_⟩
      apply LiveCellRel.boxed descriptor (by simpa using objectEq) objectAfter
      · simp only
        exact UInt32.toNat_ofNat_of_lt' fits
      · simpa using persistent
      · simpa using live
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
      rw [objectEq] at boxedEq
      contradiction

/-- Constructor increments preserve every decoded payload region and update
the enclosing live-cell ownership equality. -/
theorem LiveCellRel.incrementReference_constructor
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (constructorCell : ∃ semantic : ConstructorObject, cell.object = .ctor semantic)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc + amount } := by
  cases related with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
        persistent live =>
      obtain ⟨result, updatedHeader, operation, updatedEq, finalValid,
          headerReadAfter, objectAfter⟩ :=
        objectRelated.incrementReference headerRead valid cell.rc amount refCount fits check
      subst updatedHeader
      refine ⟨result, operation, finalValid, ?_⟩
      apply LiveCellRel.constructor descriptor (by simpa using objectEq) objectAfter
        headerReadAfter
      · simpa using headerKind
      · simp only
        exact UInt32.toNat_ofNat_of_lt' fits
      · simpa using persistent
      · simpa using live
  | boxed _ objectEq _ _ _ _ =>
      obtain ⟨semantic, constructorEq⟩ := constructorCell
      rw [objectEq] at constructorEq
      contradiction
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨semantic, constructorEq⟩ := constructorCell
      rw [objectEq] at constructorEq
      contradiction

/-- Constructor cells above one remain live and preserve every decoded field
while source and concrete ownership counts both decrease by one. -/
theorem LiveCellRel.decrementReferenceOnce_constructor_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (constructorCell : ∃ semantic : ConstructorObject, cell.object = .ctor semantic)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  cases related with
  | @constructor info fieldKinds semantic header _ descriptor objectEq objectRelated
        headerRead headerKind refCount persistent live =>
      obtain ⟨result, updatedHeader, operation, updatedEq, finalValid,
          headerReadAfter, objectAfter⟩ :=
        objectRelated.decrementReferenceOnce_above_one headerRead valid cell.rc refCount
          oneLt check
      subst updatedHeader
      have nextFits : cell.rc - 1 < UInt32.size := by
        have oldFits := UInt32.toNat_lt_size header.refCount
        rw [refCount] at oldFits
        omega
      refine ⟨result, operation, finalValid, ?_⟩
      apply LiveCellRel.constructor descriptor (by simpa using objectEq) objectAfter
        headerReadAfter
      · simpa using headerKind
      · simp only
        exact UInt32.toNat_ofNat_of_lt' nextFits
      · simpa using persistent
      · simpa using live
  | boxed _ objectEq _ _ _ _ =>
      obtain ⟨semantic, constructorEq⟩ := constructorCell
      rw [objectEq] at constructorEq
      contradiction
  | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨semantic, constructorEq⟩ := constructorCell
      rw [objectEq] at constructorEq
      contradiction

/-- Natural limbs frame across a common-header increment, yielding the same
decoded semantic natural at the incremented live-cell count. -/
theorem LiveCellRel.incrementReference_natural
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (naturalCell : ∃ value : Nat, cell.object = .natural value)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc + amount } := by
  have headerOwned := related.headerOwned
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      obtain ⟨value, naturalEq⟩ := naturalCell
      rw [objectEq] at naturalEq
      contradiction
  | boxed _ objectEq _ _ _ _ =>
      obtain ⟨value, naturalEq⟩ := naturalCell
      rw [objectEq] at naturalEq
      contradiction
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      have notPromoted : Header.isPromotedTag header = false := by
        simp [Header.isPromotedTag, headerKind, ordinary]
      obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
          headerWrite, finalValid, headerReadAfter⟩ :=
        incrementReference_header valid headerRead headerOwned notPromoted ordinary
          cell.rc amount refCount fits check
      subst updatedHeader
      subst result
      have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
        Nat.le_trans headerOwned valid.cursorInBounds
      have decoderEq :
          readNatural ({ state with memory } : MemoryState) address =
            readNatural state address := by
        obtain ⟨heap, _, _, _, _, _⟩ :=
          MemoryState.PrefixExtension.readLiveHeader_facts state address _ headerRead
        unfold readNatural
        rw [heap]
        simp only
        rw [headerReadAfter, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        simp [headerKind, ordinary, marker]
        rw [Header.readNaturalLimbs_of_write_eq_ok state.memory memory address
          { header with refCount := UInt32.ofNat (cell.rc + amount) }
          0 _ headerInBounds headerWrite]
      refine ⟨{ state with memory }, operation, finalValid, ?_⟩
      apply LiveCellRel.natural descriptor (by simpa using objectEq) headerReadAfter
      · simpa using headerKind
      · simpa using ordinary
      · simpa using marker
      · simpa using extent
      · simpa using limbsFit
      · rw [decoderEq]
        exact decoded
      · simp only
        exact UInt32.toNat_ofNat_of_lt' fits
      · simpa using persistent
      · simpa using live

/-- Natural cells above one retain their complete limb decoder while the
common header and semantic cell counts decrease together. -/
theorem LiveCellRel.decrementReferenceOnce_natural_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (naturalCell : ∃ value : Nat, cell.object = .natural value)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  have headerOwned := related.headerOwned
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      obtain ⟨value, naturalEq⟩ := naturalCell
      rw [objectEq] at naturalEq
      contradiction
  | boxed _ objectEq _ _ _ _ =>
      obtain ⟨value, naturalEq⟩ := naturalCell
      rw [objectEq] at naturalEq
      contradiction
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      have notPromoted : Header.isPromotedTag header = false := by
        simp [Header.isPromotedTag, headerKind, ordinary]
      obtain ⟨result, updatedHeader, memory, write, updatedEq, resultEq,
          headerWrite, finalValid, headerReadAfter⟩ :=
        writeReferenceCount_header valid headerRead headerOwned
          (UInt32.ofNat (cell.rc - 1))
      subst updatedHeader
      subst result
      obtain ⟨heap, _, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
      have refCountNe : header.refCount ≠ 0 := by
        intro zero
        rw [zero] at refCount
        simp at refCount
        omega
      have operation :
          decrementReferenceOnce state address check = .ok { state with memory } := by
        simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
        rw [heap]
        simp only
        rw [headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        rw [if_neg (by simp [notPromoted])]
        rw [if_neg (by simp [ordinary])]
        rw [if_neg (by simpa using refCountNe)]
        rw [refCount, if_pos oneLt]
        exact write
      have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
        Nat.le_trans headerOwned valid.cursorInBounds
      have decoderEq :
          readNatural ({ state with memory } : MemoryState) address =
            readNatural state address := by
        unfold readNatural
        rw [heap]
        simp only
        rw [headerReadAfter, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        simp [headerKind, ordinary, marker]
        rw [Header.readNaturalLimbs_of_write_eq_ok state.memory memory address
          { header with refCount := UInt32.ofNat (cell.rc - 1) }
          0 _ headerInBounds headerWrite]
      have nextFits : cell.rc - 1 < UInt32.size := by
        have oldFits := UInt32.toNat_lt_size header.refCount
        rw [refCount] at oldFits
        omega
      refine ⟨{ state with memory }, operation, finalValid, ?_⟩
      apply LiveCellRel.natural descriptor (by simpa using objectEq) headerReadAfter
      · simpa using headerKind
      · simpa using ordinary
      · simpa using marker
      · simpa using extent
      · simpa using limbsFit
      · rw [decoderEq]
        exact decoded
      · simp only
        exact UInt32.toNat_ofNat_of_lt' nextFits
      · simpa using persistent
      · simpa using live

/-- Boxes and heap naturals own no concrete child references. At count one,
both representations therefore transition directly to `DeadCellRel`. -/
theorem LiveCellRel.decrementReferenceOnce_leaf_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (valid : state.FrontierInvariant) (one : cell.rc = 1) (check : Bool) :
    ∃ result header memory,
      decrementReferenceOnce state address check = .ok result ∧
      state.readLiveHeader address = .ok header ∧
      result = { state with memory } ∧
      header.forRelease.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      DeadCellRel result address := by
  cases related with
  | constructor _ objectEq _ _ _ _ _ _ =>
      rcases leafCell with boxedCell | naturalCell
      · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
      · obtain ⟨value, naturalEq⟩ := naturalCell
        rw [objectEq] at naturalEq
        contradiction
  | @boxed kind scalar header _ descriptor objectEq objectRelated refCount persistent live =>
      have notPromoted : header.isPromotedTag = false := by
        have different : (ObjectKind.boxed == ObjectKind.natural) = false := by decide
        simp [Header.isPromotedTag, objectRelated.headerKind, different]
      have countOne : header.refCount.toNat = 1 := by
        rw [refCount, one]
      have owned : readOwnedReferences state address header = .ok [] := by
        simp [readOwnedReferences, objectRelated.headerKind]
      obtain ⟨result, memory, operation, resultEq, headerWrite, finalValid,
          deadRelated⟩ :=
        Fir.Wasm.Concrete.decrementReferenceOnce_leaf_one valid
          objectRelated.headerRead objectRelated.headerOwned notPromoted
          objectRelated.ordinary countOne owned check
      exact ⟨result, header, memory, operation, objectRelated.headerRead,
        resultEq, headerWrite, finalValid, deadRelated⟩
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      have notPromoted : header.isPromotedTag = false := by
        simp [Header.isPromotedTag, headerKind, ordinary]
      have countOne : header.refCount.toNat = 1 := by
        rw [refCount, one]
      have owned : readOwnedReferences state address header = .ok [] := by
        simp [readOwnedReferences, headerKind]
      obtain ⟨result, memory, operation, resultEq, headerWrite, finalValid,
          deadRelated⟩ :=
        Fir.Wasm.Concrete.decrementReferenceOnce_leaf_one valid headerRead
          (LiveCellRel.natural descriptor objectEq headerRead headerKind ordinary marker
            extent limbsFit decoded refCount persistent live).headerOwned
          notPromoted ordinary countOne owned check
      exact ⟨result, header, memory, operation, headerRead, resultEq, headerWrite,
        finalValid, deadRelated⟩

/-- Complete local increment theorem for every live-cell representation in
the current W6 heap relation. -/
theorem LiveCellRel.incrementReference
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      Fir.Wasm.Concrete.incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc + amount } := by
  cases related with
  | @constructor info fieldKinds semantic header _ descriptor objectEq objectRelated
        headerRead headerKind refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .constructor descriptor objectEq objectRelated headerRead headerKind refCount
          persistent live
      exact localRelated.incrementReference_constructor ⟨semantic, objectEq⟩ valid
        amount fits check
  | @boxed kind scalar header _ descriptor objectEq objectRelated refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .boxed descriptor objectEq objectRelated refCount persistent live
      exact localRelated.incrementReference_boxed ⟨kind, scalar, objectEq⟩ valid
        amount fits check
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
          decoded refCount persistent live
      exact localRelated.incrementReference_natural ⟨value, objectEq⟩ valid
        amount fits check

/-- Complete local above-one decrement theorem for every live-cell
representation in the current W6 heap relation. -/
theorem LiveCellRel.decrementReferenceOnce_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      Fir.Wasm.Concrete.decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  cases related with
  | @constructor info fieldKinds semantic header _ descriptor objectEq objectRelated
        headerRead headerKind refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .constructor descriptor objectEq objectRelated headerRead headerKind refCount
          persistent live
      exact localRelated.decrementReferenceOnce_constructor_above_one
        ⟨semantic, objectEq⟩ valid oneLt check
  | @boxed kind scalar header _ descriptor objectEq objectRelated refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .boxed descriptor objectEq objectRelated refCount persistent live
      exact localRelated.decrementReferenceOnce_boxed_above_one
        ⟨kind, scalar, objectEq⟩ valid oneLt check
  | @natural value header _ descriptor objectEq headerRead headerKind ordinary marker
        extent limbsFit decoded refCount persistent live =>
      let localRelated : LiveCellRel state witness address cell :=
        .natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
          decoded refCount persistent live
      exact localRelated.decrementReferenceOnce_natural_above_one
        ⟨value, objectEq⟩ valid oneLt check

theorem LiveCellRel.live_eq_true
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) : cell.live = true := by
  cases related <;> assumption

theorem LiveCellRel.persistent_eq_false
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell) : cell.persistent = false := by
  cases related with
  | constructor _ _ objectRelated headerRead _ _ persistent _ =>
      obtain ⟨objectHeader, objectHeaderRead, _, _, objectOrdinary, _, _, _, _⟩ :=
        objectRelated.header
      rw [headerRead] at objectHeaderRead
      cases objectHeaderRead
      rw [← persistent]
      exact objectOrdinary
  | boxed _ _ objectRelated _ persistent _ =>
      rw [← persistent]
      exact objectRelated.ordinary
  | natural _ _ _ _ ordinary _ _ _ _ _ persistent _ =>
      rw [← persistent]
      exact ordinary

/-- Above one, the source ownership operation takes the same nonrecursive
count-rewrite step for every ordinary cell in the concrete heap relation. -/
theorem LiveCellRel.decValueOnce_above_one_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (oneLt : 1 < cell.rc) (check : Bool) :
    Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
      setCell runtime location { cell with rc := cell.rc - 1 } := by
  unfold Fir.LeanIR.Impure.decValueOnce
  exact Fir.LeanIR.Impure.decLocation_above_one runtime location cell found
    related.live_eq_true related.persistent_eq_false oneLt

/-- Source count-one release of a box or natural marks the cell dead directly:
their semantic payloads contain no heap references requiring recursion. -/
theorem LiveCellRel.decValueOnce_leaf_one_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (one : cell.rc = 1) (check : Bool) :
    Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
      setCell runtime location { cell with rc := 0, live := false } := by
  have nonzero : cell.rc ≠ 0 := by omega
  have notAboveOne : ¬1 < cell.rc := by omega
  unfold Fir.LeanIR.Impure.decValueOnce Fir.LeanIR.Impure.decLocation
  simp only [Fir.LeanIR.Impure.decLocationFuel, getLiveCell, found,
    related.live_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [if_neg (by simp [related.persistent_eq_false])]
  rw [if_neg nonzero, if_neg notAboveOne]
  rcases leafCell with boxedCell | naturalCell
  · obtain ⟨kind, scalar, objectEq⟩ := boxedCell
    have ownedValues : cell.object.ownedValues = #[scalar.semanticValue] := by
      rw [objectEq]
      rfl
    rw [ownedValues]
    have foldScalar (next : RuntimeState) :
        Array.foldlM (fun next value =>
          match value with
          | .object (.heap child) =>
              Fir.LeanIR.Impure.decLocationFuel runtime.heap.length next child
          | _ => .ok next) next #[scalar.semanticValue] = .ok next := by
      cases scalar <;>
        simp [BoxedScalar.semanticValue, Array.foldlM, Array.foldlM.loop]
    cases resultEq : setCell runtime location { cell with rc := 0, live := false } with
    | error fault => rfl
    | ok next => exact foldScalar next
  · obtain ⟨value, objectEq⟩ := naturalCell
    have ownedValues : cell.object.ownedValues = #[] := by
      rw [objectEq]
      rfl
    rw [ownedValues]
    cases resultEq : setCell runtime location { cell with rc := 0, live := false } with
    | error fault => rfl
    | ok next =>
        change Except.ok next = Except.ok next
        rfl

/-- Complete local source/concrete composition for count-one boxes and heap
naturals: both executions make the semantic cell dead, and concrete memory
retains exactly the canonical freed allocation relation. -/
theorem LiveCellRel.decrementReferenceOnce_leaf_refines_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (valid : state.FrontierInvariant)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (one : cell.rc = 1) (check : Bool) :
    ∃ result,
      Fir.Wasm.Concrete.decrementReferenceOnce state address check = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        setCell runtime location { cell with rc := 0, live := false } ∧
      result.FrontierInvariant ∧
      DeadCellRel result address := by
  obtain ⟨result, _, _, operation, _, _, _, finalValid, deadRelated⟩ :=
    related.decrementReferenceOnce_leaf_one leafCell valid one check
  exact ⟨result, operation,
    related.decValueOnce_leaf_one_eq leafCell runtime location found one check,
    finalValid, deadRelated⟩

/-- The boxed above-one decrement crosses the complete local refinement
boundary: concrete and source execution perform the same count update, and
the resulting concrete cell still decodes as that updated semantic cell. -/
theorem LiveCellRel.decrementReferenceOnce_boxed_refines_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (boxedCell : ∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
      cell.object = .boxed kind.semanticType scalar.semanticValue)
    (valid : state.FrontierInvariant)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        setCell runtime location { cell with rc := cell.rc - 1 } ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  obtain ⟨result, operation, finalValid, relatedAfter⟩ :=
    related.decrementReferenceOnce_boxed_above_one boxedCell valid oneLt check
  exact ⟨result, operation,
    related.decValueOnce_above_one_eq runtime location found oneLt check,
    finalValid, relatedAfter⟩

/-- Complete local source/concrete composition for the nonrecursive decrement
branch across constructors, boxes, and heap naturals. -/
theorem LiveCellRel.decrementReferenceOnce_refines_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (valid : state.FrontierInvariant)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      Fir.Wasm.Concrete.decrementReferenceOnce state address check = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        setCell runtime location { cell with rc := cell.rc - 1 } ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address { cell with rc := cell.rc - 1 } := by
  obtain ⟨result, operation, finalValid, relatedAfter⟩ :=
    related.decrementReferenceOnce_above_one valid oneLt check
  exact ⟨result, operation,
    related.decValueOnce_above_one_eq runtime location found oneLt check,
    finalValid, relatedAfter⟩

/-- Every currently represented ordinary live cell takes the same semantic
increment step; the object-specific concrete theorem only has to frame its
payload decoder. -/
theorem LiveCellRel.incValue_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (amount : Nat) (check : Bool) :
    Fir.LeanIR.Impure.incValue runtime (.object (.heap location)) amount check =
      setCell runtime location { cell with rc := cell.rc + amount } := by
  unfold Fir.LeanIR.Impure.incValue Fir.LeanIR.Impure.incLocation
  simp only [getLiveCell, found, related.live_eq_true, related.persistent_eq_false,
    ↓reduceIte, Bind.bind, Except.bind]
  congr 2

/-- The corresponding semantic boxed increment reaches exactly the mutable
`setCell` boundary with the incremented count. -/
theorem LiveCellRel.incValue_boxed_eq
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (boxedCell : ∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
      cell.object = .boxed kind.semanticType scalar.semanticValue)
    (runtime : RuntimeState) (location : Location)
    (found : findCell? runtime.heap location = some cell)
    (amount : Nat) (check : Bool) :
    Fir.LeanIR.Impure.incValue runtime (.object (.heap location)) amount check =
      setCell runtime location { cell with rc := cell.rc + amount } := by
  have cellLive : cell.live = true := by
    cases related with
    | constructor _ objectEq _ _ _ _ _ live =>
        obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
    | boxed _ _ _ _ _ live => exact live
    | natural _ objectEq _ _ _ _ _ _ _ _ _ live =>
        obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
  have notPersistent : cell.persistent = false := by
    cases related with
    | constructor _ objectEq _ _ _ _ _ _ =>
        obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
    | boxed _ _ objectRelated _ persistent _ =>
        rw [← persistent]
        exact objectRelated.ordinary
    | natural _ objectEq _ _ _ _ _ _ _ _ _ _ =>
        obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
  unfold Fir.LeanIR.Impure.incValue Fir.LeanIR.Impure.incLocation
  simp only [getLiveCell, found, cellLive, notPersistent, ↓reduceIte,
    Bind.bind, Except.bind]
  congr 2

end Fir.Wasm.Concrete
