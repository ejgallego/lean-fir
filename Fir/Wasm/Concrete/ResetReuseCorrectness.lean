import Fir.Wasm.Concrete.OwnershipFrameCorrectness
import Fir.Wasm.Concrete.ConstructorHeapCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Explicit transition relation for the unique reset-to-reuse protocol.
`LiveHeapRel` is required only before reset; the exact concrete and semantic
reset equations name the temporary states without claiming that cleared
heap-only slots satisfy the normal ABI-indexed value relation. A later reuse
must consume both states together and re-establish `LiveHeapRel`. -/
structure ResetReuseProtocolRel
    (before after : MemoryState) (witness : RefinementWitness)
    (runtime nextRuntime : RuntimeState) (location : Location)
    (address : Word32) (cell : HeapCell) (object : ConstructorObject)
    (count : Nat) : Prop where
  relatedBefore : LiveHeapRel before witness runtime
  mapped : witness.locations.lookup? location = some address
  found : findCell? runtime.heap location = some cell
  live : cell.live = true
  ordinary : cell.persistent = false
  unique : cell.rc = 1
  constructor : cell.object = .ctor object
  countFits : count ≤ object.objectFields.size
  concreteReset : resetObject before count address = .ok (after, address)
  semanticReset :
    Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
      .ok (nextRuntime, .reuseToken (some location))

/-- Protocol-only descriptor kinds for the reset target. Cleared prefix slots
are decoded as tagged-capable objects; untouched suffix slots retain their
frozen allocation-time ABI kinds. -/
def resetProtocolFieldKinds (fieldKinds : Array AbiKind) (count : Nat) :
    Array AbiKind :=
  fieldKinds.mapIdx fun index kind =>
    if index < count then .tobject else kind

@[simp] theorem resetProtocolFieldKinds_size (fieldKinds : Array AbiKind)
    (count : Nat) :
    (resetProtocolFieldKinds fieldKinds count).size = fieldKinds.size := by
  simp [resetProtocolFieldKinds]

theorem resetProtocolFieldKinds_prefix
    {fieldKinds : Array AbiKind} {count index : Nat} {kind : AbiKind}
    (atIndex : fieldKinds[index]? = some kind) (cleared : index < count) :
    (resetProtocolFieldKinds fieldKinds count)[index]? = some .tobject := by
  rw [resetProtocolFieldKinds, Array.getElem?_mapIdx, atIndex]
  simp [cleared]

theorem resetProtocolFieldKinds_suffix
    {fieldKinds : Array AbiKind} {count index : Nat} {kind : AbiKind}
    (atIndex : fieldKinds[index]? = some kind) (retained : count ≤ index) :
    (resetProtocolFieldKinds fieldKinds count)[index]? = some kind := by
  rw [resetProtocolFieldKinds, Array.getElem?_mapIdx, atIndex]
  simp [Nat.not_lt.mpr retained]

theorem resetProtocolFieldKinds_valid
    (fieldKinds : Array AbiKind) (count : Nat)
    (valid : fieldKinds.all AbiKind.isObjectField = true) :
    (resetProtocolFieldKinds fieldKinds count).all AbiKind.isObjectField = true := by
  apply Array.all_eq_true.mpr
  intro index indexLt
  simp only [resetProtocolFieldKinds] at indexLt ⊢
  rw [Array.getElem_mapIdx]
  split
  · rfl
  · exact Array.all_eq_true.mp valid index (by simpa using indexLt)

/-- Canonical cleared reset slots have an exact strict relation at the
protocol-only tagged-capable kind. -/
theorem ValueRel.taggedZero_tobject (witness : RefinementWitness) :
    ValueRel witness .tobject (.word32 taggedZero)
      (.object (.tagged 0)) := by
  exact .tobject (.tagged (.immediate 0 (by decide)))

theorem resetProtocolFieldKinds_prefix_rel
    (witness : RefinementWitness) (address : Word32) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (count index : Nat) (kind : AbiKind)
    (atIndex : fieldKinds[index]? = some kind) (cleared : index < count) :
    ∃ protocolKind,
      (resetProtocolFieldKinds fieldKinds count)[index]? = some protocolKind ∧
      ValueRel (witness.rebindConstructor address info
        (resetProtocolFieldKinds fieldKinds count)) protocolKind
        (.word32 taggedZero) (.object (.tagged 0)) := by
  exact ⟨.tobject,
    resetProtocolFieldKinds_prefix atIndex cleared,
    ValueRel.taggedZero_tobject _⟩

theorem resetProtocolFieldKinds_suffix_rel
    (witness : RefinementWitness) (address : Word32) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (count index : Nat) (kind : AbiKind)
    {word : Word32} {value : Value}
    (atIndex : fieldKinds[index]? = some kind) (retained : count ≤ index)
    (related : ValueRel witness kind (.word32 word) value) :
    ∃ protocolKind,
      (resetProtocolFieldKinds fieldKinds count)[index]? = some protocolKind ∧
      ValueRel (witness.rebindConstructor address info
        (resetProtocolFieldKinds fieldKinds count)) protocolKind
        (.word32 word) value := by
  exact ⟨kind,
    resetProtocolFieldKinds_suffix atIndex retained,
    related.rebindConstructor address info
      (resetProtocolFieldKinds fieldKinds count)⟩

/-- Semantic reset target immediately after the ownership prefix has been
cleared but before those former children are released. -/
def resetProtocolObject (object : ConstructorObject) (count : Nat) :
    ConstructorObject := {
  object with
  objectFields := object.objectFields.mapIdx fun index field =>
    if index < count then .object (.tagged 0) else field }

/-- Clearing a bounded concrete prefix establishes the normal constructor
relation under reset's protocol-only descriptor. All non-object observations
are framed; object slots split into canonical tagged-zero prefix values and
unchanged suffix values. -/
theorem ConstructorObjectRel.resetPrefix
    (state : MemoryState) (memory : LinearMemory) (witness : RefinementWitness)
    (address : Word32) (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (semantic : ConstructorObject) (count : Nat)
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (countFits : count ≤ semantic.objectFields.size)
    (post : WriteObjectFieldsPost state.memory memory address.value 0
      (List.replicate count taggedZero)) :
    ConstructorObjectRel ({ state with memory } : MemoryState)
      (witness.rebindConstructor address info
        (resetProtocolFieldKinds fieldKinds count))
      address info (resetProtocolFieldKinds fieldKinds count)
      (resetProtocolObject semantic count) := by
  obtain ⟨header, headerRead, headerKind, allocationBytes, persistent,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      (List.replicate count taggedZero) post]
    exact headerRead
  have countFitsInfo : count ≤ info.size := by
    rw [← related.semanticObjectFields]
    exact countFits
  have writtenFits : (List.replicate count taggedZero).length ≤
      header.aux1.toNat := by
    simp only [List.length_replicate]
    rw [objectCount]
    exact countFitsInfo
  refine {
    header := ⟨header, headerAfter, headerKind, allocationBytes, persistent,
      tag, objectCount, usizeCount, scalarCount⟩
    headerOwned := related.headerOwned
    extent := related.extent
    semanticObjectFields := by
      simp [resetProtocolObject, related.semanticObjectFields]
    semanticUSizeFields := by
      simpa [resetProtocolObject] using related.semanticUSizeFields
    semanticScalarFields := ?_
    fieldKindsSize := by
      simpa using related.fieldKindsSize
    fieldKindsValid := resetProtocolFieldKinds_valid fieldKinds count
      related.fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · intro field member
    have oldMember : field ∈ semantic.scalarFields := by
      simpa [resetProtocolObject] using member
    have beforeField := related.semanticScalarFields field oldMember
    cases valueEq : field.value with
    | uint8 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have slotIndexEq : field.width =
            header.aux1.toNat + header.aux2.toNat := by
          rw [widthEq, objectCount, usizeCount]
        rw [readScalarUInt8Field_of_writeObjectFields state memory address header
          (List.replicate count taggedZero) field.width field.offset headerRead
          headerKind writtenFits slotIndexEq post]
        exact readBefore
    | uint16 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have slotIndexEq : field.width =
            header.aux1.toNat + header.aux2.toNat := by
          rw [widthEq, objectCount, usizeCount]
        rw [readScalarUInt16Field_of_writeObjectFields state memory address header
          (List.replicate count taggedZero) field.width field.offset headerRead
          headerKind writtenFits slotIndexEq post]
        exact readBefore
    | uint32 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have slotIndexEq : field.width =
            header.aux1.toNat + header.aux2.toNat := by
          rw [widthEq, objectCount, usizeCount]
        rw [readScalarUInt32Field_of_writeObjectFields state memory address header
          (List.replicate count taggedZero) field.width field.offset headerRead
          headerKind writtenFits slotIndexEq post]
        exact readBefore
    | uint64 value =>
        simp only [valueEq] at beforeField ⊢
        obtain ⟨widthEq, fieldFits, readBefore⟩ := beforeField
        refine ⟨widthEq, fieldFits, ?_⟩
        have slotIndexEq : field.width =
            header.aux1.toNat + header.aux2.toNat := by
          rw [widthEq, objectCount, usizeCount]
        rw [readScalarUInt64Field_of_writeObjectFields state memory address header
          (List.replicate count taggedZero) field.width field.offset headerRead
          headerKind writtenFits slotIndexEq post]
        exact readBefore
  · intro index protocolKind value protocolKindAt valueAt
    have indexLtSemantic : index < semantic.objectFields.size := by
      obtain ⟨indexLt, _⟩ := Array.getElem?_eq_some_iff.mp valueAt
      simpa [resetProtocolObject] using indexLt
    have indexLtInfo : index < info.size := by
      rw [← related.semanticObjectFields]
      exact indexLtSemantic
    have indexLtKinds : index < fieldKinds.size := by
      rw [related.fieldKindsSize]
      exact indexLtInfo
    let originalKind := fieldKinds[index]
    let originalValue := semantic.objectFields[index]
    have originalKindAt : fieldKinds[index]? = some originalKind :=
      Array.getElem?_eq_getElem indexLtKinds
    have originalValueAt : semantic.objectFields[index]? = some originalValue :=
      Array.getElem?_eq_getElem indexLtSemantic
    have indexValid : index < header.aux1.toNat := by
      rw [objectCount]
      exact indexLtInfo
    by_cases cleared : index < count
    · have protocolAt := resetProtocolFieldKinds_prefix originalKindAt cleared
      rw [protocolAt] at protocolKindAt
      have protocolKindEq : protocolKind = .tobject :=
        Option.some.inj protocolKindAt.symm
      subst protocolKind
      have clearedAt : (resetProtocolObject semantic count).objectFields[index]? =
          some (.object (.tagged 0)) := by
        rw [resetProtocolObject, Array.getElem?_mapIdx, originalValueAt]
        simp [cleared]
      rw [clearedAt] at valueAt
      have valueEq : value = .object (.tagged 0) :=
        Option.some.inj valueAt.symm
      subst value
      have installedAt : (List.replicate count taggedZero)[index]? =
          some taggedZero := by
        simp [cleared]
      exact ⟨taggedZero,
        readObjectField_of_writeObjectFields_at state memory address header
          (List.replicate count taggedZero) index taggedZero headerRead headerKind
          indexValid post installedAt,
        ValueRel.taggedZero_tobject _⟩
    · have retained : count ≤ index := Nat.le_of_not_gt cleared
      have protocolAt := resetProtocolFieldKinds_suffix originalKindAt retained
      rw [protocolAt] at protocolKindAt
      have protocolKindEq : protocolKind = originalKind :=
        Option.some.inj protocolKindAt.symm
      subst protocolKind
      have retainedAt : (resetProtocolObject semantic count).objectFields[index]? =
          some originalValue := by
        rw [resetProtocolObject, Array.getElem?_mapIdx, originalValueAt]
        simp [cleared]
      rw [retainedAt] at valueAt
      have valueEq : value = originalValue := Option.some.inj valueAt.symm
      subst value
      obtain ⟨word, readBefore, valueRelated⟩ :=
        related.objectFields index originalKind originalValue originalKindAt
          originalValueAt
      exact ⟨word,
        readObjectField_of_writeObjectFields_suffix state memory address header
          (List.replicate count taggedZero) index headerRead headerKind (by
            simpa using retained) post ▸ readBefore,
        valueRelated.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)⟩
  · intro index value valueAt
    have oldAt : semantic.usizeFields[index]? = some value := by
      simpa [resetProtocolObject] using valueAt
    rw [readUSizeField_of_writeObjectFields state memory address header
      (List.replicate count taggedZero) index headerRead headerKind writtenFits post]
    exact related.usizeFields index value oldAt

/-- The protocol transition returns the same already-mapped location/address
pair in both reuse-token representations. -/
theorem ResetReuseProtocolRel.tokenRelated
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {object : ConstructorObject}
    {count : Nat}
    (protocol : ResetReuseProtocolRel before after witness runtime nextRuntime
      location address cell object count) :
    ValueRel witness .reuseToken (.word32 address)
      (.reuseToken (some location)) :=
  .reuseSome (.mapped protocol.mapped)

/-- Rebinding the active constructor descriptor after reuse does not change
the protocol token's semantic location identity. -/
theorem ResetReuseProtocolRel.tokenRelated_rebindConstructor
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {object : ConstructorObject}
    {count : Nat}
    (protocol : ResetReuseProtocolRel before after witness runtime nextRuntime
      location address cell object count)
    (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    ValueRel (witness.rebindConstructor address info fieldKinds) .reuseToken
      (.word32 address) (.reuseToken (some location)) :=
  protocol.tokenRelated.rebindConstructor address info fieldKinds

theorem ResetReuseProtocolRel.reboundWitnessWellFormed
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {object : ConstructorObject}
    {count : Nat}
    (protocol : ResetReuseProtocolRel before after witness runtime nextRuntime
      location address cell object count)
    (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    (witness.rebindConstructor address info fieldKinds).WellFormed :=
  protocol.relatedBefore.witnessWellFormed.rebindConstructor address info fieldKinds

/-- Both physical tagged encodings take reset's empty-token path without
changing concrete memory. -/
theorem LiveHeapRel.resetObject_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload) (count : Nat) :
    resetObject state count word = .ok (state, Word32.zero) := by
  cases tagged with
  | immediate actualPayload fits =>
      unfold resetObject
      rw [Word32.classify_encodeImmediate]
      rfl
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
      have releaseNoop : decrementReferenceOnce state word true = .ok state := by
        simpa using related.decrementReferenceOnce_tagged
          (TaggedReferenceRel.promoted found) true
      unfold resetObject
      rw [addressHeap, headerRead]
      simp only [Bind.bind, Except.bind, liftMemory]
      rw [if_pos (by simp [isPromoted])]
      rw [releaseNoop]
      rfl

/-- The tagged reset equation agrees with FIR and returns the related empty
reuse token. -/
theorem LiveHeapRel.resetObject_refines_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload) (count : Nat) :
    resetObject state count word = .ok (state, Word32.zero) ∧
      Fir.LeanIR.Impure.reset runtime count (.object (.tagged payload)) =
        .ok (runtime, .reuseToken none) ∧
      ValueRel witness .reuseToken (.word32 Word32.zero) (.reuseToken none) := by
  exact ⟨related.resetObject_tagged tagged count, rfl, .reuseNone⟩

/-- A non-unique ordinary heap cell follows reset's fallback path: one public
decrement is performed and the empty reuse token is returned. -/
theorem LiveHeapRel.resetObject_refines_nonunique
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {count : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (notUnique : cell.rc ≠ 1)
    (semanticOperation :
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .ok (nextRuntime, .reuseToken none)) :
    ∃ result,
      resetObject state count address = .ok (result, Word32.zero) ∧
      LiveHeapRel result witness nextRuntime ∧
      ValueRel witness .reuseToken (.word32 Word32.zero) (.reuseToken none) := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, ordinary, refCount⟩ :=
    targetRelated.ordinaryHeader
  have headerCountNe : header.refCount ≠ 1 := by
    intro one
    rw [one] at refCount
    simp at refCount
    exact notUnique refCount.symm
  have fallback :
      (header.isPromotedTag || header.persistent || header.refCount != 1) = true := by
    simp [notPromoted, ordinary, headerCountNe]
  have semanticDec :
      Fir.LeanIR.Impure.decLocation runtime location = .ok nextRuntime := by
    unfold Fir.LeanIR.Impure.reset at semanticOperation
    simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
      at semanticOperation
    rw [if_pos (by simp [targetRelated.persistent_eq_false, notUnique])]
      at semanticOperation
    cases decEq : Fir.LeanIR.Impure.decLocation runtime location with
    | error fault =>
        rw [decEq] at semanticOperation
        contradiction
    | ok middleRuntime =>
        rw [decEq] at semanticOperation
        have pairEq := Except.ok.inj semanticOperation
        have runtimeEq : middleRuntime = nextRuntime :=
          congrArg Prod.fst pairEq
        subst middleRuntime
        rfl
  obtain ⟨result, concreteDec, finalRelated⟩ :=
    related.decrementReferenceOnce_refines mapped semanticDec
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  have concreteReset :
      resetObject state count address = .ok (result, Word32.zero) := by
    unfold resetObject
    rw [addressHeap, headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_pos fallback, concreteDec]
    rfl
  exact ⟨result, concreteReset, finalRelated, .reuseNone⟩

/-- Consuming an empty reuse token is exactly fresh constructor allocation.
For a nonempty layout, the existing allocation theorem supplies the extended
witness, complete heap relation, and returned heap reference. -/
theorem LiveHeapRel.reuseObject_none_refines_nonempty
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (fields : Array Word32)
    (semanticFields : Array Value) (address : Word32) (updateHeader : Bool)
    (related : LiveHeapRel state witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (reused : reuseObject state Word32.zero info updateHeader fields =
      .ok (result, address)) :
    let nextWitness :=
      witness.bindConstructor runtime.nextLocation address info fieldKinds
    LiveHeapRel result nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      Fir.LeanIR.Impure.reuse runtime (.reuseToken none) info updateHeader
        semanticFields =
          .ok (semanticConstructorResult runtime info semanticFields,
            .object (.heap runtime.nextLocation)) := by
  have allocated : allocateConstructor state info fields = .ok (result, address) := by
    unfold reuseObject at reused
    rw [if_pos (by decide)] at reused
    exact reused
  obtain ⟨heapRelated, valueRelated⟩ :=
    allocateConstructor_nonempty_liveHeapRel state result witness runtime info
      fieldKinds fields semanticFields address related arity semanticArity
      fieldKindsSize fieldKindsValid fieldRelated nonempty tagFits objectFieldsFit
      usizeFieldsFit scalarBytesFit allocated
  exact ⟨heapRelated, valueRelated, by
    simpa [Fir.LeanIR.Impure.reuse] using
      allocCtor_nonempty_eq runtime info semanticFields semanticArity nonempty⟩

end Fir.Wasm.Concrete
