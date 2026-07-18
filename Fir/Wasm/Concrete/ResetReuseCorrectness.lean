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

/-- Constructor payload relations transport through a proof-only descriptor
rebind; only their nested value relations mention the witness. -/
theorem ConstructorObjectRel.rebindConstructor
    {state : MemoryState} {witness : RefinementWitness}
    {address reboundAddress : Word32} {info reboundInfo : LCNF.CtorInfo}
    {fieldKinds reboundFieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic) :
    ConstructorObjectRel state
      (witness.rebindConstructor reboundAddress reboundInfo reboundFieldKinds)
      address info fieldKinds semantic := by
  refine {
    header := related.header
    headerOwned := related.headerOwned
    extent := related.extent
    semanticObjectFields := related.semanticObjectFields
    semanticUSizeFields := related.semanticUSizeFields
    semanticScalarFields := related.semanticScalarFields
    fieldKindsSize := related.fieldKindsSize
    fieldKindsValid := related.fieldKindsValid
    objectFields := ?_
    usizeFields := related.usizeFields }
  intro index kind value kindAt valueAt
  obtain ⟨word, read, valueRelated⟩ :=
    related.objectFields index kind value kindAt valueAt
  exact ⟨word, read,
    valueRelated.rebindConstructor reboundAddress reboundInfo reboundFieldKinds⟩

/-- Rebinding one active descriptor leaves every live cell at a distinct
physical address related. -/
theorem LiveCellRel.rebindConstructor_other
    {state : MemoryState} {witness : RefinementWitness}
    {address reboundAddress : Word32} {cell : HeapCell}
    {reboundInfo : LCNF.CtorInfo} {reboundFieldKinds : Array AbiKind}
    (related : LiveCellRel state witness address cell)
    (different : reboundAddress.value ≠ address.value) :
    LiveCellRel state
      (witness.rebindConstructor reboundAddress reboundInfo reboundFieldKinds)
      address cell := by
  cases related with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
      persistent live =>
      exact .constructor
        (by
          rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress
            address reboundInfo reboundFieldKinds different]
          exact descriptor)
        objectEq objectRelated.rebindConstructor headerRead headerKind refCount
          persistent live
  | boxed descriptor objectEq objectRelated refCount persistent live =>
      exact .boxed
        (by
          rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress
            address reboundInfo reboundFieldKinds different]
          exact descriptor)
        objectEq objectRelated refCount persistent live
  | natural descriptor objectEq headerRead headerKind ordinary marker extent limbsFit
      decoded refCount persistent live =>
      exact .natural
        (by
          rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress
            address reboundInfo reboundFieldKinds different]
          exact descriptor)
        objectEq headerRead headerKind ordinary marker extent limbsFit decoded refCount
          persistent live

/-- Rebinding one active descriptor leaves every whole-cell relation at a
distinct physical address intact. -/
theorem CellRel.rebindConstructor_other
    {state : MemoryState} {witness : RefinementWitness}
    {address reboundAddress : Word32} {cell : HeapCell}
    {reboundInfo : LCNF.CtorInfo} {reboundFieldKinds : Array AbiKind}
    (related : CellRel state witness address cell)
    (different : reboundAddress.value ≠ address.value) :
    CellRel state
      (witness.rebindConstructor reboundAddress reboundInfo reboundFieldKinds)
      address cell := by
  cases related with
  | live liveRelated =>
      exact .live (liveRelated.rebindConstructor_other different)
  | dead count dead descriptor deadRelated =>
      obtain ⟨allocation, found⟩ := descriptor
      exact .dead count dead
        ⟨allocation, by
          rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress
            address reboundInfo reboundFieldKinds different]
          exact found⟩
        deadRelated

/-- Rebinding a distinct constructor descriptor leaves a promoted tagged
representation and its shadow descriptor unchanged. -/
theorem PromotedTagRel.rebindConstructor_other
    {state : MemoryState} {witness : RefinementWitness}
    {payload : UInt64} {address reboundAddress : Word32}
    {reboundInfo : LCNF.CtorInfo} {reboundFieldKinds : Array AbiKind}
    (related : PromotedTagRel state witness payload address)
    (different : reboundAddress.value ≠ address.value) :
    PromotedTagRel state
      (witness.rebindConstructor reboundAddress reboundInfo reboundFieldKinds)
      payload address := {
  mapped := by simpa using related.mapped
  descriptor := by
    rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress address
      reboundInfo reboundFieldKinds different]
    exact related.descriptor
  header := related.header
  decoded := related.decoded }

/-- Assemble a semantic `setCell` step while the target's proof descriptor is
rebound. Location identities do not change; callers provide the rebuilt
target and framed non-target relations under the new witness. -/
theorem LiveHeapRel.setCell_rebindConstructor_of_frames
    {state result : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell replacement : HeapCell} (reboundInfo : LCNF.CtorInfo)
    (reboundFieldKinds : Array AbiKind)
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (cursor : result.heapCursor = state.heapCursor)
    (frontier : result.FrontierInvariant)
    (targetRelated : CellRel result
      (witness.rebindConstructor address reboundInfo reboundFieldKinds)
      address replacement)
    (descriptorRegion : ∀ other descriptor,
      (witness.rebindConstructor address reboundInfo reboundFieldKinds).descriptors.lookup?
          other = some descriptor →
      ∃ header,
        Header.read result.memory other = .ok header ∧
        headerBytes ≤ header.allocationBytes.toNat ∧
        header.allocationBytes.toNat % target.heapAlignment = 0 ∧
        other.value + header.allocationBytes.toNat ≤ result.heapCursor)
    (descriptorDisjoint : ∀ left right leftDescriptor rightDescriptor,
      (witness.rebindConstructor address reboundInfo reboundFieldKinds).descriptors.lookup?
          left = some leftDescriptor →
      (witness.rebindConstructor address reboundInfo reboundFieldKinds).descriptors.lookup?
          right = some rightDescriptor →
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
      CellRel result
        (witness.rebindConstructor address reboundInfo reboundFieldKinds)
        otherAddress otherCell)
    (promotedFrame : ∀ payload other,
      witness.promotedTags.Contains payload other →
      PromotedTagRel result
        (witness.rebindConstructor address reboundInfo reboundFieldKinds)
        payload other) :
    ∃ nextRuntime,
      setCell runtime location replacement = .ok nextRuntime ∧
      LiveHeapRel result
        (witness.rebindConstructor address reboundInfo reboundFieldKinds)
        nextRuntime := by
  obtain ⟨nextRuntime, updated, targetFound, otherFound, heapLength,
      nextLocation⟩ :=
    setCell_spec_of_find runtime location cell replacement found
  refine ⟨nextRuntime, updated, ?_⟩
  refine {
    frontier
    witnessWellFormed :=
      related.witnessWellFormed.rebindConstructor address reboundInfo
        reboundFieldKinds
    locationsBeforeNext := ?_
    releaseFuelBound := by
      rw [heapLength, cursor]
      exact related.releaseFuelBound
    descriptorsOwned := ?_
    descriptorRegion
    descriptorDisjoint
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
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
      exact ⟨address, by simpa using mapped, targetRelated⟩
    · have foundBefore : findCell? runtime.heap other = some otherCell := by
        rw [← otherFound other isTarget]
        exact foundAfter
      obtain ⟨otherAddress, otherMapped, otherRelated⟩ :=
        related.semanticToConcrete other otherCell foundBefore
      exact ⟨otherAddress, by simpa using otherMapped,
        cellFrame other otherAddress otherCell isTarget foundBefore otherMapped
          otherRelated⟩
  · intro other otherAddress reboundMapped
    have oldMapped : witness.locations.lookup? other = some otherAddress := by
      simpa using reboundMapped
    by_cases isTarget : other = location
    · subst other
      have addressEq := Option.some.inj (mapped.symm.trans oldMapped)
      subst otherAddress
      exact ⟨replacement, targetFound, targetRelated⟩
    · obtain ⟨otherCell, foundBefore, otherRelated⟩ :=
        related.concreteToSemantic other otherAddress oldMapped
      exact ⟨otherCell, by
          rw [otherFound other isTarget]
          exact foundBefore,
        cellFrame other otherAddress otherCell isTarget foundBefore oldMapped
          otherRelated⟩
  · intro payload other reboundMapped
    apply promotedFrame payload other
    simpa using reboundMapped

/-- A successful unique-reset prefix clear and matching semantic `setCell`
produce a complete whole-heap relation under the protocol witness. -/
theorem LiveHeapRel.writeObjectFields_resetPrefix
    (state : MemoryState) (memory : LinearMemory) (witness : RefinementWitness)
    (runtime : RuntimeState) (location : Location) (address : Word32)
    (cell : HeapCell) (header : Header) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (semantic : ConstructorObject) (count : Nat)
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor info fieldKinds))
    (objectEq : cell.object = .ctor semantic)
    (objectRelated : ConstructorObjectRel state witness address info fieldKinds
      semantic)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (refCount : header.refCount.toNat = cell.rc)
    (persistent : header.persistent = cell.persistent)
    (live : cell.live = true)
    (countFits : count ≤ semantic.objectFields.size)
    (written : writeObjectFields state.memory address.value 0
      (List.replicate count taggedZero) = .ok memory) :
    ∃ nextRuntime,
      setCell runtime location
          { cell with object := .ctor (resetProtocolObject semantic count) } =
        .ok nextRuntime ∧
      LiveHeapRel ({ state with memory } : MemoryState)
        (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count))
        nextRuntime := by
  have wordEq : ∀ left right : Word32, left.value = right.value → left = right := by
    intro left right equal
    cases left
    cases right
    simp_all
  have targetBefore : LiveCellRel state witness address cell :=
    .constructor descriptor objectEq objectRelated headerRead headerKind refCount
      persistent live
  obtain ⟨relationHeader, relationRead, _, activeFits, _, _, _, _, _⟩ :=
    objectRelated.header
  rw [headerRead] at relationRead
  have relationHeaderEq := Except.ok.inj relationRead
  subst relationHeader
  obtain ⟨_, rawRead, _, headerMinimum, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have countFitsInfo : count ≤ info.size := by
    rw [← objectRelated.semanticObjectFields]
    exact countFits
  have fieldsInTarget : objectFieldAddress address.value
      (List.replicate count taggedZero).length ≤
        address.value + header.allocationBytes.toNat := by
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
        info.ssize)
    simp only [List.length_replicate]
    simp [objectFieldAddress, ConstructorLayout.ofInfo, target] at activeFits aligned ⊢
    omega
  have fieldsBeforeFrontier : objectFieldAddress address.value
      (List.replicate count taggedZero).length ≤ state.heapCursor := by
    have fieldsInActive : objectFieldAddress address.value
        (List.replicate count taggedZero).length ≤
          address.value + (ConstructorLayout.ofInfo info).allocationBytes := by
      have aligned := align8_ge
        (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
          info.ssize)
      simp [objectFieldAddress, ConstructorLayout.ofInfo, target] at aligned ⊢
      omega
    have activeExtent := objectRelated.extent
    have headerOwned := targetBefore.headerOwned
    omega
  have fieldsInBounds : objectFieldAddress address.value
      (0 + (List.replicate count taggedZero).length) ≤ state.memory.size := by
    simp only [Nat.zero_add]
    exact Nat.le_trans fieldsBeforeFrontier related.frontier.cursorInBounds
  have post := writeObjectFields_post state.memory memory address.value 0
    (List.replicate count taggedZero) fieldsInBounds written
  have finalFrontier : ({ state with memory } : MemoryState).FrontierInvariant :=
    related.frontier.writeObjectFields (by simpa using fieldsBeforeFrontier) written
  have objectAfter := objectRelated.resetPrefix state memory witness address info
    fieldKinds semantic count countFits post
  have headerAfter :
      ({ state with memory } : MemoryState).readLiveHeader address = .ok header := by
    rw [MemoryState.readLiveHeader_of_writeObjectFields state memory address 0
      (List.replicate count taggedZero) post]
    exact headerRead
  have targetAfter : CellRel ({ state with memory } : MemoryState)
      (witness.rebindConstructor address info
      (resetProtocolFieldKinds fieldKinds count)) address
      { cell with object := .ctor (resetProtocolObject semantic count) } := by
    apply CellRel.live
    apply LiveCellRel.constructor
      (witness.lookup_rebindConstructor_descriptor address info
        (resetProtocolFieldKinds fieldKinds count))
      rfl objectAfter headerAfter headerKind
    · simpa using refCount
    · simpa using persistent
    · simpa using live
  obtain ⟨oldDescriptorRegion, oldDescriptorDisjoint⟩ :=
    related.descriptorSpatial_of_writeObjectFields descriptor rawRead rfl
      fieldsInTarget written
  have rawReadAfter : Header.read memory address = .ok header := by
    rw [Header.read_of_writeObjectFields state.memory memory address 0
      (List.replicate count taggedZero) post]
    exact rawRead
  have protocolDescriptorRegion : ∀ other otherDescriptor,
      (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)).descriptors.lookup? other =
        some otherDescriptor →
      ∃ otherHeader,
        Header.read memory other = .ok otherHeader ∧
        headerBytes ≤ otherHeader.allocationBytes.toNat ∧
        otherHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
        other.value + otherHeader.allocationBytes.toNat ≤ state.heapCursor := by
    intro other otherDescriptor otherFound
    by_cases different : address.value ≠ other.value
    · rw [witness.lookup_rebindConstructor_descriptor_other address other info
        (resetProtocolFieldKinds fieldKinds count) different] at otherFound
      simpa using oldDescriptorRegion other otherDescriptor otherFound
    · have sameValue : address.value = other.value := by omega
      have otherEq : other = address := wordEq other address sameValue.symm
      subst other
      simpa using oldDescriptorRegion address (.constructor info fieldKinds) descriptor
  have protocolDescriptorDisjoint : ∀ left right leftDescriptor rightDescriptor,
      (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)).descriptors.lookup? left =
        some leftDescriptor →
      (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)).descriptors.lookup? right =
        some rightDescriptor →
      left.value ≠ right.value →
      ∀ leftHeader rightHeader,
        Header.read memory left = .ok leftHeader →
        Header.read memory right = .ok rightHeader →
        left.value + leftHeader.allocationBytes.toNat ≤ right.value ∨
          right.value + rightHeader.allocationBytes.toNat ≤ left.value := by
    intro left right leftDescriptor rightDescriptor leftFound rightFound different
      leftHeader rightHeader leftRead rightRead
    by_cases leftTarget : address.value = left.value
    · have rightTarget : address.value ≠ right.value := by
        intro rightEq
        exact different (leftTarget.symm.trans rightEq)
      have leftEq : left = address := wordEq left address leftTarget.symm
      subst left
      rw [rawReadAfter] at leftRead
      have leftHeaderEq := Except.ok.inj leftRead
      subst leftHeader
      rw [witness.lookup_rebindConstructor_descriptor_other address right info
        (resetProtocolFieldKinds fieldKinds count) rightTarget] at rightFound
      exact oldDescriptorDisjoint address right (.constructor info fieldKinds)
        rightDescriptor descriptor rightFound rightTarget header rightHeader rawReadAfter
          rightRead
    · by_cases rightTarget : address.value = right.value
      · have rightEq : right = address := wordEq right address rightTarget.symm
        subst right
        rw [rawReadAfter] at rightRead
        have rightHeaderEq := Except.ok.inj rightRead
        subst rightHeader
        rw [witness.lookup_rebindConstructor_descriptor_other address left info
          (resetProtocolFieldKinds fieldKinds count) leftTarget] at leftFound
        exact oldDescriptorDisjoint left address leftDescriptor
          (.constructor info fieldKinds) leftFound descriptor (Ne.symm leftTarget)
            leftHeader header leftRead rawReadAfter
      · rw [witness.lookup_rebindConstructor_descriptor_other address left info
          (resetProtocolFieldKinds fieldKinds count) leftTarget] at leftFound
        rw [witness.lookup_rebindConstructor_descriptor_other address right info
          (resetProtocolFieldKinds fieldKinds count) rightTarget] at rightFound
        exact oldDescriptorDisjoint left right leftDescriptor rightDescriptor
          leftFound rightFound different leftHeader rightHeader leftRead rightRead
  have cellFrame : ∀ other otherAddress otherCell,
      other ≠ location →
      findCell? runtime.heap other = some otherCell →
      witness.locations.lookup? other = some otherAddress →
      CellRel state witness otherAddress otherCell →
      CellRel ({ state with memory } : MemoryState)
        (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)) otherAddress otherCell := by
    intro other otherAddress otherCell otherNe _ mappedOther otherRelated
    obtain ⟨otherDescriptor, otherDescriptorFound⟩ := otherRelated.descriptor
    obtain ⟨otherHeader, otherHeaderRead, _, _, _⟩ :=
      related.descriptorRegion otherAddress otherDescriptor otherDescriptorFound
    have differentWord : address ≠ otherAddress := by
      intro equal
      subst otherAddress
      have locationEq := related.witnessWellFormed.locationInjective location other
        address mapped mappedOther
      exact otherNe locationEq.symm
    have differentValue : address.value ≠ otherAddress.value := by
      intro equal
      exact differentWord (wordEq address otherAddress equal)
    have frame := related.allocationFrame_of_writeObjectFields_other descriptor
      otherDescriptorFound differentValue rawRead otherHeaderRead rfl fieldsInTarget
        written
    exact (otherRelated.allocationFrame otherHeaderRead frame)
      |>.rebindConstructor_other differentValue
  have promotedFrame : ∀ payload other,
      witness.promotedTags.Contains payload other →
      PromotedTagRel ({ state with memory } : MemoryState)
        (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)) payload other := by
    intro payload other promotedMapped
    have promoted := related.promoted payload other promotedMapped
    obtain ⟨promotedHeader, promotedHeaderRead, _, _, _, _, _, _⟩ :=
      promoted.header
    obtain ⟨_, promotedRawRead, _, _, _, _⟩ :=
      MemoryState.PrefixExtension.readLiveHeader_facts state other promotedHeader
        promotedHeaderRead
    have differentWord : address ≠ other :=
      related.witnessWellFormed.locationPromotionDisjoint location payload address
        other mapped promotedMapped
    have differentValue : address.value ≠ other.value := by
      intro equal
      exact differentWord (wordEq address other equal)
    have frame := related.allocationFrame_of_writeObjectFields_other descriptor
      promoted.descriptor differentValue rawRead promotedRawRead rfl fieldsInTarget
        written
    exact (promoted.allocationFrame promotedHeaderRead frame)
      |>.rebindConstructor_other differentValue
  exact related.setCell_rebindConstructor_of_frames info
    (resetProtocolFieldKinds fieldKinds count) mapped found rfl finalFrontier
      targetAfter protocolDescriptorRegion protocolDescriptorDisjoint cellFrame
        promotedFrame

/-- Ownership correspondence composes across adjacent released prefixes. -/
theorem OwnershipValuesRel.append
    {witness : RefinementWitness} {leftWords rightWords : List Word32}
    {leftValues rightValues : List Value}
    (left : OwnershipValuesRel witness leftWords leftValues)
    (right : OwnershipValuesRel witness rightWords rightValues) :
    OwnershipValuesRel witness (leftWords ++ rightWords)
      (leftValues ++ rightValues) := by
  induction left with
  | nil => simpa using right
  | cons head tail ih =>
      simpa using OwnershipValuesRel.cons head ih

/-- The concrete prefix snapshot performed by reset returns words in the same
order as FIR's semantic `extract 0 count`, with an ownership relation at every
position. -/
theorem ConstructorObjectRel.readOwnedPrefix
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {semantic : ConstructorObject}
    (related : ConstructorObjectRel state witness address info fieldKinds semantic)
    (count : Nat) (countFits : count ≤ semantic.objectFields.size) :
    ∃ words,
      (List.range count).mapM (fun index =>
        readObjectField state address index) = .ok words ∧
      OwnershipValuesRel witness words
        (semantic.objectFields.extract 0 count).toList := by
  have countFitsInfo : count ≤ info.size := by
    rw [← related.semanticObjectFields]
    exact countFits
  induction count with
  | zero =>
      exact ⟨[], rfl, by simp; exact .nil⟩
  | succ count ih =>
      have countLtSemantic : count < semantic.objectFields.size := by omega
      have countLtInfo : count < info.size := by omega
      obtain ⟨words, wordsRead, wordsRelated⟩ :=
        ih (by omega) (by omega)
      let value := semantic.objectFields[count]'countLtSemantic
      have valueAt : semantic.objectFields[count]? = some value := by
        exact Array.getElem?_eq_getElem countLtSemantic
      obtain ⟨kind, kindAt, admissible⟩ := related.fieldKind countLtInfo
      obtain ⟨word, wordRead, valueRelated⟩ :=
        related.objectFields count kind value kindAt valueAt
      have prefixRead :
          (List.range (count + 1)).mapM (fun index =>
            readObjectField state address index) = .ok (words ++ [word]) := by
        rw [List.range_succ, List.mapM_append, wordsRead]
        simp [wordRead]
        rfl
      have semanticTake : semantic.objectFields.toList.take (count + 1) =
          semantic.objectFields.toList.take count ++ [value] := by
        rw [List.take_succ_eq_append_getElem (by simpa using countLtSemantic)]
        simp [value]
      refine ⟨words ++ [word], prefixRead, ?_⟩
      have wordsRelatedTake : OwnershipValuesRel witness words
          (semantic.objectFields.toList.take count) := by
        simpa [Array.toList_extract, List.extract_eq_take_drop] using wordsRelated
      have appended := wordsRelatedTake.append
        (OwnershipValuesRel.cons
          (OwnershipValueRel.intro kind admissible valueRelated)
          OwnershipValuesRel.nil)
      rw [← semanticTake] at appended
      simpa [Array.toList_extract, List.extract_eq_take_drop] using appended

/-- Ordered ownership correspondence lifts the public checked decrement
through reset's concrete and semantic released-prefix folds. -/
theorem OwnershipValuesRel.foldlM_public_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime finalRuntime : RuntimeState} {words : List Word32}
    {values : List Value}
    (related : OwnershipValuesRel witness words values)
    (heap : LiveHeapRel state witness runtime)
    (semanticOperation : values.foldlM (init := runtime) (fun next value =>
      Fir.LeanIR.Impure.decValueOnce next value true) = .ok finalRuntime) :
    ∃ finalState,
      words.foldlM (init := state) (fun next child =>
        decrementReferenceOnce next child true) = .ok finalState ∧
      LiveHeapRel finalState witness finalRuntime := by
  induction related generalizing state runtime finalRuntime with
  | nil =>
      simp only [List.foldlM_nil] at semanticOperation ⊢
      have runtimeEq := Except.ok.inj semanticOperation
      subst finalRuntime
      exact ⟨state, rfl, heap⟩
  | @cons word value words values head tail ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at semanticOperation ⊢
      cases headSemantic : Fir.LeanIR.Impure.decValueOnce runtime value true with
      | error fault =>
          rw [headSemantic] at semanticOperation
          contradiction
      | ok middleRuntime =>
          rw [headSemantic] at semanticOperation
          have releaseStep := head.releaseStep heap
            (state.heapCursor / headerBytes + 1)
          rcases releaseStep with heapChild | noOp
          · obtain ⟨location, valueEq, mapped⟩ := heapChild
            subst value
            have semanticHead : Fir.LeanIR.Impure.decLocation runtime location =
                .ok middleRuntime := by
              simpa [Fir.LeanIR.Impure.decValueOnce] using headSemantic
            obtain ⟨middleState, concreteHead, middleHeap⟩ :=
              heap.decrementReferenceOnce_refines mapped semanticHead
            obtain ⟨finalState, concreteTail, finalHeap⟩ :=
              ih middleHeap semanticOperation
            exact ⟨finalState, by rw [concreteHead]; exact concreteTail, finalHeap⟩
          · obtain ⟨notHeap, concreteFuelNoOp⟩ := noOp
            have runtimeEq : middleRuntime = runtime := by
              cases value with
              | object reference =>
                  cases reference with
                  | heap location => exact False.elim (notHeap location rfl)
                  | tagged payload =>
                      have equal : runtime = middleRuntime := by
                        have operation :
                            (Except.ok runtime : Except RuntimeFault RuntimeState) =
                              .ok middleRuntime := by
                          simpa [Fir.LeanIR.Impure.decValueOnce] using headSemantic
                        exact Except.ok.inj operation
                      exact equal.symm
              | usize value =>
                  simp [Fir.LeanIR.Impure.decValueOnce] at headSemantic
              | scalar value =>
                  simp [Fir.LeanIR.Impure.decValueOnce] at headSemantic
              | erased =>
                  simp [Fir.LeanIR.Impure.decValueOnce] at headSemantic
              | reuseToken location =>
                  simp [Fir.LeanIR.Impure.decValueOnce] at headSemantic
            subst middleRuntime
            have concreteHead : decrementReferenceOnce state word true =
                .ok state := by
              unfold decrementReferenceOnce
              exact concreteFuelNoOp
            obtain ⟨finalState, concreteTail, finalHeap⟩ :=
              ih heap semanticOperation
            exact ⟨finalState, by rw [concreteHead]; exact concreteTail, finalHeap⟩

/-- One saved ownership slot remains related when reset shadows the target
constructor descriptor. -/
theorem OwnershipValueRel.rebindConstructor
    {witness : RefinementWitness} {word : Word32} {value : Value}
    (related : OwnershipValueRel witness word value)
    (address : Word32) (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    OwnershipValueRel (witness.rebindConstructor address info fieldKinds)
      word value := by
  cases related with
  | intro kind admissible valueRelated =>
      exact .intro kind admissible
        (valueRelated.rebindConstructor address info fieldKinds)

/-- Saved ownership prefixes transport pointwise through the protocol
descriptor rebind without changing their traversal order. -/
theorem OwnershipValuesRel.rebindConstructor
    {witness : RefinementWitness} {words : List Word32} {values : List Value}
    (related : OwnershipValuesRel witness words values)
    (address : Word32) (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    OwnershipValuesRel (witness.rebindConstructor address info fieldKinds)
      words values := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (head.rebindConstructor address info fieldKinds) ih

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

/-- A unique constructor reset enters the explicit reset/reuse protocol. The
cleared target and every released child remain related under the rebound
protocol descriptor, and the returned nonempty token keeps the same semantic
location identity. -/
theorem LiveHeapRel.resetObject_refines_unique
    {state : MemoryState} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {object : ConstructorObject} {count : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1) (constructor : cell.object = .ctor object)
    (countFits : count ≤ object.objectFields.size)
    (semanticOperation :
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .ok (nextRuntime, .reuseToken (some location))) :
    ∃ result info fieldKinds,
      resetObject state count address = .ok (result, address) ∧
      LiveHeapRel result
        (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)) nextRuntime ∧
      ResetReuseProtocolRel state result witness runtime nextRuntime location
        address cell object count ∧
      ValueRel
        (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count))
        .reuseToken (.word32 address) (.reuseToken (some location)) := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  cases targetRelated with
  | @constructor info fieldKinds semantic header _ descriptor objectEq objectRelated
      headerRead headerKind refCount persistent cellLive =>
      rw [constructor] at objectEq
      injection objectEq with semanticEq
      subst semantic
      let replacement : HeapCell :=
        { cell with object := .ctor (resetProtocolObject object count) }
      obtain ⟨middleRuntime, semanticSet, _, _, _, _⟩ :=
        setCell_spec_of_find runtime location cell replacement found
      have semanticFold :
          (object.objectFields.extract 0 count).foldlM
              (fun next value => Fir.LeanIR.Impure.decValueOnce next value true)
              middleRuntime = .ok nextRuntime := by
        unfold Fir.LeanIR.Impure.reset at semanticOperation
        simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
          at semanticOperation
        rw [if_neg (by simp [ordinary, unique])] at semanticOperation
        rw [constructor] at semanticOperation
        simp only at semanticOperation
        rw [if_neg (Nat.not_lt.mpr countFits)] at semanticOperation
        have semanticOperation' : (do
            let next ← setCell runtime location replacement
            let next ← (object.objectFields.extract 0 count).foldlM
              (fun next value => Fir.LeanIR.Impure.decValueOnce next value true)
              next
            return (next, Value.reuseToken (some location))) =
              .ok (nextRuntime, Value.reuseToken (some location)) := by
          simpa only [replacement, resetProtocolObject, live, Bind.bind, Except.bind]
            using semanticOperation
        rw [semanticSet] at semanticOperation'
        simp only [Bind.bind, Except.bind] at semanticOperation'
        cases foldEq : (object.objectFields.extract 0 count).foldlM
            (fun next value => Fir.LeanIR.Impure.decValueOnce next value true)
            middleRuntime with
        | error fault =>
            rw [foldEq] at semanticOperation'
            contradiction
        | ok finalRuntime =>
            rw [foldEq] at semanticOperation'
            have pairEq := Except.ok.inj semanticOperation'
            have runtimeEq : finalRuntime = nextRuntime := congrArg Prod.fst pairEq
            subst finalRuntime
            rfl
      obtain ⟨words, ownedRead, ownershipRelated⟩ :=
        objectRelated.readOwnedPrefix count countFits
      have fieldsBeforeFrontier : objectFieldAddress address.value count ≤
          state.heapCursor := by
        have aligned := align8_ge
          (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
            info.ssize)
        have activeExtent := objectRelated.extent
        have countFitsInfo : count ≤ info.size := by
          rw [← objectRelated.semanticObjectFields]
          exact countFits
        simp [objectFieldAddress, ConstructorLayout.ofInfo, target] at aligned activeExtent ⊢
        omega
      have fieldsInBounds : objectFieldAddress address.value (0 + count) ≤
          state.memory.size := by
        simp only [Nat.zero_add]
        exact Nat.le_trans fieldsBeforeFrontier related.frontier.cursorInBounds
      obtain ⟨fieldMemory, fieldWrite, fieldPost⟩ :=
        writeObjectFields_spec state.memory address.value 0
          (List.replicate count taggedZero) (by simpa using fieldsInBounds)
      obtain ⟨protocolRuntime, protocolSet, protocolHeap⟩ :=
        LiveHeapRel.writeObjectFields_resetPrefix state fieldMemory witness runtime
          location address cell header info fieldKinds object count related mapped found
          descriptor constructor objectRelated headerRead headerKind refCount persistent
          cellLive countFits fieldWrite
      have protocolRuntimeEq : protocolRuntime = middleRuntime := by
        exact Except.ok.inj (protocolSet.symm.trans semanticSet)
      subst protocolRuntime
      have semanticFoldList :
          (object.objectFields.extract 0 count).toList.foldlM
              (init := middleRuntime)
              (fun next value => Fir.LeanIR.Impure.decValueOnce next value true) =
            .ok nextRuntime := by
        simpa only [Array.foldlM_toList] using semanticFold
      have protocolOwnership := ownershipRelated.rebindConstructor address info
        (resetProtocolFieldKinds fieldKinds count)
      obtain ⟨result, concreteFold, finalHeap⟩ :=
        protocolOwnership.foldlM_public_refines protocolHeap semanticFoldList
      obtain ⟨addressHeap, _, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
      obtain ⟨objectHeader, objectHeaderRead, _, _, _, _, objectCount, _, _⟩ :=
        objectRelated.header
      rw [headerRead] at objectHeaderRead
      have objectHeaderEq := Except.ok.inj objectHeaderRead
      subst objectHeader
      have headerOrdinary : header.persistent = false := persistent.trans ordinary
      have headerOne : header.refCount = 1 := by
        apply UInt32.toNat.inj
        simpa [unique] using refCount
      have notPromoted : header.isPromotedTag = false := by
        have different : (ObjectKind.constructor == ObjectKind.natural) = false :=
          by decide
        simp [Header.isPromotedTag, headerKind, different]
      have countFitsInfo : count ≤ info.size := by
        rw [← objectRelated.semanticObjectFields]
        exact countFits
      have headerKindCheck : (header.kind == ObjectKind.constructor) = true := by
        rw [headerKind]
        decide
      have concreteReset : resetObject state count address = .ok (result, address) := by
        unfold resetObject
        rw [addressHeap, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        rw [if_neg (by simp [notPromoted, headerOrdinary, headerOne])]
        rw [if_pos headerKindCheck]
        rw [objectCount, if_neg (Nat.not_lt.mpr countFitsInfo)]
        rw [ownedRead, fieldWrite]
        simp only
        rw [concreteFold]
        rfl
      have protocol : ResetReuseProtocolRel state result witness runtime nextRuntime
          location address cell object count := {
        relatedBefore := related
        mapped
        found
        live
        ordinary
        unique
        constructor
        countFits
        concreteReset
        semanticReset := semanticOperation }
      exact ⟨result, info, fieldKinds, concreteReset, finalHeap, protocol,
        protocol.tokenRelated_rebindConstructor info
          (resetProtocolFieldKinds fieldKinds count)⟩
  | boxed descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | natural descriptor objectEq headerRead headerKind ordinaryHeader marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction

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
